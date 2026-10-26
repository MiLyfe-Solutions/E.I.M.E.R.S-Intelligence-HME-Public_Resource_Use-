import V185TrunkScan23Chunk1215

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7205333 : List Nat := [1, 3, 2, 3, 1, 3, 3, 1, 1, 2, 3]
def baseStart_7205333 : Nat := 118140960795 + 7205333 * 2 ^ 59
def prefixEnd_7205333 : Nat := 4983230072969 + 3 ^ 40 * 7205333 * 2
def baseEnd_7205333 : Nat := 3699799104702362835200783

theorem tailTrace_7205333 : CollatzResearch.WordTrace tailWord_7205333 prefixEnd_7205333 3699799104702362835200783 := by
  unfold tailWord_7205333
  simp only [CollatzResearch.WordTrace]
  refine ⟨262800084405316588750596653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175200056270211059167064435 262800084405316588750596653)
  ·
    refine ⟨98550031651993720781473745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262800084405316588750596653 98550031651993720781473745)
    ·
      refine ⟨73912523738995290586105309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98550031651993720781473745 73912523738995290586105309)
      ·
        refine ⟨27717196402123233969789491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73912523738995290586105309 27717196402123233969789491)
        ·
          refine ⟨41575794603184850954684237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27717196402123233969789491 41575794603184850954684237)
          ·
            refine ⟨15590922976194319108006589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41575794603184850954684237 15590922976194319108006589)
            ·
              refine ⟨5846596116072869665502471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15590922976194319108006589 5846596116072869665502471)
              ·
                refine ⟨8769894174109304498253707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5846596116072869665502471 8769894174109304498253707)
                ·
                  refine ⟨13154841261163956747380561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8769894174109304498253707 13154841261163956747380561)
                  ·
                    refine ⟨9866130945872967560535421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13154841261163956747380561 9866130945872967560535421)
                    ·
                      refine ⟨3699799104702362835200783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9866130945872967560535421 3699799104702362835200783)
                      ·
                        rfl

theorem cell23_7205333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_7205333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205333 prefixEnd_7205333 := by exact prefixLift 7205333
  have htrace : WordTrace (prefixWord ++ tailWord_7205333) baseStart_7205333 baseEnd_7205333 := by
    simpa [prefixWord, tailWord_7205333, baseEnd_7205333] using wordTrace_append hprefix tailTrace_7205333
  have hstable : (prefixWord ++ tailWord_7205333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205333).length < 2 ^ (prefixWord ++ tailWord_7205333).sum := by decide
  have hdescent : baseEnd_7205333 < baseStart_7205333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205386 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 1, 4, 2]
def baseStart_7205386 : Nat := 118140960795 + 7205386 * 2 ^ 59
def prefixEnd_7205386 : Nat := 4983230072969 + 3 ^ 40 * 7205386 * 2
def baseEnd_7205386 : Nat := 3699826319177051127838039

theorem tailTrace_7205386 : CollatzResearch.WordTrace tailWord_7205386 prefixEnd_7205386 3699826319177051127838039 := by
  unfold tailWord_7205386
  simp only [CollatzResearch.WordTrace]
  refine ⟨65700504368531144700569003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175201344982749719201517341 65700504368531144700569003)
  ·
    refine ⟨98550756552796717050853505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65700504368531144700569003 98550756552796717050853505)
    ·
      refine ⟨73913067414597537788140129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98550756552796717050853505 73913067414597537788140129)
      ·
        refine ⟨55434800560948153341105097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73913067414597537788140129 55434800560948153341105097)
        ·
          refine ⟨41576100420711115005828823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55434800560948153341105097 41576100420711115005828823)
          ·
            refine ⟨62364150631066672508743235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41576100420711115005828823 62364150631066672508743235)
            ·
              refine ⟨93546225946600008763114853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62364150631066672508743235 93546225946600008763114853)
              ·
                refine ⟨17539917364987501643084035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93546225946600008763114853 17539917364987501643084035)
                ·
                  refine ⟨26309876047481252464626053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17539917364987501643084035 26309876047481252464626053)
                  ·
                    refine ⟨4933101758902734837117385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26309876047481252464626053 4933101758902734837117385)
                    ·
                      refine ⟨3699826319177051127838039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4933101758902734837117385 3699826319177051127838039)
                      ·
                        rfl

theorem cell23_7205386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_7205386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205386 prefixEnd_7205386 := by exact prefixLift 7205386
  have htrace : WordTrace (prefixWord ++ tailWord_7205386) baseStart_7205386 baseEnd_7205386 := by
    simpa [prefixWord, tailWord_7205386, baseEnd_7205386] using wordTrace_append hprefix tailTrace_7205386
  have hstable : (prefixWord ++ tailWord_7205386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205386).length < 2 ^ (prefixWord ++ tailWord_7205386).sum := by decide
  have hdescent : baseEnd_7205386 < baseStart_7205386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205390 : List Nat := [4, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2]
def baseStart_7205390 : Nat := 118140960795 + 7205390 * 2 ^ 59
def prefixEnd_7205390 : Nat := 4983230072969 + 3 ^ 40 * 7205390 * 2
def baseEnd_7205390 : Nat := 3699828373099669112188021

theorem tailTrace_7205390 : CollatzResearch.WordTrace tailWord_7205390 prefixEnd_7205390 3699828373099669112188021 := by
  unfold tailWord_7205390
  simp only [CollatzResearch.WordTrace]
  refine ⟨32850270420763760935677703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175201442244073391656947749 32850270420763760935677703)
  ·
    refine ⟨49275405631145641403516555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32850270420763760935677703 49275405631145641403516555)
    ·
      refine ⟨73913108446718462105274833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49275405631145641403516555 73913108446718462105274833)
      ·
        refine ⟨55434831335038846578956125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73913108446718462105274833 55434831335038846578956125)
        ·
          refine ⟨20788061750639567467108547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55434831335038846578956125 20788061750639567467108547)
          ·
            refine ⟨31182092625959351200662821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20788061750639567467108547 31182092625959351200662821)
            ·
              refine ⟨5846642367367378350124279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31182092625959351200662821 5846642367367378350124279)
              ·
                refine ⟨8769963551051067525186419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5846642367367378350124279 8769963551051067525186419)
                ·
                  refine ⟨13154945326576601287779629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8769963551051067525186419 13154945326576601287779629)
                  ·
                    refine ⟨4933104497466225482917361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13154945326576601287779629 4933104497466225482917361)
                    ·
                      refine ⟨3699828373099669112188021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4933104497466225482917361 3699828373099669112188021)
                      ·
                        rfl

theorem cell23_7205390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_7205390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205390 prefixEnd_7205390 := by exact prefixLift 7205390
  have htrace : WordTrace (prefixWord ++ tailWord_7205390) baseStart_7205390 baseEnd_7205390 := by
    simpa [prefixWord, tailWord_7205390, baseEnd_7205390] using wordTrace_append hprefix tailTrace_7205390
  have hstable : (prefixWord ++ tailWord_7205390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205390).length < 2 ^ (prefixWord ++ tailWord_7205390).sum := by decide
  have hdescent : baseEnd_7205390 < baseStart_7205390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205396 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_7205396 : Nat := 118140960795 + 7205396 * 2 ^ 59
def prefixEnd_7205396 : Nat := 4983230072969 + 3 ^ 40 * 7205396 * 2
def baseEnd_7205396 : Nat := 1233277151327865362904331

theorem tailTrace_7205396 : CollatzResearch.WordTrace tailWord_7205396 prefixEnd_7205396 1233277151327865362904331 := by
  unfold tailWord_7205396
  simp only [CollatzResearch.WordTrace]
  refine ⟨131401191102044175255070021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175201588136058900340093361 131401191102044175255070021)
  ·
    refine ⟨24637723331633282860325629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131401191102044175255070021 24637723331633282860325629)
    ·
      refine ⟨9239146249362481072622111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24637723331633282860325629 9239146249362481072622111)
      ·
        refine ⟨13858719374043721608933167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9239146249362481072622111 13858719374043721608933167)
        ·
          refine ⟨20788079061065582413399751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13858719374043721608933167 20788079061065582413399751)
          ·
            refine ⟨31182118591598373620099627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20788079061065582413399751 31182118591598373620099627)
            ·
              refine ⟨46773177887397560430149441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31182118591598373620099627 46773177887397560430149441)
              ·
                refine ⟨35079883415548170322612081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46773177887397560430149441 35079883415548170322612081)
                ·
                  refine ⟨26309912561661127741959061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35079883415548170322612081 26309912561661127741959061)
                  ·
                    refine ⟨1233277151327865362904331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26309912561661127741959061 1233277151327865362904331)
                    ·
                      rfl

theorem cell23_7205396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_7205396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205396 prefixEnd_7205396 := by exact prefixLift 7205396
  have htrace : WordTrace (prefixWord ++ tailWord_7205396) baseStart_7205396 baseEnd_7205396 := by
    simpa [prefixWord, tailWord_7205396, baseEnd_7205396] using wordTrace_append hprefix tailTrace_7205396
  have hstable : (prefixWord ++ tailWord_7205396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205396).length < 2 ^ (prefixWord ++ tailWord_7205396).sum := by decide
  have hdescent : baseEnd_7205396 < baseStart_7205396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205409 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 7]
def baseStart_7205409 : Nat := 118140960795 + 7205409 * 2 ^ 59
def prefixEnd_7205409 : Nat := 4983230072969 + 3 ^ 40 * 7205409 * 2
def baseEnd_7205409 : Nat := 411093125470233837538937

theorem tailTrace_7205409 : CollatzResearch.WordTrace tailWord_7205409 prefixEnd_7205409 411093125470233837538937 := by
  unfold tailWord_7205409
  simp only [CollatzResearch.WordTrace]
  refine ⟨262802856353041253730363281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175201904235360835820242187 262802856353041253730363281)
  ·
    refine ⟨197102142264780940297772461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262802856353041253730363281 197102142264780940297772461)
    ·
      refine ⟨73913303349292852611664673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197102142264780940297772461 73913303349292852611664673)
      ·
        refine ⟨55434977511969639458748505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73913303349292852611664673 55434977511969639458748505)
        ·
          refine ⟨41576233133977229594061379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55434977511969639458748505 41576233133977229594061379)
          ·
            refine ⟨62364349700965844391092069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41576233133977229594061379 62364349700965844391092069)
            ·
              refine ⟨11693315568931095823329763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62364349700965844391092069 11693315568931095823329763)
              ·
                refine ⟨17539973353396643734994645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11693315568931095823329763 17539973353396643734994645)
                ·
                  refine ⟨411093125470233837538937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17539973353396643734994645 411093125470233837538937)
                  ·
                    rfl

theorem cell23_7205409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 7].length) (baseStart_7205409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205409 prefixEnd_7205409 := by exact prefixLift 7205409
  have htrace : WordTrace (prefixWord ++ tailWord_7205409) baseStart_7205409 baseEnd_7205409 := by
    simpa [prefixWord, tailWord_7205409, baseEnd_7205409] using wordTrace_append hprefix tailTrace_7205409
  have hstable : (prefixWord ++ tailWord_7205409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205409).length < 2 ^ (prefixWord ++ tailWord_7205409).sum := by decide
  have hdescent : baseEnd_7205409 < baseStart_7205409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205416 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_7205416 : Nat := 118140960795 + 7205416 * 2 ^ 59
def prefixEnd_7205416 : Nat := 4983230072969 + 3 ^ 40 * 7205416 * 2
def baseEnd_7205416 : Nat := 3699841723596686010462901

theorem tailTrace_7205416 : CollatzResearch.WordTrace tailWord_7205416 prefixEnd_7205416 3699841723596686010462901 := by
  unfold tailWord_7205416
  simp only [CollatzResearch.WordTrace]
  refine ⟨131401555832007946962934051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175202074442677262617245401 131401555832007946962934051)
  ·
    refine ⟨197102333748011920444401077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131401555832007946962934051 197102333748011920444401077)
    ·
      refine ⟨18478343788876117541662601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197102333748011920444401077 18478343788876117541662601)
      ·
        refine ⟨13858757841657088156246951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18478343788876117541662601 13858757841657088156246951)
        ·
          refine ⟨20788136762485632234370427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13858757841657088156246951 20788136762485632234370427)
          ·
            refine ⟨31182205143728448351555641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20788136762485632234370427 31182205143728448351555641)
            ·
              refine ⟨23386653857796336263666731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31182205143728448351555641 23386653857796336263666731)
              ·
                refine ⟨35079980786694504395500097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23386653857796336263666731 35079980786694504395500097)
                ·
                  refine ⟨26309985590020878296625073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35079980786694504395500097 26309985590020878296625073)
                  ·
                    refine ⟨19732489192515658722468805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26309985590020878296625073 19732489192515658722468805)
                    ·
                      refine ⟨3699841723596686010462901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19732489192515658722468805 3699841723596686010462901)
                      ·
                        rfl

theorem cell23_7205416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_7205416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205416 prefixEnd_7205416 := by exact prefixLift 7205416
  have htrace : WordTrace (prefixWord ++ tailWord_7205416) baseStart_7205416 baseEnd_7205416 := by
    simpa [prefixWord, tailWord_7205416, baseEnd_7205416] using wordTrace_append hprefix tailTrace_7205416
  have hstable : (prefixWord ++ tailWord_7205416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205416).length < 2 ^ (prefixWord ++ tailWord_7205416).sum := by decide
  have hdescent : baseEnd_7205416 < baseStart_7205416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205439 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 2, 5]
def baseStart_7205439 : Nat := 118140960795 + 7205439 * 2 ^ 59
def prefixEnd_7205439 : Nat := 4983230072969 + 3 ^ 40 * 7205439 * 2
def baseEnd_7205439 : Nat := 1233284511217246473491765

theorem tailTrace_7205439 : CollatzResearch.WordTrace tailWord_7205439 prefixEnd_7205439 1233284511217246473491765 := by
  unfold tailWord_7205439
  simp only [CollatzResearch.WordTrace]
  refine ⟨262803950542932568853955371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175202633695288379235970247 262803950542932568853955371)
  ·
    refine ⟨394205925814398853280933057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262803950542932568853955371 394205925814398853280933057)
    ·
      refine ⟨295654444360799139960699793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394205925814398853280933057 295654444360799139960699793)
      ·
        refine ⟨221740833270599354970524845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295654444360799139960699793 221740833270599354970524845)
        ·
          refine ⟨83152812476474758113946817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221740833270599354970524845 83152812476474758113946817)
          ·
            refine ⟨62364609357356068585460113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83152812476474758113946817 62364609357356068585460113)
            ·
              refine ⟨46773457018017051439095085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62364609357356068585460113 46773457018017051439095085)
              ·
                refine ⟨17540046381756394289660657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46773457018017051439095085 17540046381756394289660657)
                ·
                  refine ⟨13155034786317295717245493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17540046381756394289660657 13155034786317295717245493)
                  ·
                    refine ⟨1233284511217246473491765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13155034786317295717245493 1233284511217246473491765)
                    ·
                      rfl

theorem cell23_7205439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 5].length) (baseStart_7205439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205439 prefixEnd_7205439 := by exact prefixLift 7205439
  have htrace : WordTrace (prefixWord ++ tailWord_7205439) baseStart_7205439 baseEnd_7205439 := by
    simpa [prefixWord, tailWord_7205439, baseEnd_7205439] using wordTrace_append hprefix tailTrace_7205439
  have hstable : (prefixWord ++ tailWord_7205439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205439).length < 2 ^ (prefixWord ++ tailWord_7205439).sum := by decide
  have hdescent : baseEnd_7205439 < baseStart_7205439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205476 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 1, 6, 2]
def baseStart_7205476 : Nat := 118140960795 + 7205476 * 2 ^ 59
def prefixEnd_7205476 : Nat := 4983230072969 + 3 ^ 40 * 7205476 * 2
def baseEnd_7205476 : Nat := 3699872532435955775712625

theorem tailTrace_7205476 : CollatzResearch.WordTrace tailWord_7205476 prefixEnd_7205476 3699872532435955775712625 := by
  unfold tailWord_7205476
  simp only [CollatzResearch.WordTrace]
  refine ⟨131402650021899262086526141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175203533362532349448701521 131402650021899262086526141)
  ·
    refine ⟨49275993758212223282447303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131402650021899262086526141 49275993758212223282447303)
    ·
      refine ⟨73913990637318334923670955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49275993758212223282447303 73913990637318334923670955)
      ·
        refine ⟨110870985955977502385506433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73913990637318334923670955 110870985955977502385506433)
        ·
          refine ⟨83153239466983126789129825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110870985955977502385506433 83153239466983126789129825)
          ·
            refine ⟨62364929600237345091847369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83153239466983126789129825 62364929600237345091847369)
            ·
              refine ⟨46773697200178008818885527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62364929600237345091847369 46773697200178008818885527)
              ·
                refine ⟨70160545800267013228328291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46773697200178008818885527 70160545800267013228328291)
                ·
                  refine ⟨105240818700400519842492437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70160545800267013228328291 105240818700400519842492437)
                  ·
                    refine ⟨4933163376581274367616833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105240818700400519842492437 4933163376581274367616833)
                    ·
                      refine ⟨3699872532435955775712625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4933163376581274367616833 3699872532435955775712625)
                      ·
                        rfl

theorem cell23_7205476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_7205476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205476 prefixEnd_7205476 := by exact prefixLift 7205476
  have htrace : WordTrace (prefixWord ++ tailWord_7205476) baseStart_7205476 baseEnd_7205476 := by
    simpa [prefixWord, tailWord_7205476, baseEnd_7205476] using wordTrace_append hprefix tailTrace_7205476
  have hstable : (prefixWord ++ tailWord_7205476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205476).length < 2 ^ (prefixWord ++ tailWord_7205476).sum := by decide
  have hdescent : baseEnd_7205476 < baseStart_7205476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205529 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 5, 5]
def baseStart_7205529 : Nat := 118140960795 + 7205529 * 2 ^ 59
def prefixEnd_7205529 : Nat := 4983230072969 + 3 ^ 40 * 7205529 * 2
def baseEnd_7205529 : Nat := 1233299915636881356116627

theorem tailTrace_7205529 : CollatzResearch.WordTrace tailWord_7205529 prefixEnd_7205529 1233299915636881356116627 := by
  unfold tailWord_7205529
  simp only [CollatzResearch.WordTrace]
  refine ⟨262807233112606514224731641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175204822075071009483154427 262807233112606514224731641)
  ·
    refine ⟨197105424834454885668548731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262807233112606514224731641 197105424834454885668548731)
    ·
      refine ⟨295658137251682328502823097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197105424834454885668548731 295658137251682328502823097)
      ·
        refine ⟨221743602938761746377117323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295658137251682328502823097 221743602938761746377117323)
        ·
          refine ⟨332615404408142619565675985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221743602938761746377117323 332615404408142619565675985)
          ·
            refine ⟨249461553306106964674256989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332615404408142619565675985 249461553306106964674256989)
            ·
              refine ⟨93548082489790111752846371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249461553306106964674256989 93548082489790111752846371)
              ·
                refine ⟨140322123734685167629269557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93548082489790111752846371 140322123734685167629269557)
                ·
                  refine ⟨13155199100126734465244021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140322123734685167629269557 13155199100126734465244021)
                  ·
                    refine ⟨1233299915636881356116627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13155199100126734465244021 1233299915636881356116627)
                    ·
                      rfl

theorem cell23_7205529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 5].length) (baseStart_7205529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205529 prefixEnd_7205529 := by exact prefixLift 7205529
  have htrace : WordTrace (prefixWord ++ tailWord_7205529) baseStart_7205529 baseEnd_7205529 := by
    simpa [prefixWord, tailWord_7205529, baseEnd_7205529] using wordTrace_append hprefix tailTrace_7205529
  have hstable : (prefixWord ++ tailWord_7205529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205529).length < 2 ^ (prefixWord ++ tailWord_7205529).sum := by decide
  have hdescent : baseEnd_7205529 < baseStart_7205529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205579 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 4]
def baseStart_7205579 : Nat := 118140960795 + 7205579 * 2 ^ 59
def prefixEnd_7205579 : Nat := 4983230072969 + 3 ^ 40 * 7205579 * 2
def baseEnd_7205579 : Nat := 3699925420943368872724651

theorem tailTrace_7205579 : CollatzResearch.WordTrace tailWord_7205579 prefixEnd_7205579 3699925420943368872724651 := by
  unfold tailWord_7205579
  simp only [CollatzResearch.WordTrace]
  refine ⟨262809056762425372764051791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175206037841616915176034527 262809056762425372764051791)
  ·
    refine ⟨394213585143638059146077687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262809056762425372764051791 394213585143638059146077687)
    ·
      refine ⟨591320377715457088719116531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394213585143638059146077687 591320377715457088719116531)
      ·
        refine ⟨886980566573185633078674797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591320377715457088719116531 886980566573185633078674797)
        ·
          refine ⟨332617712464944612404503049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 886980566573185633078674797 332617712464944612404503049)
          ·
            refine ⟨249463284348708459303377287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332617712464944612404503049 249463284348708459303377287)
            ·
              refine ⟨374194926523062688955065931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249463284348708459303377287 374194926523062688955065931)
              ·
                refine ⟨561292389784594033432598897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374194926523062688955065931 561292389784594033432598897)
                ·
                  refine ⟨420969292338445525074449173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 561292389784594033432598897 420969292338445525074449173)
                  ·
                    refine ⟨19732935578364633987864805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 420969292338445525074449173 19732935578364633987864805)
                    ·
                      refine ⟨3699925420943368872724651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19732935578364633987864805 3699925420943368872724651)
                      ·
                        rfl

theorem cell23_7205579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 4].length) (baseStart_7205579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205579 prefixEnd_7205579 := by exact prefixLift 7205579
  have htrace : WordTrace (prefixWord ++ tailWord_7205579) baseStart_7205579 baseEnd_7205579 := by
    simpa [prefixWord, tailWord_7205579, baseEnd_7205579] using wordTrace_append hprefix tailTrace_7205579
  have hstable : (prefixWord ++ tailWord_7205579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205579).length < 2 ^ (prefixWord ++ tailWord_7205579).sum := by decide
  have hdescent : baseEnd_7205579 < baseStart_7205579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205616 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 3]
def baseStart_7205616 : Nat := 118140960795 + 7205616 * 2 ^ 59
def prefixEnd_7205616 : Nat := 4983230072969 + 3 ^ 40 * 7205616 * 2
def baseEnd_7205616 : Nat := 3699944419727585227961981

theorem tailTrace_7205616 : CollatzResearch.WordTrace tailWord_7205616 prefixEnd_7205616 3699944419727585227961981 := by
  unfold tailWord_7205616
  simp only [CollatzResearch.WordTrace]
  refine ⟨131405203131645664041574351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175206937508860885388765801 131405203131645664041574351)
  ·
    refine ⟨197107804697468496062361527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131405203131645664041574351 197107804697468496062361527)
    ·
      refine ⟨295661707046202744093542291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197107804697468496062361527 295661707046202744093542291)
      ·
        refine ⟨443492560569304116140313437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295661707046202744093542291 443492560569304116140313437)
        ·
          refine ⟨166309710213489043552617539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443492560569304116140313437 166309710213489043552617539)
          ·
            refine ⟨249464565320233565328926309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166309710213489043552617539 249464565320233565328926309)
            ·
              refine ⟨46774605997543793499173683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249464565320233565328926309 46774605997543793499173683)
              ·
                refine ⟨70161908996315690248760525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46774605997543793499173683 70161908996315690248760525)
                ·
                  refine ⟨26310715873618383843285197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70161908996315690248760525 26310715873618383843285197)
                  ·
                    refine ⟨9866518452606893941231949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26310715873618383843285197 9866518452606893941231949)
                    ·
                      refine ⟨3699944419727585227961981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9866518452606893941231949 3699944419727585227961981)
                      ·
                        rfl

theorem cell23_7205616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 3].length) (baseStart_7205616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205616 prefixEnd_7205616 := by exact prefixLift 7205616
  have htrace : WordTrace (prefixWord ++ tailWord_7205616) baseStart_7205616 baseEnd_7205616 := by
    simpa [prefixWord, tailWord_7205616, baseEnd_7205616] using wordTrace_append hprefix tailTrace_7205616
  have hstable : (prefixWord ++ tailWord_7205616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205616).length < 2 ^ (prefixWord ++ tailWord_7205616).sum := by decide
  have hdescent : baseEnd_7205616 < baseStart_7205616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205619 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 1, 9]
def baseStart_7205619 : Nat := 118140960795 + 7205619 * 2 ^ 59
def prefixEnd_7205619 : Nat := 4983230072969 + 3 ^ 40 * 7205619 * 2
def baseEnd_7205619 : Nat := 1233315320056516238741489

theorem tailTrace_7205619 : CollatzResearch.WordTrace tailWord_7205619 prefixEnd_7205619 1233315320056516238741489 := by
  unfold tailWord_7205619
  simp only [CollatzResearch.WordTrace]
  refine ⟨262810515682280459595507911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175207010454853639730338607 262810515682280459595507911)
  ·
    refine ⟨394215773523420689393261867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262810515682280459595507911 394215773523420689393261867)
    ·
      refine ⟨591323660285131034089892801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394215773523420689393261867 591323660285131034089892801)
      ·
        refine ⟨443492745213848275567419601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591323660285131034089892801 443492745213848275567419601)
        ·
          refine ⟨332619558910386206675564701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443492745213848275567419601 332619558910386206675564701)
          ·
            refine ⟨124732334591394827503336763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332619558910386206675564701 124732334591394827503336763)
            ·
              refine ⟨187098501887092241255005145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124732334591394827503336763 187098501887092241255005145)
              ·
                refine ⟨140323876415319180941253859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187098501887092241255005145 140323876415319180941253859)
                ·
                  refine ⟨210485814622978771411880789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140323876415319180941253859 210485814622978771411880789)
                  ·
                    refine ⟨1233315320056516238741489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 210485814622978771411880789 1233315320056516238741489)
                    ·
                      rfl

theorem cell23_7205619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 9].length) (baseStart_7205619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205619 prefixEnd_7205619 := by exact prefixLift 7205619
  have htrace : WordTrace (prefixWord ++ tailWord_7205619) baseStart_7205619 baseEnd_7205619 := by
    simpa [prefixWord, tailWord_7205619, baseEnd_7205619] using wordTrace_append hprefix tailTrace_7205619
  have hstable : (prefixWord ++ tailWord_7205619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205619).length < 2 ^ (prefixWord ++ tailWord_7205619).sum := by decide
  have hdescent : baseEnd_7205619 < baseStart_7205619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205634 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_7205634 : Nat := 118140960795 + 7205634 * 2 ^ 59
def prefixEnd_7205634 : Nat := 4983230072969 + 3 ^ 40 * 7205634 * 2
def baseEnd_7205634 : Nat := 3699953662379366157536899

theorem tailTrace_7205634 : CollatzResearch.WordTrace tailWord_7205634 prefixEnd_7205634 3699953662379366157536899 := by
  unfold tailWord_7205634
  simp only [CollatzResearch.WordTrace]
  refine ⟨65702765694306529289325989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175207375184817411438202637 65702765694306529289325989)
  ·
    refine ⟨12319268567682474241748623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65702765694306529289325989 12319268567682474241748623)
    ·
      refine ⟨18478902851523711362622935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12319268567682474241748623 18478902851523711362622935)
      ·
        refine ⟨27718354277285567043934403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18478902851523711362622935 27718354277285567043934403)
        ·
          refine ⟨41577531415928350565901605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27718354277285567043934403 41577531415928350565901605)
          ·
            refine ⟨7795787140486565731106551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41577531415928350565901605 7795787140486565731106551)
            ·
              refine ⟨11693680710729848596659827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7795787140486565731106551 11693680710729848596659827)
              ·
                refine ⟨17540521066094772894989741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11693680710729848596659827 17540521066094772894989741)
                ·
                  refine ⟨6577695399785539835621153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17540521066094772894989741 6577695399785539835621153)
                  ·
                    refine ⟨4933271549839154876715865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6577695399785539835621153 4933271549839154876715865)
                    ·
                      refine ⟨3699953662379366157536899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4933271549839154876715865 3699953662379366157536899)
                      ·
                        rfl

theorem cell23_7205634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_7205634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205634 prefixEnd_7205634 := by exact prefixLift 7205634
  have htrace : WordTrace (prefixWord ++ tailWord_7205634) baseStart_7205634 baseEnd_7205634 := by
    simpa [prefixWord, tailWord_7205634, baseEnd_7205634] using wordTrace_append hprefix tailTrace_7205634
  have hstable : (prefixWord ++ tailWord_7205634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205634).length < 2 ^ (prefixWord ++ tailWord_7205634).sum := by decide
  have hdescent : baseEnd_7205634 < baseStart_7205634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205636 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_7205636 : Nat := 118140960795 + 7205636 * 2 ^ 59
def prefixEnd_7205636 : Nat := 4983230072969 + 3 ^ 40 * 7205636 * 2
def baseEnd_7205636 : Nat := 1233318229780225049903963

theorem tailTrace_7205636 : CollatzResearch.WordTrace tailWord_7205636 prefixEnd_7205636 1233318229780225049903963 := by
  unfold tailWord_7205636
  simp only [CollatzResearch.WordTrace]
  refine ⟨131405567861609435749438381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175207423815479247665917841 131405567861609435749438381)
  ·
    refine ⟨49277087948103538406039393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131405567861609435749438381 49277087948103538406039393)
    ·
      refine ⟨36957815961077653804529545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49277087948103538406039393 36957815961077653804529545)
      ·
        refine ⟨27718361970808240353397159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36957815961077653804529545 27718361970808240353397159)
        ·
          refine ⟨41577542956212360530095739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27718361970808240353397159 41577542956212360530095739)
          ·
            refine ⟨62366314434318540795143609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41577542956212360530095739 62366314434318540795143609)
            ·
              refine ⟨46774735825738905596357707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62366314434318540795143609 46774735825738905596357707)
              ·
                refine ⟨70162103738608358394536561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46774735825738905596357707 70162103738608358394536561)
                ·
                  refine ⟨52621577803956268795902421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70162103738608358394536561 52621577803956268795902421)
                  ·
                    refine ⟨1233318229780225049903963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52621577803956268795902421 1233318229780225049903963)
                    ·
                      rfl

theorem cell23_7205636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_7205636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205636 prefixEnd_7205636 := by exact prefixLift 7205636
  have htrace : WordTrace (prefixWord ++ tailWord_7205636) baseStart_7205636 baseEnd_7205636 := by
    simpa [prefixWord, tailWord_7205636, baseEnd_7205636] using wordTrace_append hprefix tailTrace_7205636
  have hstable : (prefixWord ++ tailWord_7205636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205636).length < 2 ^ (prefixWord ++ tailWord_7205636).sum := by decide
  have hdescent : baseEnd_7205636 < baseStart_7205636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205643 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 3, 3, 2]
def baseStart_7205643 : Nat := 118140960795 + 7205643 * 2 ^ 59
def prefixEnd_7205643 : Nat := 4983230072969 + 3 ^ 40 * 7205643 * 2
def baseEnd_7205643 : Nat := 3699958283705256622324357

theorem tailTrace_7205643 : CollatzResearch.WordTrace tailWord_7205643 prefixEnd_7205643 3699958283705256622324357 := by
  unfold tailWord_7205643
  simp only [CollatzResearch.WordTrace]
  refine ⟨262811391034193511694381583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175207594022795674462921055 262811391034193511694381583)
  ·
    refine ⟨394217086551290267541572375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262811391034193511694381583 394217086551290267541572375)
    ·
      refine ⟨591325629826935401312358563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394217086551290267541572375 591325629826935401312358563)
      ·
        refine ⟨886988444740403101968537845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591325629826935401312358563 886988444740403101968537845)
        ·
          refine ⟨83155166694412790809550423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 886988444740403101968537845 83155166694412790809550423)
          ·
            refine ⟨124732750041619186214325635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83155166694412790809550423 124732750041619186214325635)
            ·
              refine ⟨187099125062428779321488453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124732750041619186214325635 187099125062428779321488453)
              ·
                refine ⟨35081085949205396122779085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187099125062428779321488453 35081085949205396122779085)
                ·
                  refine ⟨13155407230952023546042157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35081085949205396122779085 13155407230952023546042157)
                  ·
                    refine ⟨4933277711607008829765809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13155407230952023546042157 4933277711607008829765809)
                    ·
                      refine ⟨3699958283705256622324357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4933277711607008829765809 3699958283705256622324357)
                      ·
                        rfl

theorem cell23_7205643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 3, 2].length) (baseStart_7205643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205643 prefixEnd_7205643 := by exact prefixLift 7205643
  have htrace : WordTrace (prefixWord ++ tailWord_7205643) baseStart_7205643 baseEnd_7205643 := by
    simpa [prefixWord, tailWord_7205643, baseEnd_7205643] using wordTrace_append hprefix tailTrace_7205643
  have hstable : (prefixWord ++ tailWord_7205643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205643).length < 2 ^ (prefixWord ++ tailWord_7205643).sum := by decide
  have hdescent : baseEnd_7205643 < baseStart_7205643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205660 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_7205660 : Nat := 118140960795 + 7205660 * 2 ^ 59
def prefixEnd_7205660 : Nat := 4983230072969 + 3 ^ 40 * 7205660 * 2
def baseEnd_7205660 : Nat := 3699967012876383055811779

theorem tailTrace_7205660 : CollatzResearch.WordTrace tailWord_7205660 prefixEnd_7205660 3699967012876383055811779 := by
  unfold tailWord_7205660
  simp only [CollatzResearch.WordTrace]
  refine ⟨131406005537565961798875217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175208007383421282398500289 131406005537565961798875217)
  ·
    refine ⟨98554504153174471349156413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131406005537565961798875217 98554504153174471349156413)
    ·
      refine ⟨36957939057440426755933655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98554504153174471349156413 36957939057440426755933655)
      ·
        refine ⟨55436908586160640133900483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36957939057440426755933655 55436908586160640133900483)
        ·
          refine ⟨83155362879240960200850725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55436908586160640133900483 83155362879240960200850725)
          ·
            refine ⟨15591630539857680037659511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83155362879240960200850725 15591630539857680037659511)
            ·
              refine ⟨23387445809786520056489267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15591630539857680037659511 23387445809786520056489267)
              ·
                refine ⟨35081168714679780084733901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23387445809786520056489267 35081168714679780084733901)
                ·
                  refine ⟨13155438268004917531775213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35081168714679780084733901 13155438268004917531775213)
                  ·
                    refine ⟨4933289350501844074415705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13155438268004917531775213 4933289350501844074415705)
                    ·
                      refine ⟨3699967012876383055811779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4933289350501844074415705 3699967012876383055811779)
                      ·
                        rfl

theorem cell23_7205660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_7205660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205660 prefixEnd_7205660 := by exact prefixLift 7205660
  have htrace : WordTrace (prefixWord ++ tailWord_7205660) baseStart_7205660 baseEnd_7205660 := by
    simpa [prefixWord, tailWord_7205660, baseEnd_7205660] using wordTrace_append hprefix tailTrace_7205660
  have hstable : (prefixWord ++ tailWord_7205660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205660).length < 2 ^ (prefixWord ++ tailWord_7205660).sum := by decide
  have hdescent : baseEnd_7205660 < baseStart_7205660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205673 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 1, 4, 2]
def baseStart_7205673 : Nat := 118140960795 + 7205673 * 2 ^ 59
def prefixEnd_7205673 : Nat := 4983230072969 + 3 ^ 40 * 7205673 * 2
def baseEnd_7205673 : Nat := 3699973688124891504949219

theorem tailTrace_7205673 : CollatzResearch.WordTrace tailWord_7205673 prefixEnd_7205673 3699973688124891504949219 := by
  unfold tailWord_7205673
  simp only [CollatzResearch.WordTrace]
  refine ⟨262812485224084826817973673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175208323482723217878649115 262812485224084826817973673)
  ·
    refine ⟨197109363918063620113480255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262812485224084826817973673 197109363918063620113480255)
    ·
      refine ⟨295664045877095430170220383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197109363918063620113480255 295664045877095430170220383)
      ·
        refine ⟨443496068815643145255330575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295664045877095430170220383 443496068815643145255330575)
        ·
          refine ⟨665244103223464717882995863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443496068815643145255330575 665244103223464717882995863)
          ·
            refine ⟨997866154835197076824493795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665244103223464717882995863 997866154835197076824493795)
            ·
              refine ⟨1496799232252795615236740693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997866154835197076824493795 1496799232252795615236740693)
              ·
                refine ⟨17540616002962448616055555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1496799232252795615236740693 17540616002962448616055555)
                ·
                  refine ⟨26310924004443672924083333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17540616002962448616055555 26310924004443672924083333)
                  ·
                    refine ⟨4933298250833188673265625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26310924004443672924083333 4933298250833188673265625)
                    ·
                      refine ⟨3699973688124891504949219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4933298250833188673265625 3699973688124891504949219)
                      ·
                        rfl

theorem cell23_7205673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 4, 2].length) (baseStart_7205673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205673 prefixEnd_7205673 := by exact prefixLift 7205673
  have htrace : WordTrace (prefixWord ++ tailWord_7205673) baseStart_7205673 baseEnd_7205673 := by
    simpa [prefixWord, tailWord_7205673, baseEnd_7205673] using wordTrace_append hprefix tailTrace_7205673
  have hstable : (prefixWord ++ tailWord_7205673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205673).length < 2 ^ (prefixWord ++ tailWord_7205673).sum := by decide
  have hdescent : baseEnd_7205673 < baseStart_7205673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205676 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_7205676 : Nat := 118140960795 + 7205676 * 2 ^ 59
def prefixEnd_7205676 : Nat := 4983230072969 + 3 ^ 40 * 7205676 * 2
def baseEnd_7205676 : Nat := 3699975228566854993211705

theorem tailTrace_7205676 : CollatzResearch.WordTrace tailWord_7205676 prefixEnd_7205676 3699975228566854993211705 := by
  unfold tailWord_7205676
  simp only [CollatzResearch.WordTrace]
  refine ⟨131406297321536979165166441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175208396428715972220221921 131406297321536979165166441)
  ·
    refine ⟨98554722991152734373874831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131406297321536979165166441 98554722991152734373874831)
    ·
      refine ⟨147832084486729101560812247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98554722991152734373874831 147832084486729101560812247)
      ·
        refine ⟨221748126730093652341218371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147832084486729101560812247 221748126730093652341218371)
        ·
          refine ⟨332622190095140478511827557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221748126730093652341218371 332622190095140478511827557)
          ·
            refine ⟨62366660642838839720967667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 332622190095140478511827557 62366660642838839720967667)
            ·
              refine ⟨93549990964258259581451501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62366660642838839720967667 93549990964258259581451501)
              ·
                refine ⟨35081246611596847343044313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93549990964258259581451501 35081246611596847343044313)
                ·
                  refine ⟨26310934958697635507283235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35081246611596847343044313 26310934958697635507283235)
                  ·
                    refine ⟨39466402438046453260924853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26310934958697635507283235 39466402438046453260924853)
                    ·
                      refine ⟨3699975228566854993211705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39466402438046453260924853 3699975228566854993211705)
                      ·
                        rfl

theorem cell23_7205676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_7205676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205676 prefixEnd_7205676 := by exact prefixLift 7205676
  have htrace : WordTrace (prefixWord ++ tailWord_7205676) baseStart_7205676 baseEnd_7205676 := by
    simpa [prefixWord, tailWord_7205676, baseEnd_7205676] using wordTrace_append hprefix tailTrace_7205676
  have hstable : (prefixWord ++ tailWord_7205676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205676).length < 2 ^ (prefixWord ++ tailWord_7205676).sum := by decide
  have hdescent : baseEnd_7205676 < baseStart_7205676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205684 : List Nat := [2, 5, 1, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_7205684 : Nat := 118140960795 + 7205684 * 2 ^ 59
def prefixEnd_7205684 : Nat := 4983230072969 + 3 ^ 40 * 7205684 * 2
def baseEnd_7205684 : Nat := 3699979336412090961911669

theorem tailTrace_7205684 : CollatzResearch.WordTrace tailWord_7205684 prefixEnd_7205684 3699979336412090961911669 := by
  unfold tailWord_7205684
  simp only [CollatzResearch.WordTrace]
  refine ⟨131406443213522487848312053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175208590951363317131082737 131406443213522487848312053)
  ·
    refine ⟨12319354051267733235779255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131406443213522487848312053 12319354051267733235779255)
    ·
      refine ⟨18479031076901599853668883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12319354051267733235779255 18479031076901599853668883)
      ·
        refine ⟨27718546615352399780503325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18479031076901599853668883 27718546615352399780503325)
        ·
          refine ⟨10394454980757149917688747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27718546615352399780503325 10394454980757149917688747)
          ·
            refine ⟨15591682471135724876533121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10394454980757149917688747 15591682471135724876533121)
            ·
              refine ⟨11693761853351793657399841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15591682471135724876533121 11693761853351793657399841)
              ·
                refine ⟨8770321390013845243049881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11693761853351793657399841 8770321390013845243049881)
                ·
                  refine ⟨6577741042510383932287411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8770321390013845243049881 6577741042510383932287411)
                  ·
                    refine ⟨9866611563765575898431117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6577741042510383932287411 9866611563765575898431117)
                    ·
                      refine ⟨3699979336412090961911669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9866611563765575898431117 3699979336412090961911669)
                      ·
                        rfl

theorem cell23_7205684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_7205684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205684 prefixEnd_7205684 := by exact prefixLift 7205684
  have htrace : WordTrace (prefixWord ++ tailWord_7205684) baseStart_7205684 baseEnd_7205684 := by
    simpa [prefixWord, tailWord_7205684, baseEnd_7205684] using wordTrace_append hprefix tailTrace_7205684
  have hstable : (prefixWord ++ tailWord_7205684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205684).length < 2 ^ (prefixWord ++ tailWord_7205684).sum := by decide
  have hdescent : baseEnd_7205684 < baseStart_7205684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205713 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 7]
def baseStart_7205713 : Nat := 118140960795 + 7205713 * 2 ^ 59
def prefixEnd_7205713 : Nat := 4983230072969 + 3 ^ 40 * 7205713 * 2
def baseEnd_7205713 : Nat := 411110469705674594272115

theorem tailTrace_7205713 : CollatzResearch.WordTrace tailWord_7205713 prefixEnd_7205713 411110469705674594272115 := by
  unfold tailWord_7205713
  simp only [CollatzResearch.WordTrace]
  refine ⟨262813944143939913649429793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175209296095959942432953195 262813944143939913649429793)
  ·
    refine ⟨197110458107954935237072345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262813944143939913649429793 197110458107954935237072345)
    ·
      refine ⟨147832843580966201427804259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197110458107954935237072345 147832843580966201427804259)
      ·
        refine ⟨221749265371449302141706389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147832843580966201427804259 221749265371449302141706389)
        ·
          refine ⟨10394496814286686037892487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 221749265371449302141706389 10394496814286686037892487)
          ·
            refine ⟨15591745221430029056838731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10394496814286686037892487 15591745221430029056838731)
            ·
              refine ⟨23387617832145043585258097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15591745221430029056838731 23387617832145043585258097)
              ·
                refine ⟨17540713374108782688943573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23387617832145043585258097 17540713374108782688943573)
                ·
                  refine ⟨411110469705674594272115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17540713374108782688943573 411110469705674594272115)
                  ·
                    rfl

theorem cell23_7205713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 7].length) (baseStart_7205713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205713 prefixEnd_7205713 := by exact prefixLift 7205713
  have htrace : WordTrace (prefixWord ++ tailWord_7205713) baseStart_7205713 baseEnd_7205713 := by
    simpa [prefixWord, tailWord_7205713, baseEnd_7205713] using wordTrace_append hprefix tailTrace_7205713
  have hstable : (prefixWord ++ tailWord_7205713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205713).length < 2 ^ (prefixWord ++ tailWord_7205713).sum := by decide
  have hdescent : baseEnd_7205713 < baseStart_7205713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205758 : List Nat := [4, 2, 3, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_7205758 : Nat := 118140960795 + 7205758 * 2 ^ 59
def prefixEnd_7205758 : Nat := 4983230072969 + 3 ^ 40 * 7205758 * 2
def baseEnd_7205758 : Nat := 3700017333980523672386329

theorem tailTrace_7205758 : CollatzResearch.WordTrace tailWord_7205758 prefixEnd_7205758 3700017333980523672386329 := by
  unfold tailWord_7205758
  simp only [CollatzResearch.WordTrace]
  refine ⟨32851948178597110791852241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175210390285851257556545285 32851948178597110791852241)
  ·
    refine ⟨24638961133947833093889181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32851948178597110791852241 24638961133947833093889181)
    ·
      refine ⟨9239610425230437410208443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24638961133947833093889181 9239610425230437410208443)
      ·
        refine ⟨13859415637845656115312665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9239610425230437410208443 13859415637845656115312665)
        ·
          refine ⟨10394561728384242086484499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13859415637845656115312665 10394561728384242086484499)
          ·
            refine ⟨15591842592576363129726749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10394561728384242086484499 15591842592576363129726749)
            ·
              refine ⟨5846940972216136173647531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15591842592576363129726749 5846940972216136173647531)
              ·
                refine ⟨8770411458324204260471297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5846940972216136173647531 8770411458324204260471297)
                ·
                  refine ⟨6577808593743153195353473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8770411458324204260471297 6577808593743153195353473)
                  ·
                    refine ⟨4933356445307364896515105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6577808593743153195353473 4933356445307364896515105)
                    ·
                      refine ⟨3700017333980523672386329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4933356445307364896515105 3700017333980523672386329)
                      ·
                        rfl

theorem cell23_7205758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_7205758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205758 prefixEnd_7205758 := by exact prefixLift 7205758
  have htrace : WordTrace (prefixWord ++ tailWord_7205758) baseStart_7205758 baseEnd_7205758 := by
    simpa [prefixWord, tailWord_7205758, baseEnd_7205758] using wordTrace_append hprefix tailTrace_7205758
  have hstable : (prefixWord ++ tailWord_7205758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205758).length < 2 ^ (prefixWord ++ tailWord_7205758).sum := by decide
  have hdescent : baseEnd_7205758 < baseStart_7205758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205780 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_7205780 : Nat := 118140960795 + 7205780 * 2 ^ 59
def prefixEnd_7205780 : Nat := 4983230072969 + 3 ^ 40 * 7205780 * 2
def baseEnd_7205780 : Nat := 3700028630554922586311227

theorem tailTrace_7205780 : CollatzResearch.WordTrace tailWord_7205780 prefixEnd_7205780 3700028630554922586311227 := by
  unfold tailWord_7205780
  simp only [CollatzResearch.WordTrace]
  refine ⟨131408193917348592046059397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175210925223131456061412529 131408193917348592046059397)
  ·
    refine ⟨24639036359502861008636137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131408193917348592046059397 24639036359502861008636137)
    ·
      refine ⟨18479277269627145756477103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24639036359502861008636137 18479277269627145756477103)
      ·
        refine ⟨27718915904440718634715655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18479277269627145756477103 27718915904440718634715655)
        ·
          refine ⟨41578373856661077952073483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27718915904440718634715655 41578373856661077952073483)
          ·
            refine ⟨62367560784991616928110225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41578373856661077952073483 62367560784991616928110225)
            ·
              refine ⟨46775670588743712696082669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62367560784991616928110225 46775670588743712696082669)
              ·
                refine ⟨17540876470778892261031001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46775670588743712696082669 17540876470778892261031001)
                ·
                  refine ⟨13155657353084169195773251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17540876470778892261031001 13155657353084169195773251)
                  ·
                    refine ⟨19733486029626253793659877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13155657353084169195773251 19733486029626253793659877)
                    ·
                      refine ⟨3700028630554922586311227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19733486029626253793659877 3700028630554922586311227)
                      ·
                        rfl

theorem cell23_7205780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_7205780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205780 prefixEnd_7205780 := by exact prefixLift 7205780
  have htrace : WordTrace (prefixWord ++ tailWord_7205780) baseStart_7205780 baseEnd_7205780 := by
    simpa [prefixWord, tailWord_7205780, baseEnd_7205780] using wordTrace_append hprefix tailTrace_7205780
  have hstable : (prefixWord ++ tailWord_7205780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205780).length < 2 ^ (prefixWord ++ tailWord_7205780).sum := by decide
  have hdescent : baseEnd_7205780 < baseStart_7205780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205783 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 3]
def baseStart_7205783 : Nat := 118140960795 + 7205783 * 2 ^ 59
def prefixEnd_7205783 : Nat := 4983230072969 + 3 ^ 40 * 7205783 * 2
def baseEnd_7205783 : Nat := 3700030170996886074573713

theorem tailTrace_7205783 : CollatzResearch.WordTrace tailWord_7205783 prefixEnd_7205783 3700030170996886074573713 := by
  unfold tailWord_7205783
  simp only [CollatzResearch.WordTrace]
  refine ⟨262816497253686315604478003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175210998169124210402985335 262816497253686315604478003)
  ·
    refine ⟨394224745880529473406717005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262816497253686315604478003 394224745880529473406717005)
    ·
      refine ⟨147834279705198552527518877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394224745880529473406717005 147834279705198552527518877)
      ·
        refine ⟨55437854889449457197819579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147834279705198552527518877 55437854889449457197819579)
        ·
          refine ⟨83156782334174185796729369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55437854889449457197819579 83156782334174185796729369)
          ·
            refine ⟨62367586750630639347547027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83156782334174185796729369 62367586750630639347547027)
            ·
              refine ⟨93551380125945959021320541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62367586750630639347547027 93551380125945959021320541)
              ·
                refine ⟨35081767547229734632995203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93551380125945959021320541 35081767547229734632995203)
                ·
                  refine ⟨52622651320844601949492805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35081767547229734632995203 52622651320844601949492805)
                  ·
                    refine ⟨9866747122658362865529901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52622651320844601949492805 9866747122658362865529901)
                    ·
                      refine ⟨3700030170996886074573713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9866747122658362865529901 3700030170996886074573713)
                      ·
                        rfl

theorem cell23_7205783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_7205783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205783 prefixEnd_7205783 := by exact prefixLift 7205783
  have htrace : WordTrace (prefixWord ++ tailWord_7205783) baseStart_7205783 baseEnd_7205783 := by
    simpa [prefixWord, tailWord_7205783, baseEnd_7205783] using wordTrace_append hprefix tailTrace_7205783
  have hstable : (prefixWord ++ tailWord_7205783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205783).length < 2 ^ (prefixWord ++ tailWord_7205783).sum := by decide
  have hdescent : baseEnd_7205783 < baseStart_7205783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205858 : List Nat := [3, 3, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7205858 : Nat := 118140960795 + 7205858 * 2 ^ 59
def prefixEnd_7205858 : Nat := 4983230072969 + 3 ^ 40 * 7205858 * 2
def baseEnd_7205858 : Nat := 1233356227348657760378623

theorem tailTrace_7205858 : CollatzResearch.WordTrace tailWord_7205858 prefixEnd_7205858 1233356227348657760378623 := by
  unfold tailWord_7205858
  simp only [CollatzResearch.WordTrace]
  refine ⟨65704808182103650853364557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175212821818943068942305485 65704808182103650853364557)
  ·
    refine ⟨24639303068288869070011709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65704808182103650853364557 24639303068288869070011709)
    ·
      refine ⟨9239738650608325901254391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24639303068288869070011709 9239738650608325901254391)
      ·
        refine ⟨13859607975912488851881587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9239738650608325901254391 13859607975912488851881587)
        ·
          refine ⟨20789411963868733277822381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13859607975912488851881587 20789411963868733277822381)
          ·
            refine ⟨7796029486450774979183393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20789411963868733277822381 7796029486450774979183393)
            ·
              refine ⟨5847022114838081234387545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7796029486450774979183393 5847022114838081234387545)
              ·
                refine ⟨4385266586128560925790659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5847022114838081234387545 4385266586128560925790659)
                ·
                  refine ⟨6577899879192841388685989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385266586128560925790659 6577899879192841388685989)
                  ·
                    refine ⟨1233356227348657760378623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6577899879192841388685989 1233356227348657760378623)
                    ·
                      rfl

theorem cell23_7205858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7205858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205858 prefixEnd_7205858 := by exact prefixLift 7205858
  have htrace : WordTrace (prefixWord ++ tailWord_7205858) baseStart_7205858 baseEnd_7205858 := by
    simpa [prefixWord, tailWord_7205858, baseEnd_7205858] using wordTrace_append hprefix tailTrace_7205858
  have hstable : (prefixWord ++ tailWord_7205858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205858).length < 2 ^ (prefixWord ++ tailWord_7205858).sum := by decide
  have hdescent : baseEnd_7205858 < baseStart_7205858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205900 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_7205900 : Nat := 118140960795 + 7205900 * 2 ^ 59
def prefixEnd_7205900 : Nat := 4983230072969 + 3 ^ 40 * 7205900 * 2
def baseEnd_7205900 : Nat := 3700090248233462116810675

theorem tailTrace_7205900 : CollatzResearch.WordTrace tailWord_7205900 prefixEnd_7205900 3700090248233462116810675 := by
  unfold tailWord_7205900
  simp only [CollatzResearch.WordTrace]
  refine ⟨131410382297131222293243577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175213843062841629724324769 131410382297131222293243577)
  ·
    refine ⟨98557786722848416719932683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131410382297131222293243577 98557786722848416719932683)
    ·
      refine ⟨147836680084272625079899025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98557786722848416719932683 147836680084272625079899025)
      ·
        refine ⟨110877510063204468809924269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147836680084272625079899025 110877510063204468809924269)
        ·
          refine ⟨41579066273701675803721601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110877510063204468809924269 41579066273701675803721601)
          ·
            refine ⟨31184299705276256852791201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41579066273701675803721601 31184299705276256852791201)
            ·
              refine ⟨23388224778957192639593401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31184299705276256852791201 23388224778957192639593401)
              ·
                refine ⟨17541168584217894479695051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23388224778957192639593401 17541168584217894479695051)
                ·
                  refine ⟨26311752876326841719542577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17541168584217894479695051 26311752876326841719542577)
                  ·
                    refine ⟨19733814657245131289656933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26311752876326841719542577 19733814657245131289656933)
                    ·
                      refine ⟨3700090248233462116810675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19733814657245131289656933 3700090248233462116810675)
                      ·
                        rfl

theorem cell23_7205900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_7205900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205900 prefixEnd_7205900 := by exact prefixLift 7205900
  have htrace : WordTrace (prefixWord ++ tailWord_7205900) baseStart_7205900 baseEnd_7205900 := by
    simpa [prefixWord, tailWord_7205900, baseEnd_7205900] using wordTrace_append hprefix tailTrace_7205900
  have hstable : (prefixWord ++ tailWord_7205900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205900).length < 2 ^ (prefixWord ++ tailWord_7205900).sum := by decide
  have hdescent : baseEnd_7205900 < baseStart_7205900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205921 : List Nat := [1, 2, 3, 2, 3, 1, 2, 4, 1, 2, 2]
def baseStart_7205921 : Nat := 118140960795 + 7205921 * 2 ^ 59
def prefixEnd_7205921 : Nat := 4983230072969 + 3 ^ 40 * 7205921 * 2
def baseEnd_7205921 : Nat := 3700101031327206534648079

theorem tailTrace_7205921 : CollatzResearch.WordTrace tailWord_7205921 prefixEnd_7205921 3700101031327206534648079 := by
  unfold tailWord_7205921
  simp only [CollatzResearch.WordTrace]
  refine ⟨262821530527186365173001617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175214353684790910115334411 262821530527186365173001617)
  ·
    refine ⟨197116147895389773879751213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262821530527186365173001617 197116147895389773879751213)
    ·
      refine ⟨73918555460771165204906705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197116147895389773879751213 73918555460771165204906705)
      ·
        refine ⟨55438916595578373903680029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73918555460771165204906705 55438916595578373903680029)
        ·
          refine ⟨20789593723341890213880011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55438916595578373903680029 20789593723341890213880011)
          ·
            refine ⟨31184390585012835320820017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20789593723341890213880011 31184390585012835320820017)
            ·
              refine ⟨23388292938759626490615013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31184390585012835320820017 23388292938759626490615013)
              ·
                refine ⟨4385304926017429966990315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23388292938759626490615013 4385304926017429966990315)
                ·
                  refine ⟨6577957389026144950485473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385304926017429966990315 6577957389026144950485473)
                  ·
                    refine ⟨4933468041769608712864105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6577957389026144950485473 4933468041769608712864105)
                    ·
                      refine ⟨3700101031327206534648079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4933468041769608712864105 3700101031327206534648079)
                      ·
                        rfl

theorem cell23_7205921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_7205921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205921 prefixEnd_7205921 := by exact prefixLift 7205921
  have htrace : WordTrace (prefixWord ++ tailWord_7205921) baseStart_7205921 baseEnd_7205921 := by
    simpa [prefixWord, tailWord_7205921, baseEnd_7205921] using wordTrace_append hprefix tailTrace_7205921
  have hstable : (prefixWord ++ tailWord_7205921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205921).length < 2 ^ (prefixWord ++ tailWord_7205921).sum := by decide
  have hdescent : baseEnd_7205921 < baseStart_7205921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7205980 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_7205980 : Nat := 118140960795 + 7205980 * 2 ^ 59
def prefixEnd_7205980 : Nat := 4983230072969 + 3 ^ 40 * 7205980 * 2
def baseEnd_7205980 : Nat := 3700131326685821803810307

theorem tailTrace_7205980 : CollatzResearch.WordTrace tailWord_7205980 prefixEnd_7205980 3700131326685821803810307 := by
  unfold tailWord_7205980
  simp only [CollatzResearch.WordTrace]
  refine ⟨131411841216986309124699697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175215788289315078832932929 131411841216986309124699697)
  ·
    refine ⟨98558880912739731843524773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131411841216986309124699697 98558880912739731843524773)
    ·
      refine ⟨18479790171138699720660895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98558880912739731843524773 18479790171138699720660895)
      ·
        refine ⟨27719685256708049580991343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18479790171138699720660895 27719685256708049580991343)
        ·
          refine ⟨41579527885062074371487015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27719685256708049580991343 41579527885062074371487015)
          ·
            refine ⟨62369291827593111557230523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41579527885062074371487015 62369291827593111557230523)
            ·
              refine ⟨93553937741389667335845785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62369291827593111557230523 93553937741389667335845785)
              ·
                refine ⟨70165453306042250501884339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93553937741389667335845785 70165453306042250501884339)
                ·
                  refine ⟨105248179959063375752826509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70165453306042250501884339 105248179959063375752826509)
                  ·
                    refine ⟨39468067484648765907309941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105248179959063375752826509 39468067484648765907309941)
                    ·
                      refine ⟨3700131326685821803810307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39468067484648765907309941 3700131326685821803810307)
                      ·
                        rfl

theorem cell23_7205980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_7205980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7205980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7205980 prefixEnd_7205980 := by exact prefixLift 7205980
  have htrace : WordTrace (prefixWord ++ tailWord_7205980) baseStart_7205980 baseEnd_7205980 := by
    simpa [prefixWord, tailWord_7205980, baseEnd_7205980] using wordTrace_append hprefix tailTrace_7205980
  have hstable : (prefixWord ++ tailWord_7205980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7205980).length < 2 ^ (prefixWord ++ tailWord_7205980).sum := by decide
  have hdescent : baseEnd_7205980 < baseStart_7205980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7205980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206003 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 8]
def baseStart_7206003 : Nat := 118140960795 + 7206003 * 2 ^ 59
def prefixEnd_7206003 : Nat := 4983230072969 + 3 ^ 40 * 7206003 * 2
def baseEnd_7206003 : Nat := 3700143136740875213822701

theorem tailTrace_7206003 : CollatzResearch.WordTrace tailWord_7206003 prefixEnd_7206003 3700143136740875213822701 := by
  unfold tailWord_7206003
  simp only [CollatzResearch.WordTrace]
  refine ⟨262824521312889293177486663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175216347541926195451657775 262824521312889293177486663)
  ·
    refine ⟨394236781969333939766229995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262824521312889293177486663 394236781969333939766229995)
    ·
      refine ⟨591355172954000909649344993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394236781969333939766229995 591355172954000909649344993)
      ·
        refine ⟨443516379715500682237008745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591355172954000909649344993 443516379715500682237008745)
        ·
          refine ⟨332637284786625511677756559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443516379715500682237008745 332637284786625511677756559)
          ·
            refine ⟨498955927179938267516634839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332637284786625511677756559 498955927179938267516634839)
            ·
              refine ⟨748433890769907401274952259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498955927179938267516634839 748433890769907401274952259)
              ·
                refine ⟨1122650836154861101912428389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748433890769907401274952259 1122650836154861101912428389)
                ·
                  refine ⟨210497031779036456608580323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1122650836154861101912428389 210497031779036456608580323)
                  ·
                    refine ⟨315745547668554684912870485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 210497031779036456608580323 315745547668554684912870485)
                    ·
                      refine ⟨3700143136740875213822701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 315745547668554684912870485 3700143136740875213822701)
                      ·
                        rfl

theorem cell23_7206003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_7206003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206003 prefixEnd_7206003 := by exact prefixLift 7206003
  have htrace : WordTrace (prefixWord ++ tailWord_7206003) baseStart_7206003 baseEnd_7206003 := by
    simpa [prefixWord, tailWord_7206003, baseEnd_7206003] using wordTrace_append hprefix tailTrace_7206003
  have hstable : (prefixWord ++ tailWord_7206003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206003).length < 2 ^ (prefixWord ++ tailWord_7206003).sum := by decide
  have hdescent : baseEnd_7206003 < baseStart_7206003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206034 : List Nat := [3, 2, 3, 1, 1, 3, 1, 4, 5]
def baseStart_7206034 : Nat := 118140960795 + 7206034 * 2 ^ 59
def prefixEnd_7206034 : Nat := 4983230072969 + 3 ^ 40 * 7206034 * 2
def baseEnd_7206034 : Nat := 411128783849018288059451

theorem tailTrace_7206034 : CollatzResearch.WordTrace tailWord_7206034 prefixEnd_7206034 411128783849018288059451 := by
  unfold tailWord_7206034
  simp only [CollatzResearch.WordTrace]
  refine ⟨65706412993944246367966289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175217101317184656981243437 65706412993944246367966289)
  ·
    refine ⟨49279809745458184775974717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65706412993944246367966289 49279809745458184775974717)
    ·
      refine ⟨18479928654546819290990519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49279809745458184775974717 18479928654546819290990519)
      ·
        refine ⟨27719892981820228936485779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18479928654546819290990519 27719892981820228936485779)
        ·
          refine ⟨41579839472730343404728669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27719892981820228936485779 41579839472730343404728669)
          ·
            refine ⟨15592439802273878776773251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41579839472730343404728669 15592439802273878776773251)
            ·
              refine ⟨23388659703410818165159877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15592439802273878776773251 23388659703410818165159877)
              ·
                refine ⟨4385373694389528405967477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23388659703410818165159877 4385373694389528405967477)
                ·
                  refine ⟨411128783849018288059451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4385373694389528405967477 411128783849018288059451)
                  ·
                    rfl

theorem cell23_7206034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_7206034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206034 prefixEnd_7206034 := by exact prefixLift 7206034
  have htrace : WordTrace (prefixWord ++ tailWord_7206034) baseStart_7206034 baseEnd_7206034 := by
    simpa [prefixWord, tailWord_7206034, baseEnd_7206034] using wordTrace_append hprefix tailTrace_7206034
  have hstable : (prefixWord ++ tailWord_7206034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206034).length < 2 ^ (prefixWord ++ tailWord_7206034).sum := by decide
  have hdescent : baseEnd_7206034 < baseStart_7206034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206067 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 4]
def baseStart_7206067 : Nat := 118140960795 + 7206067 * 2 ^ 59
def prefixEnd_7206067 : Nat := 4983230072969 + 3 ^ 40 * 7206067 * 2
def baseEnd_7206067 : Nat := 3700175999502762963422407

theorem tailTrace_7206067 : CollatzResearch.WordTrace tailWord_7206067 prefixEnd_7206067 3700175999502762963422407 := by
  unfold tailWord_7206067
  simp only [CollatzResearch.WordTrace]
  refine ⟨262826855584657432107816455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175217903723104954738544303 262826855584657432107816455)
  ·
    refine ⟨394240283376986148161724683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262826855584657432107816455 394240283376986148161724683)
    ·
      refine ⟨591360425065479222242587025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394240283376986148161724683 591360425065479222242587025)
      ·
        refine ⟨443520318799109416681940269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591360425065479222242587025 443520318799109416681940269)
        ·
          refine ⟨166320119549666031255727601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443520318799109416681940269 166320119549666031255727601)
          ·
            refine ⟨124740089662249523441795701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166320119549666031255727601 124740089662249523441795701)
            ·
              refine ⟨11694383405835892822668347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124740089662249523441795701 11694383405835892822668347)
              ·
                refine ⟨17541575108753839234002521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11694383405835892822668347 17541575108753839234002521)
                ·
                  refine ⟨13156181331565379425501891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17541575108753839234002521 13156181331565379425501891)
                  ·
                    refine ⟨19734271997348069138252837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13156181331565379425501891 19734271997348069138252837)
                    ·
                      refine ⟨3700175999502762963422407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19734271997348069138252837 3700175999502762963422407)
                      ·
                        rfl

theorem cell23_7206067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 4].length) (baseStart_7206067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206067 prefixEnd_7206067 := by exact prefixLift 7206067
  have htrace : WordTrace (prefixWord ++ tailWord_7206067) baseStart_7206067 baseEnd_7206067 := by
    simpa [prefixWord, tailWord_7206067, baseEnd_7206067] using wordTrace_append hprefix tailTrace_7206067
  have hstable : (prefixWord ++ tailWord_7206067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206067).length < 2 ^ (prefixWord ++ tailWord_7206067).sum := by decide
  have hdescent : baseEnd_7206067 < baseStart_7206067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206087 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_7206087 : Nat := 118140960795 + 7206087 * 2 ^ 59
def prefixEnd_7206087 : Nat := 4983230072969 + 3 ^ 40 * 7206087 * 2
def baseEnd_7206087 : Nat := 3700186269115852885172315

theorem tailTrace_7206087 : CollatzResearch.WordTrace tailWord_7206087 prefixEnd_7206087 3700186269115852885172315 := by
  unfold tailWord_7206087
  simp only [CollatzResearch.WordTrace]
  refine ⟨262827585044584975523544515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175218390029723317015696343 262827585044584975523544515)
  ·
    refine ⟨394241377566877463285316773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262827585044584975523544515 394241377566877463285316773)
    ·
      refine ⟨73920258293789524365996895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394241377566877463285316773 73920258293789524365996895)
      ·
        refine ⟨110880387440684286548995343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73920258293789524365996895 110880387440684286548995343)
        ·
          refine ⟨166320581161026429823493015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110880387440684286548995343 166320581161026429823493015)
          ·
            refine ⟨249480871741539644735239523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166320581161026429823493015 249480871741539644735239523)
            ·
              refine ⟨374221307612309467102859285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249480871741539644735239523 374221307612309467102859285)
              ·
                refine ⟨17541623794327006270446529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 374221307612309467102859285 17541623794327006270446529)
                ·
                  refine ⟨13156217845745254702834897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17541623794327006270446529 13156217845745254702834897)
                  ·
                    refine ⟨9867163384308941027126173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13156217845745254702834897 9867163384308941027126173)
                    ·
                      refine ⟨3700186269115852885172315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9867163384308941027126173 3700186269115852885172315)
                      ·
                        rfl

theorem cell23_7206087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_7206087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206087 prefixEnd_7206087 := by exact prefixLift 7206087
  have htrace : WordTrace (prefixWord ++ tailWord_7206087) baseStart_7206087 baseEnd_7206087 := by
    simpa [prefixWord, tailWord_7206087, baseEnd_7206087] using wordTrace_append hprefix tailTrace_7206087
  have hstable : (prefixWord ++ tailWord_7206087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206087).length < 2 ^ (prefixWord ++ tailWord_7206087).sum := by decide
  have hdescent : baseEnd_7206087 < baseStart_7206087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206137 : List Nat := [1, 2, 1, 3, 1, 1, 3, 5, 1, 5]
def baseStart_7206137 : Nat := 118140960795 + 7206137 * 2 ^ 59
def prefixEnd_7206137 : Nat := 4983230072969 + 3 ^ 40 * 7206137 * 2
def baseEnd_7206137 : Nat := 1233403981049525896515695

theorem tailTrace_7206137 : CollatzResearch.WordTrace tailWord_7206137 prefixEnd_7206137 1233403981049525896515695 := by
  unfold tailWord_7206137
  simp only [CollatzResearch.WordTrace]
  refine ⟨262829408694403834062864665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175219605796269222708576443 262829408694403834062864665)
  ·
    refine ⟨197122056520802875547148499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262829408694403834062864665 197122056520802875547148499)
    ·
      refine ⟨295683084781204313320722749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197122056520802875547148499 295683084781204313320722749)
      ·
        refine ⟨110881156792951617495271031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295683084781204313320722749 110881156792951617495271031)
        ·
          refine ⟨166321735189427426242906547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110881156792951617495271031 166321735189427426242906547)
          ·
            refine ⟨249482602784141139364359821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166321735189427426242906547 249482602784141139364359821)
            ·
              refine ⟨93555976044052927261634933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249482602784141139364359821 93555976044052927261634933)
              ·
                refine ⟨8770872754129961930778275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93555976044052927261634933 8770872754129961930778275)
                ·
                  refine ⟨13156309131194942896167413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8770872754129961930778275 13156309131194942896167413)
                  ·
                    refine ⟨1233403981049525896515695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13156309131194942896167413 1233403981049525896515695)
                    ·
                      rfl

theorem cell23_7206137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 5].length) (baseStart_7206137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206137 prefixEnd_7206137 := by exact prefixLift 7206137
  have htrace : WordTrace (prefixWord ++ tailWord_7206137) baseStart_7206137 baseEnd_7206137 := by
    simpa [prefixWord, tailWord_7206137, baseEnd_7206137] using wordTrace_append hprefix tailTrace_7206137
  have hstable : (prefixWord ++ tailWord_7206137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206137).length < 2 ^ (prefixWord ++ tailWord_7206137).sum := by decide
  have hdescent : baseEnd_7206137 < baseStart_7206137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206160 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 5]
def baseStart_7206160 : Nat := 118140960795 + 7206160 * 2 ^ 59
def prefixEnd_7206160 : Nat := 4983230072969 + 3 ^ 40 * 7206160 * 2
def baseEnd_7206160 : Nat := 3700223753203631099559479

theorem tailTrace_7206160 : CollatzResearch.WordTrace tailWord_7206160 prefixEnd_7206160 3700223753203631099559479 := by
  unfold tailWord_7206160
  simp only [CollatzResearch.WordTrace]
  refine ⟨131415123786660254495475967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175220165048880339327301289 131415123786660254495475967)
  ·
    refine ⟨197122685679990381743213951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131415123786660254495475967 197122685679990381743213951)
    ·
      refine ⟨295684028519985572614820927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197122685679990381743213951 295684028519985572614820927)
      ·
        refine ⟨443526042779978358922231391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295684028519985572614820927 443526042779978358922231391)
        ·
          refine ⟨665289064169967538383347087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443526042779978358922231391 665289064169967538383347087)
          ·
            refine ⟨997933596254951307575020631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665289064169967538383347087 997933596254951307575020631)
            ·
              refine ⟨1496900394382426961362530947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997933596254951307575020631 1496900394382426961362530947)
              ·
                refine ⟨2245350591573640442043796421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496900394382426961362530947 2245350591573640442043796421)
                ·
                  refine ⟨421003235920057582883211829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2245350591573640442043796421 421003235920057582883211829)
                  ·
                    refine ⟨39469053367505398395301109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 421003235920057582883211829 39469053367505398395301109)
                    ·
                      refine ⟨3700223753203631099559479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39469053367505398395301109 3700223753203631099559479)
                      ·
                        rfl

theorem cell23_7206160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_7206160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206160 prefixEnd_7206160 := by exact prefixLift 7206160
  have htrace : WordTrace (prefixWord ++ tailWord_7206160) baseStart_7206160 baseEnd_7206160 := by
    simpa [prefixWord, tailWord_7206160, baseEnd_7206160] using wordTrace_append hprefix tailTrace_7206160
  have hstable : (prefixWord ++ tailWord_7206160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206160).length < 2 ^ (prefixWord ++ tailWord_7206160).sum := by decide
  have hdescent : baseEnd_7206160 < baseStart_7206160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206167 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 1, 6]
def baseStart_7206167 : Nat := 118140960795 + 7206167 * 2 ^ 59
def prefixEnd_7206167 : Nat := 4983230072969 + 3 ^ 40 * 7206167 * 2
def baseEnd_7206167 : Nat := 1233409115856070857390649

theorem tailTrace_7206167 : CollatzResearch.WordTrace tailWord_7206167 prefixEnd_7206167 1233409115856070857390649 := by
  unfold tailWord_7206167
  simp only [CollatzResearch.WordTrace]
  refine ⟨262830502884295149186456755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175220335256196766124304503 262830502884295149186456755)
  ·
    refine ⟨394245754326442723779685133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262830502884295149186456755 394245754326442723779685133)
    ·
      refine ⟨147842157872416021417381925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394245754326442723779685133 147842157872416021417381925)
      ·
        refine ⟨27720404601078004015759111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147842157872416021417381925 27720404601078004015759111)
        ·
          refine ⟨41580606901617006023638667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27720404601078004015759111 41580606901617006023638667)
          ·
            refine ⟨62370910352425509035458001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41580606901617006023638667 62370910352425509035458001)
            ·
              refine ⟨46778182764319131776593501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62370910352425509035458001 46778182764319131776593501)
              ·
                refine ⟨17541818536619674416222563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46778182764319131776593501 17541818536619674416222563)
                ·
                  refine ⟨26312727804929511624333845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17541818536619674416222563 26312727804929511624333845)
                  ·
                    refine ⟨1233409115856070857390649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26312727804929511624333845 1233409115856070857390649)
                    ·
                      rfl

theorem cell23_7206167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_7206167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206167 prefixEnd_7206167 := by exact prefixLift 7206167
  have htrace : WordTrace (prefixWord ++ tailWord_7206167) baseStart_7206167 baseEnd_7206167 := by
    simpa [prefixWord, tailWord_7206167, baseEnd_7206167] using wordTrace_append hprefix tailTrace_7206167
  have hstable : (prefixWord ++ tailWord_7206167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206167).length < 2 ^ (prefixWord ++ tailWord_7206167).sum := by decide
  have hdescent : baseEnd_7206167 < baseStart_7206167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206178 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_7206178 : Nat := 118140960795 + 7206178 * 2 ^ 59
def prefixEnd_7206178 : Nat := 4983230072969 + 3 ^ 40 * 7206178 * 2
def baseEnd_7206178 : Nat := 3700232995855412029134397

theorem tailTrace_7206178 : CollatzResearch.WordTrace tailWord_7206178 prefixEnd_7206178 3700232995855412029134397 := by
  unfold tailWord_7206178
  simp only [CollatzResearch.WordTrace]
  refine ⟨65707726021813824516276797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175220602724836865376738125 65707726021813824516276797)
  ·
    refine ⟨24640397258180184193603799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65707726021813824516276797 24640397258180184193603799)
    ·
      refine ⟨36960595887270276290405699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24640397258180184193603799 36960595887270276290405699)
      ·
        refine ⟨55440893830905414435608549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36960595887270276290405699 55440893830905414435608549)
        ·
          refine ⟨10395167593294765206676603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55440893830905414435608549 10395167593294765206676603)
          ·
            refine ⟨15592751389942147810014905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10395167593294765206676603 15592751389942147810014905)
            ·
              refine ⟨11694563542456610857511179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15592751389942147810014905 11694563542456610857511179)
              ·
                refine ⟨17541845313684916286266769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11694563542456610857511179 17541845313684916286266769)
                ·
                  refine ⟨13156383985263687214700077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17541845313684916286266769 13156383985263687214700077)
                  ·
                    refine ⟨4933643994473882705512529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13156383985263687214700077 4933643994473882705512529)
                    ·
                      refine ⟨3700232995855412029134397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4933643994473882705512529 3700232995855412029134397)
                      ·
                        rfl

theorem cell23_7206178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_7206178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206178 prefixEnd_7206178 := by exact prefixLift 7206178
  have htrace : WordTrace (prefixWord ++ tailWord_7206178) baseStart_7206178 baseEnd_7206178 := by
    simpa [prefixWord, tailWord_7206178, baseEnd_7206178] using wordTrace_append hprefix tailTrace_7206178
  have hstable : (prefixWord ++ tailWord_7206178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206178).length < 2 ^ (prefixWord ++ tailWord_7206178).sum := by decide
  have hdescent : baseEnd_7206178 < baseStart_7206178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206184 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 1, 6]
def baseStart_7206184 : Nat := 118140960795 + 7206184 * 2 ^ 59
def prefixEnd_7206184 : Nat := 4983230072969 + 3 ^ 40 * 7206184 * 2
def baseEnd_7206184 : Nat := 1233412025579779668553123

theorem tailTrace_7206184 : CollatzResearch.WordTrace tailWord_7206184 prefixEnd_7206184 1233412025579779668553123 := by
  unfold tailWord_7206184
  simp only [CollatzResearch.WordTrace]
  refine ⟨131415561462616780544912803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175220748616822374059883737 131415561462616780544912803)
  ·
    refine ⟨197123342193925170817369205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131415561462616780544912803 197123342193925170817369205)
    ·
      refine ⟨18480313330680484764128363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197123342193925170817369205 18480313330680484764128363)
      ·
        refine ⟨27720469996020727146192545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18480313330680484764128363 27720469996020727146192545)
        ·
          refine ⟨20790352497015545359644409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27720469996020727146192545 20790352497015545359644409)
          ·
            refine ⟨15592764372761659019733307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20790352497015545359644409 15592764372761659019733307)
            ·
              refine ⟨23389146559142488529599961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15592764372761659019733307 23389146559142488529599961)
              ·
                refine ⟨17541859919356866397199971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23389146559142488529599961 17541859919356866397199971)
                ·
                  refine ⟨26312789879035299595799957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17541859919356866397199971 26312789879035299595799957)
                  ·
                    refine ⟨1233412025579779668553123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26312789879035299595799957 1233412025579779668553123)
                    ·
                      rfl

theorem cell23_7206184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_7206184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206184 prefixEnd_7206184 := by exact prefixLift 7206184
  have htrace : WordTrace (prefixWord ++ tailWord_7206184) baseStart_7206184 baseEnd_7206184 := by
    simpa [prefixWord, tailWord_7206184, baseEnd_7206184] using wordTrace_append hprefix tailTrace_7206184
  have hstable : (prefixWord ++ tailWord_7206184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206184).length < 2 ^ (prefixWord ++ tailWord_7206184).sum := by decide
  have hdescent : baseEnd_7206184 < baseStart_7206184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206194 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_7206194 : Nat := 118140960795 + 7206194 * 2 ^ 59
def prefixEnd_7206194 : Nat := 4983230072969 + 3 ^ 40 * 7206194 * 2
def baseEnd_7206194 : Nat := 3700241211545883966534323

theorem tailTrace_7206194 : CollatzResearch.WordTrace tailWord_7206194 prefixEnd_7206194 3700241211545883966534323 := by
  unfold tailWord_7206194
  simp only [CollatzResearch.WordTrace]
  refine ⟨65707871913799333199422409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175220991770131555198459757 65707871913799333199422409)
  ·
    refine ⟨49280903935349499899566807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65707871913799333199422409 49280903935349499899566807)
    ·
      refine ⟨73921355903024249849350211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49280903935349499899566807 73921355903024249849350211)
      ·
        refine ⟨110882033854536374774025317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73921355903024249849350211 110882033854536374774025317)
        ·
          refine ⟨20790381347725570270129747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110882033854536374774025317 20790381347725570270129747)
          ·
            refine ⟨31185572021588355405194621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20790381347725570270129747 31185572021588355405194621)
            ·
              refine ⟨11694589508095633276947983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31185572021588355405194621 11694589508095633276947983)
              ·
                refine ⟨17541884262143449915421975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11694589508095633276947983 17541884262143449915421975)
                ·
                  refine ⟨26312826393215174873132963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17541884262143449915421975 26312826393215174873132963)
                  ·
                    refine ⟨39469239589822762309699445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26312826393215174873132963 39469239589822762309699445)
                    ·
                      refine ⟨3700241211545883966534323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39469239589822762309699445 3700241211545883966534323)
                      ·
                        rfl

theorem cell23_7206194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_7206194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206194 prefixEnd_7206194 := by exact prefixLift 7206194
  have htrace : WordTrace (prefixWord ++ tailWord_7206194) baseStart_7206194 baseEnd_7206194 := by
    simpa [prefixWord, tailWord_7206194, baseEnd_7206194] using wordTrace_append hprefix tailTrace_7206194
  have hstable : (prefixWord ++ tailWord_7206194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206194).length < 2 ^ (prefixWord ++ tailWord_7206194).sum := by decide
  have hdescent : baseEnd_7206194 < baseStart_7206194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206208 : List Nat := [2, 1, 1, 2, 2, 1, 5, 4, 1, 2, 2]
def baseStart_7206208 : Nat := 118140960795 + 7206208 * 2 ^ 59
def prefixEnd_7206208 : Nat := 4983230072969 + 3 ^ 40 * 7206208 * 2
def baseEnd_7206208 : Nat := 3700248400275046911759259

theorem tailTrace_7206208 : CollatzResearch.WordTrace tailWord_7206208 prefixEnd_7206208 3700248400275046911759259 := by
  unfold tailWord_7206208
  simp only [CollatzResearch.WordTrace]
  refine ⟨131415999138573306594349639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175221332184764408792466185 131415999138573306594349639)
  ·
    refine ⟨197123998707859959891524459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131415999138573306594349639 197123998707859959891524459)
    ·
      refine ⟨295685998061789939837286689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197123998707859959891524459 295685998061789939837286689)
      ·
        refine ⟨221764498546342454877965017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295685998061789939837286689 221764498546342454877965017)
        ·
          refine ⟨166323373909756841158473763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221764498546342454877965017 166323373909756841158473763)
          ·
            refine ⟨249485060864635261737710645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166323373909756841158473763 249485060864635261737710645)
            ·
              refine ⟨23389224456059555787910373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249485060864635261737710645 23389224456059555787910373)
              ·
                refine ⟨4385479585511166710233195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23389224456059555787910373 4385479585511166710233195)
                ·
                  refine ⟨6578219378266750065349793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385479585511166710233195 6578219378266750065349793)
                  ·
                    refine ⟨4933664533700062549012345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6578219378266750065349793 4933664533700062549012345)
                    ·
                      refine ⟨3700248400275046911759259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4933664533700062549012345 3700248400275046911759259)
                      ·
                        rfl

theorem cell23_7206208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 1, 2, 2].length) (baseStart_7206208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206208 prefixEnd_7206208 := by exact prefixLift 7206208
  have htrace : WordTrace (prefixWord ++ tailWord_7206208) baseStart_7206208 baseEnd_7206208 := by
    simpa [prefixWord, tailWord_7206208, baseEnd_7206208] using wordTrace_append hprefix tailTrace_7206208
  have hstable : (prefixWord ++ tailWord_7206208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206208).length < 2 ^ (prefixWord ++ tailWord_7206208).sum := by decide
  have hdescent : baseEnd_7206208 < baseStart_7206208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206224 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 3]
def baseStart_7206224 : Nat := 118140960795 + 7206224 * 2 ^ 59
def prefixEnd_7206224 : Nat := 4983230072969 + 3 ^ 40 * 7206224 * 2
def baseEnd_7206224 : Nat := 3700256615965518849159185

theorem tailTrace_7206224 : CollatzResearch.WordTrace tailWord_7206224 prefixEnd_7206224 3700256615965518849159185 := by
  unfold tailWord_7206224
  simp only [CollatzResearch.WordTrace]
  refine ⟨131416290922544323960640863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175221721230059098614187817 131416290922544323960640863)
  ·
    refine ⟨197124436383816485940961295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131416290922544323960640863 197124436383816485940961295)
    ·
      refine ⟨295686654575724728911441943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197124436383816485940961295 295686654575724728911441943)
      ·
        refine ⟨443529981863587093367162915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295686654575724728911441943 443529981863587093367162915)
        ·
          refine ⟨665294972795380640050744373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443529981863587093367162915 665294972795380640050744373)
          ·
            refine ⟨62371403699566935004757285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 665294972795380640050744373 62371403699566935004757285)
            ·
              refine ⟨11694638193668800313391991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62371403699566935004757285 11694638193668800313391991)
              ·
                refine ⟨17541957290503200470087987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11694638193668800313391991 17541957290503200470087987)
                ·
                  refine ⟨26312935935754800705131981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17541957290503200470087987 26312935935754800705131981)
                  ·
                    refine ⟨9867350975908050264424493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26312935935754800705131981 9867350975908050264424493)
                    ·
                      refine ⟨3700256615965518849159185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9867350975908050264424493 3700256615965518849159185)
                      ·
                        rfl

theorem cell23_7206224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 3].length) (baseStart_7206224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206224 prefixEnd_7206224 := by exact prefixLift 7206224
  have htrace : WordTrace (prefixWord ++ tailWord_7206224) baseStart_7206224 baseEnd_7206224 := by
    simpa [prefixWord, tailWord_7206224, baseEnd_7206224] using wordTrace_append hprefix tailTrace_7206224
  have hstable : (prefixWord ++ tailWord_7206224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206224).length < 2 ^ (prefixWord ++ tailWord_7206224).sum := by decide
  have hdescent : baseEnd_7206224 < baseStart_7206224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206257 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 2, 6]
def baseStart_7206257 : Nat := 118140960795 + 7206257 * 2 ^ 59
def prefixEnd_7206257 : Nat := 4983230072969 + 3 ^ 40 * 7206257 * 2
def baseEnd_7206257 : Nat := 1233424520275705740015511

theorem tailTrace_7206257 : CollatzResearch.WordTrace tailWord_7206257 prefixEnd_7206257 1233424520275705740015511 := by
  unfold tailWord_7206257
  simp only [CollatzResearch.WordTrace]
  refine ⟨262833785453969094557233025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175222523635979396371488683 262833785453969094557233025)
  ·
    refine ⟨197125339090476820917924769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262833785453969094557233025 197125339090476820917924769)
    ·
      refine ⟨147844004317857615688443577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197125339090476820917924769 147844004317857615688443577)
      ·
        refine ⟨110883003238393211766332683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147844004317857615688443577 110883003238393211766332683)
        ·
          refine ⟨166324504857589817649499025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110883003238393211766332683 166324504857589817649499025)
          ·
            refine ⟨124743378643192363237124269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166324504857589817649499025 124743378643192363237124269)
            ·
              refine ⟨46778766991197136213921601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124743378643192363237124269 46778766991197136213921601)
              ·
                refine ⟨35084075243397852160441201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46778766991197136213921601 35084075243397852160441201)
                ·
                  refine ⟨26313056432548389120330901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35084075243397852160441201 26313056432548389120330901)
                  ·
                    refine ⟨1233424520275705740015511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26313056432548389120330901 1233424520275705740015511)
                    ·
                      rfl

theorem cell23_7206257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_7206257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206257 prefixEnd_7206257 := by exact prefixLift 7206257
  have htrace : WordTrace (prefixWord ++ tailWord_7206257) baseStart_7206257 baseEnd_7206257 := by
    simpa [prefixWord, tailWord_7206257, baseEnd_7206257] using wordTrace_append hprefix tailTrace_7206257
  have hstable : (prefixWord ++ tailWord_7206257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206257).length < 2 ^ (prefixWord ++ tailWord_7206257).sum := by decide
  have hdescent : baseEnd_7206257 < baseStart_7206257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206334 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_7206334 : Nat := 118140960795 + 7206334 * 2 ^ 59
def prefixEnd_7206334 : Nat := 4983230072969 + 3 ^ 40 * 7206334 * 2
def baseEnd_7206334 : Nat := 1233437699612504472927893

theorem tailTrace_7206334 : CollatzResearch.WordTrace tailWord_7206334 prefixEnd_7206334 1233437699612504472927893 := by
  unfold tailWord_7206334
  simp only [CollatzResearch.WordTrace]
  refine ⟨32854574234336267088473257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175224395916460091138524037 32854574234336267088473257)
  ·
    refine ⟨24640930675752200316354943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32854574234336267088473257 24640930675752200316354943)
    ·
      refine ⟨36961396013628300474532415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24640930675752200316354943 36961396013628300474532415)
      ·
        refine ⟨55442094020442450711798623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36961396013628300474532415 55442094020442450711798623)
        ·
          refine ⟨83163141030663676067697935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55442094020442450711798623 83163141030663676067697935)
          ·
            refine ⟨124744711545995514101546903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83163141030663676067697935 124744711545995514101546903)
            ·
              refine ⟨187117067318993271152320355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124744711545995514101546903 187117067318993271152320355)
              ·
                refine ⟨280675600978489906728480533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187117067318993271152320355 280675600978489906728480533)
                ·
                  refine ⟨13156668795866714377897525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 280675600978489906728480533 13156668795866714377897525)
                  ·
                    refine ⟨1233437699612504472927893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13156668795866714377897525 1233437699612504472927893)
                    ·
                      rfl

theorem cell23_7206334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_7206334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206334 prefixEnd_7206334 := by exact prefixLift 7206334
  have htrace : WordTrace (prefixWord ++ tailWord_7206334) baseStart_7206334 baseEnd_7206334 := by
    simpa [prefixWord, tailWord_7206334, baseEnd_7206334] using wordTrace_append hprefix tailTrace_7206334
  have hstable : (prefixWord ++ tailWord_7206334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206334).length < 2 ^ (prefixWord ++ tailWord_7206334).sum := by decide
  have hdescent : baseEnd_7206334 < baseStart_7206334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206347 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 2, 8]
def baseStart_7206347 : Nat := 118140960795 + 7206347 * 2 ^ 59
def prefixEnd_7206347 : Nat := 4983230072969 + 3 ^ 40 * 7206347 * 2
def baseEnd_7206347 : Nat := 1233439924695340622640373

theorem tailTrace_7206347 : CollatzResearch.WordTrace tailWord_7206347 prefixEnd_7206347 1233439924695340622640373 := by
  unfold tailWord_7206347
  simp only [CollatzResearch.WordTrace]
  refine ⟨262837068023643039928009295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175224712015762026618672863 262837068023643039928009295)
  ·
    refine ⟨394255602035464559892013943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262837068023643039928009295 394255602035464559892013943)
    ·
      refine ⟨591383403053196839838020915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394255602035464559892013943 591383403053196839838020915)
      ·
        refine ⟨887075104579795259757031373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591383403053196839838020915 887075104579795259757031373)
        ·
          refine ⟨332653164217423222408886765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 887075104579795259757031373 332653164217423222408886765)
          ·
            refine ⟨124744936581533708403332537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332653164217423222408886765 124744936581533708403332537)
            ·
              refine ⟨93558702436150281302499403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124744936581533708403332537 93558702436150281302499403)
              ·
                refine ⟨140338053654225421953749105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93558702436150281302499403 140338053654225421953749105)
                ·
                  refine ⟨105253540240669066465311829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140338053654225421953749105 105253540240669066465311829)
                  ·
                    refine ⟨1233439924695340622640373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105253540240669066465311829 1233439924695340622640373)
                    ·
                      rfl

theorem cell23_7206347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 8].length) (baseStart_7206347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206347 prefixEnd_7206347 := by exact prefixLift 7206347
  have htrace : WordTrace (prefixWord ++ tailWord_7206347) baseStart_7206347 baseEnd_7206347 := by
    simpa [prefixWord, tailWord_7206347, baseEnd_7206347] using wordTrace_append hprefix tailTrace_7206347
  have hstable : (prefixWord ++ tailWord_7206347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206347).length < 2 ^ (prefixWord ++ tailWord_7206347).sum := by decide
  have hdescent : baseEnd_7206347 < baseStart_7206347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206371 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 4]
def baseStart_7206371 : Nat := 118140960795 + 7206371 * 2 ^ 59
def prefixEnd_7206371 : Nat := 4983230072969 + 3 ^ 40 * 7206371 * 2
def baseEnd_7206371 : Nat := 3700332097621729774021009

theorem tailTrace_7206371 : CollatzResearch.WordTrace tailWord_7206371 prefixEnd_7206371 3700332097621729774021009 := by
  unfold tailWord_7206371
  simp only [CollatzResearch.WordTrace]
  refine ⟨262837943375556092026882967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175225295583704061351255311 262837943375556092026882967)
  ·
    refine ⟨394256915063334138040324451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262837943375556092026882967 394256915063334138040324451)
    ·
      refine ⟨591385372595001207060486677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394256915063334138040324451 591385372595001207060486677)
      ·
        refine ⟨27721189340390681580960313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 591385372595001207060486677 27721189340390681580960313)
        ·
          refine ⟨20790892005293011185720235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27721189340390681580960313 20790892005293011185720235)
          ·
            refine ⟨31186338007939516778580353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20790892005293011185720235 31186338007939516778580353)
            ·
              refine ⟨23389753505954637583935265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31186338007939516778580353 23389753505954637583935265)
              ·
                refine ⟨17542315129465978187951449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23389753505954637583935265 17542315129465978187951449)
                ·
                  refine ⟨13156736347099483640963587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17542315129465978187951449 13156736347099483640963587)
                  ·
                    refine ⟨19735104520649225461445381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13156736347099483640963587 19735104520649225461445381)
                    ·
                      refine ⟨3700332097621729774021009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19735104520649225461445381 3700332097621729774021009)
                      ·
                        rfl

theorem cell23_7206371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_7206371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206371 prefixEnd_7206371 := by exact prefixLift 7206371
  have htrace : WordTrace (prefixWord ++ tailWord_7206371) baseStart_7206371 baseEnd_7206371 := by
    simpa [prefixWord, tailWord_7206371, baseEnd_7206371] using wordTrace_append hprefix tailTrace_7206371
  have hstable : (prefixWord ++ tailWord_7206371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206371).length < 2 ^ (prefixWord ++ tailWord_7206371).sum := by decide
  have hdescent : baseEnd_7206371 < baseStart_7206371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206377 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 12]
def baseStart_7206377 : Nat := 118140960795 + 7206377 * 2 ^ 59
def prefixEnd_7206377 : Nat := 4983230072969 + 3 ^ 40 * 7206377 * 2
def baseEnd_7206377 : Nat := 411148353167295194505109

theorem tailTrace_7206377 : CollatzResearch.WordTrace tailWord_7206377 prefixEnd_7206377 411148353167295194505109 := by
  unfold tailWord_7206377
  simp only [CollatzResearch.WordTrace]
  refine ⟨262838162213534355051601385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175225441475689570034400923 262838162213534355051601385)
  ·
    refine ⟨197128621660150766288701039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262838162213534355051601385 197128621660150766288701039)
    ·
      refine ⟨295692932490226149433051559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197128621660150766288701039 295692932490226149433051559)
      ·
        refine ⟨443539398735339224149577339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295692932490226149433051559 443539398735339224149577339)
        ·
          refine ⟨665309098103008836224366009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443539398735339224149577339 665309098103008836224366009)
          ·
            refine ⟨498981823577256627168274507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665309098103008836224366009 498981823577256627168274507)
            ·
              refine ⟨748472735365884940752411761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498981823577256627168274507 748472735365884940752411761)
              ·
                refine ⟨561354551524413705564308821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748472735365884940752411761 561354551524413705564308821)
                ·
                  refine ⟨411148353167295194505109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 561354551524413705564308821 411148353167295194505109)
                  ·
                    rfl

theorem cell23_7206377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 12].length) (baseStart_7206377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206377 prefixEnd_7206377 := by exact prefixLift 7206377
  have htrace : WordTrace (prefixWord ++ tailWord_7206377) baseStart_7206377 baseEnd_7206377 := by
    simpa [prefixWord, tailWord_7206377, baseEnd_7206377] using wordTrace_append hprefix tailTrace_7206377
  have hstable : (prefixWord ++ tailWord_7206377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206377).length < 2 ^ (prefixWord ++ tailWord_7206377).sum := by decide
  have hdescent : baseEnd_7206377 < baseStart_7206377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206394 : List Nat := [3, 1, 1, 1, 1, 2, 3, 5, 6]
def baseStart_7206394 : Nat := 118140960795 + 7206394 * 2 ^ 59
def prefixEnd_7206394 : Nat := 4983230072969 + 3 ^ 40 * 7206394 * 2
def baseEnd_7206394 : Nat := 411149323075198131559267

theorem tailTrace_7206394 : CollatzResearch.WordTrace tailWord_7206394 prefixEnd_7206394 411149323075198131559267 := by
  unfold tailWord_7206394
  simp only [CollatzResearch.WordTrace]
  refine ⟨65709695563618191738742559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175225854836315177969980157 65709695563618191738742559)
  ·
    refine ⟨98564543345427287608113839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65709695563618191738742559 98564543345427287608113839)
    ·
      refine ⟨147846815018140931412170759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98564543345427287608113839 147846815018140931412170759)
      ·
        refine ⟨221770222527211397118256139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147846815018140931412170759 221770222527211397118256139)
        ·
          refine ⟨332655333790817095677384209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221770222527211397118256139 332655333790817095677384209)
          ·
            refine ⟨249491500343112821758038157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332655333790817095677384209 249491500343112821758038157)
            ·
              refine ⟨93559312628667308159264309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249491500343112821758038157 93559312628667308159264309)
              ·
                refine ⟨8771185558937560139931029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93559312628667308159264309 8771185558937560139931029)
                ·
                  refine ⟨411149323075198131559267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8771185558937560139931029 411149323075198131559267)
                  ·
                    rfl

theorem cell23_7206394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_7206394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206394 prefixEnd_7206394 := by exact prefixLift 7206394
  have htrace : WordTrace (prefixWord ++ tailWord_7206394) baseStart_7206394 baseEnd_7206394 := by
    simpa [prefixWord, tailWord_7206394, baseEnd_7206394] using wordTrace_append hprefix tailTrace_7206394
  have hstable : (prefixWord ++ tailWord_7206394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206394).length < 2 ^ (prefixWord ++ tailWord_7206394).sum := by decide
  have hdescent : baseEnd_7206394 < baseStart_7206394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206464 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 5]
def baseStart_7206464 : Nat := 118140960795 + 7206464 * 2 ^ 59
def prefixEnd_7206464 : Nat := 4983230072969 + 3 ^ 40 * 7206464 * 2
def baseEnd_7206464 : Nat := 3700379851322597910158081

theorem tailTrace_7206464 : CollatzResearch.WordTrace tailWord_7206464 prefixEnd_7206464 3700379851322597910158081 := by
  unfold tailWord_7206464
  simp only [CollatzResearch.WordTrace]
  refine ⟨131420667682109584455009223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175227556909479445940012297 131420667682109584455009223)
  ·
    refine ⟨197131001523164376682513835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131420667682109584455009223 197131001523164376682513835)
    ·
      refine ⟨295696502284746565023770753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197131001523164376682513835 295696502284746565023770753)
      ·
        refine ⟨221772376713559923767828065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295696502284746565023770753 221772376713559923767828065)
        ·
          refine ⟨166329282535169942825871049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221772376713559923767828065 166329282535169942825871049)
          ·
            refine ⟨124746961901377457119403287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166329282535169942825871049 124746961901377457119403287)
            ·
              refine ⟨187120442852066185679104931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124746961901377457119403287 187120442852066185679104931)
              ·
                refine ⟨280680664278099278518657397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187120442852066185679104931 280680664278099278518657397)
                ·
                  refine ⟨26313812276071807361124131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 280680664278099278518657397 26313812276071807361124131)
                  ·
                    refine ⟨39470718414107711041686197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26313812276071807361124131 39470718414107711041686197)
                    ·
                      refine ⟨3700379851322597910158081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39470718414107711041686197 3700379851322597910158081)
                      ·
                        rfl

theorem cell23_7206464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_7206464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206464 prefixEnd_7206464 := by exact prefixLift 7206464
  have htrace : WordTrace (prefixWord ++ tailWord_7206464) baseStart_7206464 baseEnd_7206464 := by
    simpa [prefixWord, tailWord_7206464, baseEnd_7206464] using wordTrace_append hprefix tailTrace_7206464
  have hstable : (prefixWord ++ tailWord_7206464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206464).length < 2 ^ (prefixWord ++ tailWord_7206464).sum := by decide
  have hdescent : baseEnd_7206464 < baseStart_7206464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206481 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 5]
def baseStart_7206481 : Nat := 118140960795 + 7206481 * 2 ^ 59
def prefixEnd_7206481 : Nat := 4983230072969 + 3 ^ 40 * 7206481 * 2
def baseEnd_7206481 : Nat := 3700388580493724343645503

theorem tailTrace_7206481 : CollatzResearch.WordTrace tailWord_7206481 prefixEnd_7206481 3700388580493724343645503 := by
  unfold tailWord_7206481
  simp only [CollatzResearch.WordTrace]
  refine ⟨262841955405157580813387297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175227970270105053875591531 262841955405157580813387297)
  ·
    refine ⟨197131466553868185610040473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262841955405157580813387297 197131466553868185610040473)
    ·
      refine ⟨147848599915401139207530355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197131466553868185610040473 147848599915401139207530355)
      ·
        refine ⟨221772899873101708811295533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147848599915401139207530355 221772899873101708811295533)
        ·
          refine ⟨83164837452413140804235825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221772899873101708811295533 83164837452413140804235825)
          ·
            refine ⟨62373628089309855603176869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83164837452413140804235825 62373628089309855603176869)
            ·
              refine ⟨11695055266745597925595663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62373628089309855603176869 11695055266745597925595663)
              ·
                refine ⟨17542582900118396888393495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11695055266745597925595663 17542582900118396888393495)
                ·
                  refine ⟨26313874350177595332590243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17542582900118396888393495 26313874350177595332590243)
                  ·
                    refine ⟨39470811525266392998885365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26313874350177595332590243 39470811525266392998885365)
                    ·
                      refine ⟨3700388580493724343645503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39470811525266392998885365 3700388580493724343645503)
                      ·
                        rfl

theorem cell23_7206481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_7206481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206481 prefixEnd_7206481 := by exact prefixLift 7206481
  have htrace : WordTrace (prefixWord ++ tailWord_7206481) baseStart_7206481 baseEnd_7206481 := by
    simpa [prefixWord, tailWord_7206481, baseEnd_7206481] using wordTrace_append hprefix tailTrace_7206481
  have hstable : (prefixWord ++ tailWord_7206481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206481).length < 2 ^ (prefixWord ++ tailWord_7206481).sum := by decide
  have hdescent : baseEnd_7206481 < baseStart_7206481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206501 : List Nat := [1, 3, 1, 3, 3, 2, 2, 8]
def baseStart_7206501 : Nat := 118140960795 + 7206501 * 2 ^ 59
def prefixEnd_7206501 : Nat := 4983230072969 + 3 ^ 40 * 7206501 * 2
def baseEnd_7206501 : Nat := 137051809263215343162793

theorem tailTrace_7206501 : CollatzResearch.WordTrace tailWord_7206501 prefixEnd_7206501 137051809263215343162793 := by
  unfold tailWord_7206501
  simp only [CollatzResearch.WordTrace]
  refine ⟨262842684865085124229115357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175228456576723416152743571 262842684865085124229115357)
  ·
    refine ⟨98566006824406921585918259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262842684865085124229115357 98566006824406921585918259)
    ·
      refine ⟨147849010236610382378877389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98566006824406921585918259 147849010236610382378877389)
      ·
        refine ⟨55443378838728893392079021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147849010236610382378877389 55443378838728893392079021)
        ·
          refine ⟨20791267064523335022029633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55443378838728893392079021 20791267064523335022029633)
          ·
            refine ⟨15593450298392501266522225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20791267064523335022029633 15593450298392501266522225)
            ·
              refine ⟨11695087723794375949891669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15593450298392501266522225 11695087723794375949891669)
              ·
                refine ⟨137051809263215343162793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11695087723794375949891669 137051809263215343162793)
                ·
                  rfl

theorem cell23_7206501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 8].length) (baseStart_7206501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206501 prefixEnd_7206501 := by exact prefixLift 7206501
  have htrace : WordTrace (prefixWord ++ tailWord_7206501) baseStart_7206501 baseEnd_7206501 := by
    simpa [prefixWord, tailWord_7206501, baseEnd_7206501] using wordTrace_append hprefix tailTrace_7206501
  have hstable : (prefixWord ++ tailWord_7206501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206501).length < 2 ^ (prefixWord ++ tailWord_7206501).sum := by decide
  have hdescent : baseEnd_7206501 < baseStart_7206501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206511 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 3]
def baseStart_7206511 : Nat := 118140960795 + 7206511 * 2 ^ 59
def prefixEnd_7206511 : Nat := 4983230072969 + 3 ^ 40 * 7206511 * 2
def baseEnd_7206511 : Nat := 3700403984913359226270365

theorem tailTrace_7206511 : CollatzResearch.WordTrace tailWord_7206511 prefixEnd_7206511 3700403984913359226270365 := by
  unfold tailWord_7206511
  simp only [CollatzResearch.WordTrace]
  refine ⟨262843049595048895936979387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175228699730032597291319591 262843049595048895936979387)
  ·
    refine ⟨394264574392573343905469081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262843049595048895936979387 394264574392573343905469081)
    ·
      refine ⟨295698430794430007929101811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394264574392573343905469081 295698430794430007929101811)
      ·
        refine ⟨443547646191645011893652717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295698430794430007929101811 443547646191645011893652717)
        ·
          refine ⟨166330367321866879460119769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443547646191645011893652717 166330367321866879460119769)
          ·
            refine ⟨124747775491400159595089827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166330367321866879460119769 124747775491400159595089827)
            ·
              refine ⟨187121663237100239392634741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124747775491400159595089827 187121663237100239392634741)
              ·
                refine ⟨17542655928478147443059507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187121663237100239392634741 17542655928478147443059507)
                ·
                  refine ⟨26313983892717221164589261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17542655928478147443059507 26313983892717221164589261)
                  ·
                    refine ⟨9867743959768957936720973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26313983892717221164589261 9867743959768957936720973)
                    ·
                      refine ⟨3700403984913359226270365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9867743959768957936720973 3700403984913359226270365)
                      ·
                        rfl

theorem cell23_7206511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 3].length) (baseStart_7206511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206511 prefixEnd_7206511 := by exact prefixLift 7206511
  have htrace : WordTrace (prefixWord ++ tailWord_7206511) baseStart_7206511 baseEnd_7206511 := by
    simpa [prefixWord, tailWord_7206511, baseEnd_7206511] using wordTrace_append hprefix tailTrace_7206511
  have hstable : (prefixWord ++ tailWord_7206511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206511).length < 2 ^ (prefixWord ++ tailWord_7206511).sum := by decide
  have hdescent : baseEnd_7206511 < baseStart_7206511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206532 : List Nat := [2, 3, 2, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_7206532 : Nat := 118140960795 + 7206532 * 2 ^ 59
def prefixEnd_7206532 : Nat := 4983230072969 + 3 ^ 40 * 7206532 * 2
def baseEnd_7206532 : Nat := 3700414768007103644107769

theorem tailTrace_7206532 : CollatzResearch.WordTrace tailWord_7206532 prefixEnd_7206532 3700414768007103644107769 := by
  unfold tailWord_7206532
  simp only [CollatzResearch.WordTrace]
  refine ⟨131421907763986408261746925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175229210351981877682329233 131421907763986408261746925)
  ·
    refine ⟨49283215411494903098155097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131421907763986408261746925 49283215411494903098155097)
    ·
      refine ⟨36962411558621177323616323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49283215411494903098155097 36962411558621177323616323)
      ·
        refine ⟨55443617337931765985424485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36962411558621177323616323 55443617337931765985424485)
        ·
          refine ⟨10395678250862206122267091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55443617337931765985424485 10395678250862206122267091)
          ·
            refine ⟨15593517376293309183400637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10395678250862206122267091 15593517376293309183400637)
            ·
              refine ⟨5847569016109990943775239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15593517376293309183400637 5847569016109990943775239)
              ·
                refine ⟨8771353524164986415662859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5847569016109990943775239 8771353524164986415662859)
                ·
                  refine ⟨13157030286247479623494289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8771353524164986415662859 13157030286247479623494289)
                  ·
                    refine ⟨9867772714685609717620717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13157030286247479623494289 9867772714685609717620717)
                    ·
                      refine ⟨3700414768007103644107769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9867772714685609717620717 3700414768007103644107769)
                      ·
                        rfl

theorem cell23_7206532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_7206532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206532 prefixEnd_7206532 := by exact prefixLift 7206532
  have htrace : WordTrace (prefixWord ++ tailWord_7206532) baseStart_7206532 baseEnd_7206532 := by
    simpa [prefixWord, tailWord_7206532, baseEnd_7206532] using wordTrace_append hprefix tailTrace_7206532
  have hstable : (prefixWord ++ tailWord_7206532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206532).length < 2 ^ (prefixWord ++ tailWord_7206532).sum := by decide
  have hdescent : baseEnd_7206532 < baseStart_7206532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206544 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 3, 8]
def baseStart_7206544 : Nat := 118140960795 + 7206544 * 2 ^ 59
def prefixEnd_7206544 : Nat := 4983230072969 + 3 ^ 40 * 7206544 * 2
def baseEnd_7206544 : Nat := 1233473643258319199052571

theorem tailTrace_7206544 : CollatzResearch.WordTrace tailWord_7206544 prefixEnd_7206544 1233473643258319199052571 := by
  unfold tailWord_7206544
  simp only [CollatzResearch.WordTrace]
  refine ⟨131422126601964671286465343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175229502135952895048620457 131422126601964671286465343)
  ·
    refine ⟨197133189902947006929698015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131422126601964671286465343 197133189902947006929698015)
    ·
      refine ⟨295699784854420510394547023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197133189902947006929698015 295699784854420510394547023)
      ·
        refine ⟨443549677281630765591820535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295699784854420510394547023 443549677281630765591820535)
        ·
          refine ⟨665324515922446148387730803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443549677281630765591820535 665324515922446148387730803)
          ·
            refine ⟨997986773883669222581596205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665324515922446148387730803 997986773883669222581596205)
            ·
              refine ⟨374245040206375958468098577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 997986773883669222581596205 374245040206375958468098577)
              ·
                refine ⟨280683780154781968851073933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374245040206375958468098577 280683780154781968851073933)
                ·
                  refine ⟨105256417558043238319152725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 280683780154781968851073933 105256417558043238319152725)
                  ·
                    refine ⟨1233473643258319199052571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105256417558043238319152725 1233473643258319199052571)
                    ·
                      rfl

theorem cell23_7206544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_7206544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206544 prefixEnd_7206544 := by exact prefixLift 7206544
  have htrace : WordTrace (prefixWord ++ tailWord_7206544) baseStart_7206544 baseEnd_7206544 := by
    simpa [prefixWord, tailWord_7206544, baseEnd_7206544] using wordTrace_append hprefix tailTrace_7206544
  have hstable : (prefixWord ++ tailWord_7206544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206544).length < 2 ^ (prefixWord ++ tailWord_7206544).sum := by decide
  have hdescent : baseEnd_7206544 < baseStart_7206544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206551 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_7206551 : Nat := 118140960795 + 7206551 * 2 ^ 59
def prefixEnd_7206551 : Nat := 4983230072969 + 3 ^ 40 * 7206551 * 2
def baseEnd_7206551 : Nat := 3700424524139539069770181

theorem tailTrace_7206551 : CollatzResearch.WordTrace tailWord_7206551 prefixEnd_7206551 3700424524139539069770181 := by
  unfold tailWord_7206551
  simp only [CollatzResearch.WordTrace]
  refine ⟨262844508514903982768435507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175229672343269321845623671 262844508514903982768435507)
  ·
    refine ⟨394266762772355974152653261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262844508514903982768435507 394266762772355974152653261)
    ·
      refine ⟨147850036039633490307244973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394266762772355974152653261 147850036039633490307244973)
      ·
        refine ⟨55443763514862558865216865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147850036039633490307244973 55443763514862558865216865)
        ·
          refine ⟨41582822636146919148912649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55443763514862558865216865 41582822636146919148912649)
          ·
            refine ⟨31187116977110189361684487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41582822636146919148912649 31187116977110189361684487)
            ·
              refine ⟨46780675465665284042526731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31187116977110189361684487 46780675465665284042526731)
              ·
                refine ⟨70171013198497926063790097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46780675465665284042526731 70171013198497926063790097)
                ·
                  refine ⟨52628259898873444547842573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70171013198497926063790097 52628259898873444547842573)
                  ·
                    refine ⟨19735597462077541705440965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52628259898873444547842573 19735597462077541705440965)
                    ·
                      refine ⟨3700424524139539069770181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19735597462077541705440965 3700424524139539069770181)
                      ·
                        rfl

theorem cell23_7206551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_7206551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206551 prefixEnd_7206551 := by exact prefixLift 7206551
  have htrace : WordTrace (prefixWord ++ tailWord_7206551) baseStart_7206551 baseEnd_7206551 := by
    simpa [prefixWord, tailWord_7206551, baseEnd_7206551] using wordTrace_append hprefix tailTrace_7206551
  have hstable : (prefixWord ++ tailWord_7206551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206551).length < 2 ^ (prefixWord ++ tailWord_7206551).sum := by decide
  have hdescent : baseEnd_7206551 < baseStart_7206551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206561 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 1, 8]
def baseStart_7206561 : Nat := 118140960795 + 7206561 * 2 ^ 59
def prefixEnd_7206561 : Nat := 4983230072969 + 3 ^ 40 * 7206561 * 2
def baseEnd_7206561 : Nat := 1233476552982028010215045

theorem tailTrace_7206561 : CollatzResearch.WordTrace tailWord_7206561 prefixEnd_7206561 1233476552982028010215045 := by
  unfold tailWord_7206561
  simp only [CollatzResearch.WordTrace]
  refine ⟨262844873244867754476299537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175229915496578502984199691 262844873244867754476299537)
  ·
    refine ⟨197133654933650815857224653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262844873244867754476299537 197133654933650815857224653)
    ·
      refine ⟨73925120600119055946459245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197133654933650815857224653 73925120600119055946459245)
      ·
        refine ⟨27721920225044645979922217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73925120600119055946459245 27721920225044645979922217)
        ·
          refine ⟨20791440168783484484941663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27721920225044645979922217 20791440168783484484941663)
          ·
            refine ⟨31187160253175226727412495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20791440168783484484941663 31187160253175226727412495)
            ·
              refine ⟨46780740379762840091118743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31187160253175226727412495 46780740379762840091118743)
              ·
                refine ⟨70171110569644260136678115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46780740379762840091118743 70171110569644260136678115)
                ·
                  refine ⟨105256665854466390205017173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70171110569644260136678115 105256665854466390205017173)
                  ·
                    refine ⟨1233476552982028010215045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105256665854466390205017173 1233476552982028010215045)
                    ·
                      rfl

theorem cell23_7206561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_7206561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206561 prefixEnd_7206561 := by exact prefixLift 7206561
  have htrace : WordTrace (prefixWord ++ tailWord_7206561) baseStart_7206561 baseEnd_7206561 := by
    simpa [prefixWord, tailWord_7206561, baseEnd_7206561] using wordTrace_append hprefix tailTrace_7206561
  have hstable : (prefixWord ++ tailWord_7206561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206561).length < 2 ^ (prefixWord ++ tailWord_7206561).sum := by decide
  have hdescent : baseEnd_7206561 < baseStart_7206561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206562 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_7206562 : Nat := 118140960795 + 7206562 * 2 ^ 59
def prefixEnd_7206562 : Nat := 4983230072969 + 3 ^ 40 * 7206562 * 2
def baseEnd_7206562 : Nat := 3700430172426738526732631

theorem tailTrace_7206562 : CollatzResearch.WordTrace tailWord_7206562 prefixEnd_7206562 3700430172426738526732631 := by
  unfold tailWord_7206562
  simp only [CollatzResearch.WordTrace]
  refine ⟨65711227429466032911771485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175229939811909421098057293 65711227429466032911771485)
  ·
    refine ⟨24641710286049762341914307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65711227429466032911771485 24641710286049762341914307)
    ·
      refine ⟨36962565429074643512871461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24641710286049762341914307 36962565429074643512871461)
      ·
        refine ⟨6930481017951495658663399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36962565429074643512871461 6930481017951495658663399)
        ·
          refine ⟨10395721526927243487995099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6930481017951495658663399 10395721526927243487995099)
          ·
            refine ⟨15593582290390865231992649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10395721526927243487995099 15593582290390865231992649)
            ·
              refine ⟨11695186717793148923994487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15593582290390865231992649 11695186717793148923994487)
              ·
                refine ⟨17542780076689723385991731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11695186717793148923994487 17542780076689723385991731)
                ·
                  refine ⟨26314170115034585078987597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17542780076689723385991731 26314170115034585078987597)
                  ·
                    refine ⟨9867813793137969404620349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26314170115034585078987597 9867813793137969404620349)
                    ·
                      refine ⟨3700430172426738526732631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9867813793137969404620349 3700430172426738526732631)
                      ·
                        rfl

theorem cell23_7206562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_7206562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206562 prefixEnd_7206562 := by exact prefixLift 7206562
  have htrace : WordTrace (prefixWord ++ tailWord_7206562) baseStart_7206562 baseEnd_7206562 := by
    simpa [prefixWord, tailWord_7206562, baseEnd_7206562] using wordTrace_append hprefix tailTrace_7206562
  have hstable : (prefixWord ++ tailWord_7206562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206562).length < 2 ^ (prefixWord ++ tailWord_7206562).sum := by decide
  have hdescent : baseEnd_7206562 < baseStart_7206562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206602 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 4, 2, 2]
def baseStart_7206602 : Nat := 118140960795 + 7206602 * 2 ^ 59
def prefixEnd_7206602 : Nat := 4983230072969 + 3 ^ 40 * 7206602 * 2
def baseEnd_7206602 : Nat := 3700450711652918370232447

theorem tailTrace_7206602 : CollatzResearch.WordTrace tailWord_7206602 prefixEnd_7206602 3700450711652918370232447 := by
  unfold tailWord_7206602
  simp only [CollatzResearch.WordTrace]
  refine ⟨65711592159429804619635515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175230912425146145652361373 65711592159429804619635515)
  ·
    refine ⟨98567388239144706929453273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65711592159429804619635515 98567388239144706929453273)
    ·
      refine ⟨73925541179358530197089955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98567388239144706929453273 73925541179358530197089955)
      ·
        refine ⟨110888311769037795295634933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73925541179358530197089955 110888311769037795295634933)
        ·
          refine ⟨10395779228347293308965775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110888311769037795295634933 10395779228347293308965775)
          ·
            refine ⟨15593668842520939963448663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10395779228347293308965775 15593668842520939963448663)
            ·
              refine ⟨23390503263781409945172995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15593668842520939963448663 23390503263781409945172995)
              ·
                refine ⟨35085754895672114917759493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23390503263781409945172995 35085754895672114917759493)
                ·
                  refine ⟨6578579042938521547079905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35085754895672114917759493 6578579042938521547079905)
                  ·
                    refine ⟨4933934282203891160309929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6578579042938521547079905 4933934282203891160309929)
                    ·
                      refine ⟨3700450711652918370232447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4933934282203891160309929 3700450711652918370232447)
                      ·
                        rfl

theorem cell23_7206602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_7206602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206602 prefixEnd_7206602 := by exact prefixLift 7206602
  have htrace : WordTrace (prefixWord ++ tailWord_7206602) baseStart_7206602 baseEnd_7206602 := by
    simpa [prefixWord, tailWord_7206602, baseEnd_7206602] using wordTrace_append hprefix tailTrace_7206602
  have hstable : (prefixWord ++ tailWord_7206602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206602).length < 2 ^ (prefixWord ++ tailWord_7206602).sum := by decide
  have hdescent : baseEnd_7206602 < baseStart_7206602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206618 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3]
def baseStart_7206618 : Nat := 118140960795 + 7206618 * 2 ^ 59
def prefixEnd_7206618 : Nat := 4983230072969 + 3 ^ 40 * 7206618 * 2
def baseEnd_7206618 : Nat := 3700458927343390307632373

theorem tailTrace_7206618 : CollatzResearch.WordTrace tailWord_7206618 prefixEnd_7206618 3700458927343390307632373 := by
  unfold tailWord_7206618
  simp only [CollatzResearch.WordTrace]
  refine ⟨65711738051415313302781127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175231301470440835474083005 65711738051415313302781127)
  ·
    refine ⟨98567607077122969954171691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65711738051415313302781127 98567607077122969954171691)
    ·
      refine ⟨147851410615684454931257537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98567607077122969954171691 147851410615684454931257537)
      ·
        refine ⟨110888557961763341198443153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147851410615684454931257537 110888557961763341198443153)
        ·
          refine ⟨83166418471322505898832365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110888557961763341198443153 83166418471322505898832365)
          ·
            refine ⟨31187406926745939712062137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83166418471322505898832365 31187406926745939712062137)
            ·
              refine ⟨23390555195059454784046603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31187406926745939712062137 23390555195059454784046603)
              ·
                refine ⟨35085832792589182176069905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23390555195059454784046603 35085832792589182176069905)
                ·
                  refine ⟨26314374594441886632052429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35085832792589182176069905 26314374594441886632052429)
                  ·
                    refine ⟨9867890472915707487019661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26314374594441886632052429 9867890472915707487019661)
                    ·
                      refine ⟨3700458927343390307632373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9867890472915707487019661 3700458927343390307632373)
                      ·
                        rfl

theorem cell23_7206618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_7206618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206618 prefixEnd_7206618 := by exact prefixLift 7206618
  have htrace : WordTrace (prefixWord ++ tailWord_7206618) baseStart_7206618 baseEnd_7206618 := by
    simpa [prefixWord, tailWord_7206618, baseEnd_7206618] using wordTrace_append hprefix tailTrace_7206618
  have hstable : (prefixWord ++ tailWord_7206618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206618).length < 2 ^ (prefixWord ++ tailWord_7206618).sum := by decide
  have hdescent : baseEnd_7206618 < baseStart_7206618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206638 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_7206638 : Nat := 118140960795 + 7206638 * 2 ^ 59
def prefixEnd_7206638 : Nat := 4983230072969 + 3 ^ 40 * 7206638 * 2
def baseEnd_7206638 : Nat := 1233489732318826743127427

theorem tailTrace_7206638 : CollatzResearch.WordTrace tailWord_7206638 prefixEnd_7206638 1233489732318826743127427 := by
  unfold tailWord_7206638
  simp only [CollatzResearch.WordTrace]
  refine ⟨32855960208198599578356571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175231787777059197751235045 32855960208198599578356571)
  ·
    refine ⟨49283940312297899367534857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32855960208198599578356571 49283940312297899367534857)
    ·
      refine ⟨36962955234223424525651143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49283940312297899367534857 36962955234223424525651143)
      ·
        refine ⟨55444432851335136788476715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36962955234223424525651143 55444432851335136788476715)
        ·
          refine ⟨83166649277002705182715073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55444432851335136788476715 83166649277002705182715073)
          ·
            refine ⟨62374986957752028887036305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83166649277002705182715073 62374986957752028887036305)
            ·
              refine ⟨46781240218314021665277229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62374986957752028887036305 46781240218314021665277229)
              ·
                refine ⟨17542965081867758124478961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46781240218314021665277229 17542965081867758124478961)
                ·
                  refine ⟨13157223811400818593359221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17542965081867758124478961 13157223811400818593359221)
                  ·
                    refine ⟨1233489732318826743127427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13157223811400818593359221 1233489732318826743127427)
                    ·
                      rfl

theorem cell23_7206638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_7206638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206638 prefixEnd_7206638 := by exact prefixLift 7206638
  have htrace : WordTrace (prefixWord ++ tailWord_7206638) baseStart_7206638 baseEnd_7206638 := by
    simpa [prefixWord, tailWord_7206638, baseEnd_7206638] using wordTrace_append hprefix tailTrace_7206638
  have hstable : (prefixWord ++ tailWord_7206638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206638).length < 2 ^ (prefixWord ++ tailWord_7206638).sum := by decide
  have hdescent : baseEnd_7206638 < baseStart_7206638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206671 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 4]
def baseStart_7206671 : Nat := 118140960795 + 7206671 * 2 ^ 59
def prefixEnd_7206671 : Nat := 4983230072969 + 3 ^ 40 * 7206671 * 2
def baseEnd_7206671 : Nat := 3700486141818078600269629

theorem tailTrace_7206671 : CollatzResearch.WordTrace tailWord_7206671 prefixEnd_7206671 3700486141818078600269629 := by
  unfold tailWord_7206671
  simp only [CollatzResearch.WordTrace]
  refine ⟨262848885274469243262803867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175232590182979495508535911 262848885274469243262803867)
  ·
    refine ⟨394273327911703864894205801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262848885274469243262803867 394273327911703864894205801)
    ·
      refine ⟨295704995933777898670654351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394273327911703864894205801 295704995933777898670654351)
      ·
        refine ⟨443557493900666848005981527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295704995933777898670654351 443557493900666848005981527)
        ·
          refine ⟨665336240851000272008972291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443557493900666848005981527 665336240851000272008972291)
          ·
            refine ⟨998004361276500408013458437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665336240851000272008972291 998004361276500408013458437)
            ·
              refine ⟨187125817739343826502523457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 998004361276500408013458437 187125817739343826502523457)
              ·
                refine ⟨140344363304507869876892593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187125817739343826502523457 140344363304507869876892593)
                ·
                  refine ⟨105258272478380902407669445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140344363304507869876892593 105258272478380902407669445)
                  ·
                    refine ⟨19735926089696419201438021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105258272478380902407669445 19735926089696419201438021)
                    ·
                      refine ⟨3700486141818078600269629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19735926089696419201438021 3700486141818078600269629)
                      ·
                        rfl

theorem cell23_7206671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_7206671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206671 prefixEnd_7206671 := by exact prefixLift 7206671
  have htrace : WordTrace (prefixWord ++ tailWord_7206671) baseStart_7206671 baseEnd_7206671 := by
    simpa [prefixWord, tailWord_7206671, baseEnd_7206671] using wordTrace_append hprefix tailTrace_7206671
  have hstable : (prefixWord ++ tailWord_7206671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206671).length < 2 ^ (prefixWord ++ tailWord_7206671).sum := by decide
  have hdescent : baseEnd_7206671 < baseStart_7206671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206725 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 3, 1, 3]
def baseStart_7206725 : Nat := 118140960795 + 7206725 * 2 ^ 59
def prefixEnd_7206725 : Nat := 4983230072969 + 3 ^ 40 * 7206725 * 2
def baseEnd_7206725 : Nat := 3700513869773421388994381

theorem tailTrace_7206725 : CollatzResearch.WordTrace tailWord_7206725 prefixEnd_7206725 3700513869773421388994381 := by
  unfold tailWord_7206725
  simp only [CollatzResearch.WordTrace]
  refine ⟨262850854816273610485269629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175233903210849073656846419 262850854816273610485269629)
  ·
    refine ⟨98569070556102603931976111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262850854816273610485269629 98569070556102603931976111)
    ·
      refine ⟨147853605834153905897964167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98569070556102603931976111 147853605834153905897964167)
      ·
        refine ⟨221780408751230858846946251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147853605834153905897964167 221780408751230858846946251)
        ·
          refine ⟨332670613126846288270419377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221780408751230858846946251 332670613126846288270419377)
          ·
            refine ⟨249502959845134716202814533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332670613126846288270419377 249502959845134716202814533)
            ·
              refine ⟨46781804970962759288027725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249502959845134716202814533 46781804970962759288027725)
              ·
                refine ⟨17543176864111034733010397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46781804970962759288027725 17543176864111034733010397)
                ·
                  refine ⟨6578691324041638024878899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17543176864111034733010397 6578691324041638024878899)
                  ·
                    refine ⟨9868036986062457037318349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6578691324041638024878899 9868036986062457037318349)
                    ·
                      refine ⟨3700513869773421388994381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9868036986062457037318349 3700513869773421388994381)
                      ·
                        rfl

theorem cell23_7206725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_7206725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206725 prefixEnd_7206725 := by exact prefixLift 7206725
  have htrace : WordTrace (prefixWord ++ tailWord_7206725) baseStart_7206725 baseEnd_7206725 := by
    simpa [prefixWord, tailWord_7206725, baseEnd_7206725] using wordTrace_append hprefix tailTrace_7206725
  have hstable : (prefixWord ++ tailWord_7206725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206725).length < 2 ^ (prefixWord ++ tailWord_7206725).sum := by decide
  have hdescent : baseEnd_7206725 < baseStart_7206725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206728 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 3, 5]
def baseStart_7206728 : Nat := 118140960795 + 7206728 * 2 ^ 59
def prefixEnd_7206728 : Nat := 4983230072969 + 3 ^ 40 * 7206728 * 2
def baseEnd_7206728 : Nat := 1233505136738461625752289

theorem tailTrace_7206728 : CollatzResearch.WordTrace tailWord_7206728 prefixEnd_7206728 1233505136738461625752289 := by
  unfold tailWord_7206728
  simp only [CollatzResearch.WordTrace]
  refine ⟨131425482117631370998814419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175233976156841827998419225 131425482117631370998814419)
  ·
    refine ⟨197138223176447056498221629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131425482117631370998814419 197138223176447056498221629)
    ·
      refine ⟨73926833691167646186833111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197138223176447056498221629 73926833691167646186833111)
      ·
        refine ⟨110890250536751469280249667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73926833691167646186833111 110890250536751469280249667)
        ·
          refine ⟨166335375805127203920374501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110890250536751469280249667 166335375805127203920374501)
          ·
            refine ⟨31187882963461350735070219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166335375805127203920374501 31187882963461350735070219)
            ·
              refine ⟨46781824445192026102605329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31187882963461350735070219 46781824445192026102605329)
              ·
                refine ⟨35086368333894019576953997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46781824445192026102605329 35086368333894019576953997)
                ·
                  refine ⟨13157388125210257341357749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35086368333894019576953997 13157388125210257341357749)
                  ·
                    refine ⟨1233505136738461625752289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13157388125210257341357749 1233505136738461625752289)
                    ·
                      rfl

theorem cell23_7206728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_7206728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206728 prefixEnd_7206728 := by exact prefixLift 7206728
  have htrace : WordTrace (prefixWord ++ tailWord_7206728) baseStart_7206728 baseEnd_7206728 := by
    simpa [prefixWord, tailWord_7206728, baseEnd_7206728] using wordTrace_append hprefix tailTrace_7206728
  have hstable : (prefixWord ++ tailWord_7206728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206728).length < 2 ^ (prefixWord ++ tailWord_7206728).sum := by decide
  have hdescent : baseEnd_7206728 < baseStart_7206728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206752 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 2, 3, 2]
def baseStart_7206752 : Nat := 118140960795 + 7206752 * 2 ^ 59
def prefixEnd_7206752 : Nat := 4983230072969 + 3 ^ 40 * 7206752 * 2
def baseEnd_7206752 : Nat := 3700527733751092783356757

theorem tailTrace_7206752 : CollatzResearch.WordTrace tailWord_7206752 prefixEnd_7206752 3700527733751092783356757 := by
  unfold tailWord_7206752
  simp only [CollatzResearch.WordTrace]
  refine ⟨131425919793587897048251255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175234559724783862731001673 131425919793587897048251255)
  ·
    refine ⟨197138879690381845572376883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131425919793587897048251255 197138879690381845572376883)
    ·
      refine ⟨295708319535572768358565325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197138879690381845572376883 295708319535572768358565325)
      ·
        refine ⟨110890619825839788134461997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295708319535572768358565325 110890619825839788134461997)
        ·
          refine ⟨41583982434689920550423249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110890619825839788134461997 41583982434689920550423249)
          ·
            refine ⟨31187986826017440412817437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41583982434689920550423249 31187986826017440412817437)
            ·
              refine ⟨11695495059756540154806539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31187986826017440412817437 11695495059756540154806539)
              ·
                refine ⟨17543242589634810232209809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11695495059756540154806539 17543242589634810232209809)
                ·
                  refine ⟨13157431942226107674157357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17543242589634810232209809 13157431942226107674157357)
                  ·
                    refine ⟨4934036978334790377809009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13157431942226107674157357 4934036978334790377809009)
                    ·
                      refine ⟨3700527733751092783356757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4934036978334790377809009 3700527733751092783356757)
                      ·
                        rfl

theorem cell23_7206752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_7206752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206752 prefixEnd_7206752 := by exact prefixLift 7206752
  have htrace : WordTrace (prefixWord ++ tailWord_7206752) baseStart_7206752 baseEnd_7206752 := by
    simpa [prefixWord, tailWord_7206752, baseEnd_7206752] using wordTrace_append hprefix tailTrace_7206752
  have hstable : (prefixWord ++ tailWord_7206752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206752).length < 2 ^ (prefixWord ++ tailWord_7206752).sum := by decide
  have hdescent : baseEnd_7206752 < baseStart_7206752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206759 : List Nat := [1, 1, 5, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_7206759 : Nat := 118140960795 + 7206759 * 2 ^ 59
def prefixEnd_7206759 : Nat := 4983230072969 + 3 ^ 40 * 7206759 * 2
def baseEnd_7206759 : Nat := 3700531328115674255969225

theorem tailTrace_7206759 : CollatzResearch.WordTrace tailWord_7206759 prefixEnd_7206759 3700531328115674255969225 := by
  unfold tailWord_7206759
  simp only [CollatzResearch.WordTrace]
  refine ⟨262852094898150434292007331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175234729932100289528004887 262852094898150434292007331)
  ·
    refine ⟨394278142347225651438010997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262852094898150434292007331 394278142347225651438010997)
    ·
      refine ⟨36963575845052404822313531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 394278142347225651438010997 36963575845052404822313531)
      ·
        refine ⟨55445363767578607233470297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36963575845052404822313531 55445363767578607233470297)
        ·
          refine ⟨41584022825683955425102723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55445363767578607233470297 41584022825683955425102723)
          ·
            refine ⟨62376034238525933137654085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41584022825683955425102723 62376034238525933137654085)
            ·
              refine ⟨11695506419723612463310141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62376034238525933137654085 11695506419723612463310141)
              ·
                refine ⟨4385814907396354673741303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11695506419723612463310141 4385814907396354673741303)
                ·
                  refine ⟨6578722361094532010611955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385814907396354673741303 6578722361094532010611955)
                  ·
                    refine ⟨9868083541641798015917933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6578722361094532010611955 9868083541641798015917933)
                    ·
                      refine ⟨3700531328115674255969225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9868083541641798015917933 3700531328115674255969225)
                      ·
                        rfl

theorem cell23_7206759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_7206759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206759 prefixEnd_7206759 := by exact prefixLift 7206759
  have htrace : WordTrace (prefixWord ++ tailWord_7206759) baseStart_7206759 baseEnd_7206759 := by
    simpa [prefixWord, tailWord_7206759, baseEnd_7206759] using wordTrace_append hprefix tailTrace_7206759
  have hstable : (prefixWord ++ tailWord_7206759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206759).length < 2 ^ (prefixWord ++ tailWord_7206759).sum := by decide
  have hdescent : baseEnd_7206759 < baseStart_7206759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206768 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 5]
def baseStart_7206768 : Nat := 118140960795 + 7206768 * 2 ^ 59
def prefixEnd_7206768 : Nat := 4983230072969 + 3 ^ 40 * 7206768 * 2
def baseEnd_7206768 : Nat := 3700535949441564720756683

theorem tailTrace_7206768 : CollatzResearch.WordTrace tailWord_7206768 prefixEnd_7206768 3700535949441564720756683 := by
  unfold tailWord_7206768
  simp only [CollatzResearch.WordTrace]
  refine ⟨131426211577558914414542479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175234948770078552552723305 131426211577558914414542479)
  ·
    refine ⟨197139317366338371621813719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131426211577558914414542479 197139317366338371621813719)
    ·
      refine ⟨295708976049507557432720579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197139317366338371621813719 295708976049507557432720579)
      ·
        refine ⟨443563464074261336149080869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295708976049507557432720579 443563464074261336149080869)
        ·
          refine ⟨83168149513924000527952663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 443563464074261336149080869 83168149513924000527952663)
          ·
            refine ⟨124752224270886000791928995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83168149513924000527952663 124752224270886000791928995)
            ·
              refine ⟨187128336406329001187893493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124752224270886000791928995 187128336406329001187893493)
              ·
                refine ⟨17543281538093343861365015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187128336406329001187893493 17543281538093343861365015)
                ·
                  refine ⟨26314922307140015792047523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17543281538093343861365015 26314922307140015792047523)
                  ·
                    refine ⟨39472383460710023688071285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26314922307140015792047523 39472383460710023688071285)
                    ·
                      refine ⟨3700535949441564720756683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39472383460710023688071285 3700535949441564720756683)
                      ·
                        rfl

theorem cell23_7206768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_7206768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206768 prefixEnd_7206768 := by exact prefixLift 7206768
  have htrace : WordTrace (prefixWord ++ tailWord_7206768) baseStart_7206768 baseEnd_7206768 := by
    simpa [prefixWord, tailWord_7206768, baseEnd_7206768] using wordTrace_append hprefix tailTrace_7206768
  have hstable : (prefixWord ++ tailWord_7206768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206768).length < 2 ^ (prefixWord ++ tailWord_7206768).sum := by decide
  have hdescent : baseEnd_7206768 < baseStart_7206768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206778 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_7206778 : Nat := 118140960795 + 7206778 * 2 ^ 59
def prefixEnd_7206778 : Nat := 4983230072969 + 3 ^ 40 * 7206778 * 2
def baseEnd_7206778 : Nat := 3700541084248109681631637

theorem tailTrace_7206778 : CollatzResearch.WordTrace tailWord_7206778 prefixEnd_7206778 3700541084248109681631637 := by
  unfold tailWord_7206778
  simp only [CollatzResearch.WordTrace]
  refine ⟨65713196971270400134237247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175235191923387733691299325 65713196971270400134237247)
  ·
    refine ⟨98569795456905600201355871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65713196971270400134237247 98569795456905600201355871)
    ·
      refine ⟨147854693185358400302033807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98569795456905600201355871 147854693185358400302033807)
      ·
        refine ⟨221782039778037600453050711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147854693185358400302033807 221782039778037600453050711)
        ·
          refine ⟨332673059667056400679576067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221782039778037600453050711 332673059667056400679576067)
          ·
            refine ⟨499009589500584601019364101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332673059667056400679576067 499009589500584601019364101)
            ·
              refine ⟨93564298031359612691130769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 499009589500584601019364101 93564298031359612691130769)
              ·
                refine ⟨70173223523519709518348077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93564298031359612691130769 70173223523519709518348077)
                ·
                  refine ⟨26314958821319891069380529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70173223523519709518348077 26314958821319891069380529)
                  ·
                    refine ⟨19736219115989918302035397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26314958821319891069380529 19736219115989918302035397)
                    ·
                      refine ⟨3700541084248109681631637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19736219115989918302035397 3700541084248109681631637)
                      ·
                        rfl

theorem cell23_7206778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_7206778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206778 prefixEnd_7206778 := by exact prefixLift 7206778
  have htrace : WordTrace (prefixWord ++ tailWord_7206778) baseStart_7206778 baseEnd_7206778 := by
    simpa [prefixWord, tailWord_7206778, baseEnd_7206778] using wordTrace_append hprefix tailTrace_7206778
  have hstable : (prefixWord ++ tailWord_7206778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206778).length < 2 ^ (prefixWord ++ tailWord_7206778).sum := by decide
  have hdescent : baseEnd_7206778 < baseStart_7206778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206792 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 1, 6]
def baseStart_7206792 : Nat := 118140960795 + 7206792 * 2 ^ 59
def prefixEnd_7206792 : Nat := 4983230072969 + 3 ^ 40 * 7206792 * 2
def baseEnd_7206792 : Nat := 1233516090992424208952191

theorem tailTrace_7206792 : CollatzResearch.WordTrace tailWord_7206792 prefixEnd_7206792 1233516090992424208952191 := by
  unfold tailWord_7206792
  simp only [CollatzResearch.WordTrace]
  refine ⟨131426649253515440463979315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175235532338020587285305753 131426649253515440463979315)
  ·
    refine ⟨197139973880273160695968973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131426649253515440463979315 197139973880273160695968973)
    ·
      refine ⟨73927490205102435260988365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197139973880273160695968973 73927490205102435260988365)
      ·
        refine ⟨27722808826913413222870637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73927490205102435260988365 27722808826913413222870637)
        ·
          refine ⟨10396053310092529958576489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27722808826913413222870637 10396053310092529958576489)
          ·
            refine ⟨7797039982569397468932367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10396053310092529958576489 7797039982569397468932367)
            ·
              refine ⟨11695559973854096203398551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7797039982569397468932367 11695559973854096203398551)
              ·
                refine ⟨17543339960781144305097827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11695559973854096203398551 17543339960781144305097827)
                ·
                  refine ⟨26315009941171716457646741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17543339960781144305097827 26315009941171716457646741)
                  ·
                    refine ⟨1233516090992424208952191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26315009941171716457646741 1233516090992424208952191)
                    ·
                      rfl

theorem cell23_7206792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_7206792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206792 prefixEnd_7206792 := by exact prefixLift 7206792
  have htrace : WordTrace (prefixWord ++ tailWord_7206792) baseStart_7206792 baseEnd_7206792 := by
    simpa [prefixWord, tailWord_7206792, baseEnd_7206792] using wordTrace_append hprefix tailTrace_7206792
  have hstable : (prefixWord ++ tailWord_7206792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206792).length < 2 ^ (prefixWord ++ tailWord_7206792).sum := by decide
  have hdescent : baseEnd_7206792 < baseStart_7206792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206833 : List Nat := [1, 2, 2, 4, 2, 2, 3, 2, 1, 2, 2]
def baseStart_7206833 : Nat := 118140960795 + 7206833 * 2 ^ 59
def prefixEnd_7206833 : Nat := 4983230072969 + 3 ^ 40 * 7206833 * 2
def baseEnd_7206833 : Nat := 3700569325684106966443885

theorem tailTrace_7206833 : CollatzResearch.WordTrace tailWord_7206833 prefixEnd_7206833 3700569325684106966443885 := by
  unfold tailWord_7206833
  simp only [CollatzResearch.WordTrace]
  refine ⟨262854793899882344930201153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175236529266588229953467435 262854793899882344930201153)
  ·
    refine ⟨197141095424911758697650865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262854793899882344930201153 197141095424911758697650865)
    ·
      refine ⟨147855821568683819023238149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197141095424911758697650865 147855821568683819023238149)
      ·
        refine ⟨27722966544128216066857153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147855821568683819023238149 27722966544128216066857153)
        ·
          refine ⟨20792224908096162050142865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27722966544128216066857153 20792224908096162050142865)
          ·
            refine ⟨15594168681072121537607149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20792224908096162050142865 15594168681072121537607149)
            ·
              refine ⟨5847813255402045576602681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15594168681072121537607149 5847813255402045576602681)
              ·
                refine ⟨4385859941551534182452011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5847813255402045576602681 4385859941551534182452011)
                ·
                  refine ⟨6578789912327301273678017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385859941551534182452011 6578789912327301273678017)
                  ·
                    refine ⟨4934092434245475955258513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6578789912327301273678017 4934092434245475955258513)
                    ·
                      refine ⟨3700569325684106966443885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4934092434245475955258513 3700569325684106966443885)
                      ·
                        rfl

theorem cell23_7206833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_7206833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206833 prefixEnd_7206833 := by exact prefixLift 7206833
  have htrace : WordTrace (prefixWord ++ tailWord_7206833) baseStart_7206833 baseEnd_7206833 := by
    simpa [prefixWord, tailWord_7206833, baseEnd_7206833] using wordTrace_append hprefix tailTrace_7206833
  have hstable : (prefixWord ++ tailWord_7206833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206833).length < 2 ^ (prefixWord ++ tailWord_7206833).sum := by decide
  have hdescent : baseEnd_7206833 < baseStart_7206833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206848 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 1, 8]
def baseStart_7206848 : Nat := 118140960795 + 7206848 * 2 ^ 59
def prefixEnd_7206848 : Nat := 4983230072969 + 3 ^ 40 * 7206848 * 2
def baseEnd_7206848 : Nat := 1233525675964641469252105

theorem tailTrace_7206848 : CollatzResearch.WordTrace tailWord_7206848 prefixEnd_7206848 1233525675964641469252105 := by
  unfold tailWord_7206848
  simp only [CollatzResearch.WordTrace]
  refine ⟨131427670497414001245998599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175236893996552001661331465 131427670497414001245998599)
  ·
    refine ⟨197141505746121001868997899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131427670497414001245998599 197141505746121001868997899)
    ·
      refine ⟨295712258619181502803496849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197141505746121001868997899 295712258619181502803496849)
      ·
        refine ⟨221784193964386127102622637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295712258619181502803496849 221784193964386127102622637)
        ·
          refine ⟨83169072736644797663483489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221784193964386127102622637 83169072736644797663483489)
          ·
            refine ⟨62376804552483598247612617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83169072736644797663483489 62376804552483598247612617)
            ·
              refine ⟨46782603414362698685709463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62376804552483598247612617 46782603414362698685709463)
              ·
                refine ⟨70173905121544048028564195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46782603414362698685709463 70173905121544048028564195)
                ·
                  refine ⟨105260857682316072042846293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70173905121544048028564195 105260857682316072042846293)
                  ·
                    refine ⟨1233525675964641469252105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105260857682316072042846293 1233525675964641469252105)
                    ·
                      rfl

theorem cell23_7206848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_7206848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206848 prefixEnd_7206848 := by exact prefixLift 7206848
  have htrace : WordTrace (prefixWord ++ tailWord_7206848) baseStart_7206848 baseEnd_7206848 := by
    simpa [prefixWord, tailWord_7206848, baseEnd_7206848] using wordTrace_append hprefix tailTrace_7206848
  have hstable : (prefixWord ++ tailWord_7206848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206848).length < 2 ^ (prefixWord ++ tailWord_7206848).sum := by decide
  have hdescent : baseEnd_7206848 < baseStart_7206848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206872 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 1, 4, 2]
def baseStart_7206872 : Nat := 118140960795 + 7206872 * 2 ^ 59
def prefixEnd_7206872 : Nat := 4983230072969 + 3 ^ 40 * 7206872 * 2
def baseEnd_7206872 : Nat := 3700589351429632313856205

theorem tailTrace_7206872 : CollatzResearch.WordTrace tailWord_7206872 prefixEnd_7206872 3700589351429632313856205 := by
  unfold tailWord_7206872
  simp only [CollatzResearch.WordTrace]
  refine ⟨131428108173370527295435435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175237477564494036393913913 131428108173370527295435435)
  ·
    refine ⟨197142162260055790943153153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131428108173370527295435435 197142162260055790943153153)
    ·
      refine ⟨147856621695041843207364865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197142162260055790943153153 147856621695041843207364865)
      ·
        refine ⟨110892466271281382405523649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147856621695041843207364865 110892466271281382405523649)
        ·
          refine ⟨83169349703461036804142737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110892466271281382405523649 83169349703461036804142737)
          ·
            refine ⟨62377012277595777603107053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83169349703461036804142737 62377012277595777603107053)
            ·
              refine ⟨23391379604098416601165145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62377012277595777603107053 23391379604098416601165145)
              ·
                refine ⟨17543534703073812450873859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23391379604098416601165145 17543534703073812450873859)
                ·
                  refine ⟨26315302054610718676310789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17543534703073812450873859 26315302054610718676310789)
                  ·
                    refine ⟨4934119135239509751808273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26315302054610718676310789 4934119135239509751808273)
                    ·
                      refine ⟨3700589351429632313856205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4934119135239509751808273 3700589351429632313856205)
                      ·
                        rfl

theorem cell23_7206872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_7206872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206872 prefixEnd_7206872 := by exact prefixLift 7206872
  have htrace : WordTrace (prefixWord ++ tailWord_7206872) baseStart_7206872 baseEnd_7206872 := by
    simpa [prefixWord, tailWord_7206872, baseEnd_7206872] using wordTrace_append hprefix tailTrace_7206872
  have hstable : (prefixWord ++ tailWord_7206872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206872).length < 2 ^ (prefixWord ++ tailWord_7206872).sum := by decide
  have hdescent : baseEnd_7206872 < baseStart_7206872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206905 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 1, 5, 3]
def baseStart_7206905 : Nat := 118140960795 + 7206905 * 2 ^ 59
def prefixEnd_7206905 : Nat := 4983230072969 + 3 ^ 40 * 7206905 * 2
def baseEnd_7206905 : Nat := 3700606296291230684743553

theorem tailTrace_7206905 : CollatzResearch.WordTrace tailWord_7206905 prefixEnd_7206905 3700606296291230684743553 := by
  unfold tailWord_7206905
  simp only [CollatzResearch.WordTrace]
  refine ⟨262857419955621501226822169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175238279970414334151214779 262857419955621501226822169)
  ·
    refine ⟨197143064966716125920116627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262857419955621501226822169 197143064966716125920116627)
    ·
      refine ⟨295714597450074188880174941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197143064966716125920116627 295714597450074188880174941)
      ·
        refine ⟨110892974043777820830065603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295714597450074188880174941 110892974043777820830065603)
        ·
          refine ⟨166339461065666731245098405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110892974043777820830065603 166339461065666731245098405)
          ·
            refine ⟨31188648949812512108455951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166339461065666731245098405 31188648949812512108455951)
            ·
              refine ⟨46782973424718768162683927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31188648949812512108455951 46782973424718768162683927)
              ·
                refine ⟨70174460137078152244025891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46782973424718768162683927 70174460137078152244025891)
                ·
                  refine ⟨105261690205617228366038837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70174460137078152244025891 105261690205617228366038837)
                  ·
                    refine ⟨9868283456776615159316141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105261690205617228366038837 9868283456776615159316141)
                    ·
                      refine ⟨3700606296291230684743553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9868283456776615159316141 3700606296291230684743553)
                      ·
                        rfl

theorem cell23_7206905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_7206905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206905 prefixEnd_7206905 := by exact prefixLift 7206905
  have htrace : WordTrace (prefixWord ++ tailWord_7206905) baseStart_7206905 baseEnd_7206905 := by
    simpa [prefixWord, tailWord_7206905, baseEnd_7206905] using wordTrace_append hprefix tailTrace_7206905
  have hstable : (prefixWord ++ tailWord_7206905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206905).length < 2 ^ (prefixWord ++ tailWord_7206905).sum := by decide
  have hdescent : baseEnd_7206905 < baseStart_7206905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206972 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 3, 4]
def baseStart_7206972 : Nat := 118140960795 + 7206972 * 2 ^ 59
def prefixEnd_7206972 : Nat := 4983230072969 + 3 ^ 40 * 7206972 * 2
def baseEnd_7206972 : Nat := 1233546899831693974201915

theorem tailTrace_7206972 : CollatzResearch.WordTrace tailWord_7206972 prefixEnd_7206972 1233546899831693974201915 := by
  unfold tailWord_7206972
  simp only [CollatzResearch.WordTrace]
  refine ⟨131429931823189385834755585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175239909097585847779674113 131429931823189385834755585)
  ·
    refine ⟨98572448867392039376066689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131429931823189385834755585 98572448867392039376066689)
    ·
      refine ⟨73929336650544029532050017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98572448867392039376066689 73929336650544029532050017)
      ·
        refine ⟨55447002487908022149037513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73929336650544029532050017 55447002487908022149037513)
        ·
          refine ⟨41585251865931016611778135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55447002487908022149037513 41585251865931016611778135)
          ·
            refine ⟨62377877798896524917667203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41585251865931016611778135 62377877798896524917667203)
            ·
              refine ⟨93566816698344787376500805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62377877798896524917667203 93566816698344787376500805)
              ·
                refine ⟨17543778130939647633093901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93566816698344787376500805 17543778130939647633093901)
                ·
                  refine ⟨6578916799102367862410213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17543778130939647633093901 6578916799102367862410213)
                  ·
                    refine ⟨1233546899831693974201915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6578916799102367862410213 1233546899831693974201915)
                    ·
                      rfl

theorem cell23_7206972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_7206972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206972 prefixEnd_7206972 := by exact prefixLift 7206972
  have htrace : WordTrace (prefixWord ++ tailWord_7206972) baseStart_7206972 baseEnd_7206972 := by
    simpa [prefixWord, tailWord_7206972, baseEnd_7206972] using wordTrace_append hprefix tailTrace_7206972
  have hstable : (prefixWord ++ tailWord_7206972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206972).length < 2 ^ (prefixWord ++ tailWord_7206972).sum := by decide
  have hdescent : baseEnd_7206972 < baseStart_7206972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7206995 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 3]
def baseStart_7206995 : Nat := 118140960795 + 7206995 * 2 ^ 59
def prefixEnd_7206995 : Nat := 4983230072969 + 3 ^ 40 * 7206995 * 2
def baseEnd_7206995 : Nat := 3700652509550135332618139

theorem tailTrace_7206995 : CollatzResearch.WordTrace tailWord_7206995 prefixEnd_7206995 3700652509550135332618139 := by
  unfold tailWord_7206995
  simp only [CollatzResearch.WordTrace]
  refine ⟨262860702525295446597598439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175240468350196964398398959 262860702525295446597598439)
  ·
    refine ⟨394291053787943169896397659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262860702525295446597598439 394291053787943169896397659)
    ·
      refine ⟨591436580681914754844596489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394291053787943169896397659 591436580681914754844596489)
      ·
        refine ⟨443577435511436066133447367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591436580681914754844596489 443577435511436066133447367)
        ·
          refine ⟨665366153267154099200171051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443577435511436066133447367 665366153267154099200171051)
          ·
            refine ⟨998049229900731148800256577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665366153267154099200171051 998049229900731148800256577)
            ·
              refine ⟨748536922425548361600192433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998049229900731148800256577 748536922425548361600192433)
              ·
                refine ⟨561402691819161271200144325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748536922425548361600192433 561402691819161271200144325)
                ·
                  refine ⟨105263004716092738350027061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 561402691819161271200144325 105263004716092738350027061)
                  ·
                    refine ⟨9868406692133694220315037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105263004716092738350027061 9868406692133694220315037)
                    ·
                      refine ⟨3700652509550135332618139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9868406692133694220315037 3700652509550135332618139)
                      ·
                        rfl

theorem cell23_7206995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 3].length) (baseStart_7206995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7206995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7206995 prefixEnd_7206995 := by exact prefixLift 7206995
  have htrace : WordTrace (prefixWord ++ tailWord_7206995) baseStart_7206995 baseEnd_7206995 := by
    simpa [prefixWord, tailWord_7206995, baseEnd_7206995] using wordTrace_append hprefix tailTrace_7206995
  have hstable : (prefixWord ++ tailWord_7206995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7206995).length < 2 ^ (prefixWord ++ tailWord_7206995).sum := by decide
  have hdescent : baseEnd_7206995 < baseStart_7206995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7206995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207049 : List Nat := [1, 2, 1, 1, 4, 2, 5, 1, 1, 5]
def baseStart_7207049 : Nat := 118140960795 + 7207049 * 2 ^ 59
def prefixEnd_7207049 : Nat := 4983230072969 + 3 ^ 40 * 7207049 * 2
def baseEnd_7207049 : Nat := 1233560079168492707114297

theorem tailTrace_7207049 : CollatzResearch.WordTrace tailWord_7207049 prefixEnd_7207049 1233560079168492707114297 := by
  unfold tailWord_7207049
  simp only [CollatzResearch.WordTrace]
  refine ⟨262862672067099813820064201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175241781378066542546709467 262862672067099813820064201)
  ·
    refine ⟨197147004050324860365048151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262862672067099813820064201 197147004050324860365048151)
    ·
      refine ⟨295720506075487290547572227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197147004050324860365048151 295720506075487290547572227)
      ·
        refine ⟨443580759113230935821358341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295720506075487290547572227 443580759113230935821358341)
        ·
          refine ⟨83171392333730800466504689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 443580759113230935821358341 83171392333730800466504689)
          ·
            refine ⟨62378544250298100349878517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83171392333730800466504689 62378544250298100349878517)
            ·
              refine ⟨5847988523465446907801111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62378544250298100349878517 5847988523465446907801111)
              ·
                refine ⟨8771982785198170361701667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5847988523465446907801111 8771982785198170361701667)
                ·
                  refine ⟨13157974177797255542552501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8771982785198170361701667 13157974177797255542552501)
                  ·
                    refine ⟨1233560079168492707114297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13157974177797255542552501 1233560079168492707114297)
                    ·
                      rfl

theorem cell23_7207049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 1, 5].length) (baseStart_7207049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207049 prefixEnd_7207049 := by exact prefixLift 7207049
  have htrace : WordTrace (prefixWord ++ tailWord_7207049) baseStart_7207049 baseEnd_7207049 := by
    simpa [prefixWord, tailWord_7207049, baseEnd_7207049] using wordTrace_append hprefix tailTrace_7207049
  have hstable : (prefixWord ++ tailWord_7207049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207049).length < 2 ^ (prefixWord ++ tailWord_7207049).sum := by decide
  have hdescent : baseEnd_7207049 < baseStart_7207049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207063 : List Nat := [1, 1, 3, 3, 4, 1, 1, 4, 1, 1, 3]
def baseStart_7207063 : Nat := 118140960795 + 7207063 * 2 ^ 59
def prefixEnd_7207063 : Nat := 4983230072969 + 3 ^ 40 * 7207063 * 2
def baseEnd_7207063 : Nat := 3700687426234641066567827

theorem tailTrace_7207063 : CollatzResearch.WordTrace tailWord_7207063 prefixEnd_7207063 3700687426234641066567827 := by
  unfold tailWord_7207063
  simp only [CollatzResearch.WordTrace]
  refine ⟨262863182689049094211073843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175242121792699396140715895 262863182689049094211073843)
  ·
    refine ⟨394294774033573641316610765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262863182689049094211073843 394294774033573641316610765)
    ·
      refine ⟨147860540262590115493729037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394294774033573641316610765 147860540262590115493729037)
      ·
        refine ⟨55447702598471293310148389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147860540262590115493729037 55447702598471293310148389)
        ·
          refine ⟨10396444237213367495652823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55447702598471293310148389 10396444237213367495652823)
          ·
            refine ⟨15594666355820051243479235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10396444237213367495652823 15594666355820051243479235)
            ·
              refine ⟨23391999533730076865218853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15594666355820051243479235 23391999533730076865218853)
              ·
                refine ⟨4385999912574389412228535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23391999533730076865218853 4385999912574389412228535)
                ·
                  refine ⟨6578999868861584118342803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385999912574389412228535 6578999868861584118342803)
                  ·
                    refine ⟨9868499803292376177514205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6578999868861584118342803 9868499803292376177514205)
                    ·
                      refine ⟨3700687426234641066567827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9868499803292376177514205 3700687426234641066567827)
                      ·
                        rfl

theorem cell23_7207063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_7207063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207063 prefixEnd_7207063 := by exact prefixLift 7207063
  have htrace : WordTrace (prefixWord ++ tailWord_7207063) baseStart_7207063 baseEnd_7207063 := by
    simpa [prefixWord, tailWord_7207063, baseEnd_7207063] using wordTrace_append hprefix tailTrace_7207063
  have hstable : (prefixWord ++ tailWord_7207063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207063).length < 2 ^ (prefixWord ++ tailWord_7207063).sum := by decide
  have hdescent : baseEnd_7207063 < baseStart_7207063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207065 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 6]
def baseStart_7207065 : Nat := 118140960795 + 7207065 * 2 ^ 59
def prefixEnd_7207065 : Nat := 4983230072969 + 3 ^ 40 * 7207065 * 2
def baseEnd_7207065 : Nat := 3700688453195950058742817

theorem tailTrace_7207065 : CollatzResearch.WordTrace tailWord_7207065 prefixEnd_7207065 3700688453195950058742817 := by
  unfold tailWord_7207065
  simp only [CollatzResearch.WordTrace]
  refine ⟨262863255635041848552646649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175242170423361232368431099 262863255635041848552646649)
  ·
    refine ⟨197147441726281386414484987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262863255635041848552646649 197147441726281386414484987)
    ·
      refine ⟨295721162589422079621727481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197147441726281386414484987 295721162589422079621727481)
      ·
        refine ⟨221790871942066559716295611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295721162589422079621727481 221790871942066559716295611)
        ·
          refine ⟨332686307913099839574443417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221790871942066559716295611 332686307913099839574443417)
          ·
            refine ⟨249514730934824879680832563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332686307913099839574443417 249514730934824879680832563)
            ·
              refine ⟨374272096402237319521248845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249514730934824879680832563 374272096402237319521248845)
              ·
                refine ⟨140352036150838994820468317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374272096402237319521248845 140352036150838994820468317)
                ·
                  refine ⟨52632013556564623057675619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140352036150838994820468317 52632013556564623057675619)
                  ·
                    refine ⟨78948020334846934586513429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52632013556564623057675619 78948020334846934586513429)
                    ·
                      refine ⟨3700688453195950058742817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78948020334846934586513429 3700688453195950058742817)
                      ·
                        rfl

theorem cell23_7207065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_7207065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207065 prefixEnd_7207065 := by exact prefixLift 7207065
  have htrace : WordTrace (prefixWord ++ tailWord_7207065) baseStart_7207065 baseEnd_7207065 := by
    simpa [prefixWord, tailWord_7207065, baseEnd_7207065] using wordTrace_append hprefix tailTrace_7207065
  have hstable : (prefixWord ++ tailWord_7207065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207065).length < 2 ^ (prefixWord ++ tailWord_7207065).sum := by decide
  have hdescent : baseEnd_7207065 < baseStart_7207065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207119 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 4, 1, 3]
def baseStart_7207119 : Nat := 118140960795 + 7207119 * 2 ^ 59
def prefixEnd_7207119 : Nat := 4983230072969 + 3 ^ 40 * 7207119 * 2
def baseEnd_7207119 : Nat := 3700716181151292847467569

theorem tailTrace_7207119 : CollatzResearch.WordTrace tailWord_7207119 prefixEnd_7207119 3700716181151292847467569 := by
  unfold tailWord_7207119
  simp only [CollatzResearch.WordTrace]
  refine ⟨262865225176846215775112411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175243483451230810516741607 262865225176846215775112411)
  ·
    refine ⟨394297837765269323662668617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262865225176846215775112411 394297837765269323662668617)
    ·
      refine ⟨295723378323951992747001463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394297837765269323662668617 295723378323951992747001463)
      ·
        refine ⟨443585067485927989120502195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295723378323951992747001463 443585067485927989120502195)
        ·
          refine ⟨665377601228891983680753293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443585067485927989120502195 665377601228891983680753293)
          ·
            refine ⟨249516600460834493880282485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 665377601228891983680753293 249516600460834493880282485)
            ·
              refine ⟨23392181293203233801276483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249516600460834493880282485 23392181293203233801276483)
              ·
                refine ⟨35088271939804850701914725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23392181293203233801276483 35088271939804850701914725)
                ·
                  refine ⟨6579050988713409506609011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35088271939804850701914725 6579050988713409506609011)
                  ·
                    refine ⟨9868576483070114259913517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6579050988713409506609011 9868576483070114259913517)
                    ·
                      refine ⟨3700716181151292847467569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9868576483070114259913517 3700716181151292847467569)
                      ·
                        rfl

theorem cell23_7207119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 1, 3].length) (baseStart_7207119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207119 prefixEnd_7207119 := by exact prefixLift 7207119
  have htrace : WordTrace (prefixWord ++ tailWord_7207119) baseStart_7207119 baseEnd_7207119 := by
    simpa [prefixWord, tailWord_7207119, baseEnd_7207119] using wordTrace_append hprefix tailTrace_7207119
  have hstable : (prefixWord ++ tailWord_7207119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207119).length < 2 ^ (prefixWord ++ tailWord_7207119).sum := by decide
  have hdescent : baseEnd_7207119 < baseStart_7207119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207129 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 5, 3, 2]
def baseStart_7207129 : Nat := 118140960795 + 7207129 * 2 ^ 59
def prefixEnd_7207129 : Nat := 4983230072969 + 3 ^ 40 * 7207129 * 2
def baseEnd_7207129 : Nat := 3700721315957837808342523

theorem tailTrace_7207129 : CollatzResearch.WordTrace tailWord_7207129 prefixEnd_7207129 3700721315957837808342523 := by
  unfold tailWord_7207129
  simp only [CollatzResearch.WordTrace]
  refine ⟨262865589906809987482976441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175243726604539991655317627 262865589906809987482976441)
  ·
    refine ⟨197149192430107490612232331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262865589906809987482976441 197149192430107490612232331)
    ·
      refine ⟨295723788645161235918348497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197149192430107490612232331 295723788645161235918348497)
      ·
        refine ⟨221792841483870926938761373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295723788645161235918348497 221792841483870926938761373)
        ·
          refine ⟨83172315556451597602035515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221792841483870926938761373 83172315556451597602035515)
          ·
            refine ⟨124758473334677396403053273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83172315556451597602035515 124758473334677396403053273)
            ·
              refine ⟨93568855001008047302289955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124758473334677396403053273 93568855001008047302289955)
              ·
                refine ⟨140353282501512070953434933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93568855001008047302289955 140353282501512070953434933)
                ·
                  refine ⟨13158120234516756651884525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140353282501512070953434933 13158120234516756651884525)
                  ·
                    refine ⟨4934295087943783744456697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13158120234516756651884525 4934295087943783744456697)
                    ·
                      refine ⟨3700721315957837808342523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4934295087943783744456697 3700721315957837808342523)
                      ·
                        rfl

theorem cell23_7207129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 3, 2].length) (baseStart_7207129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207129 prefixEnd_7207129 := by exact prefixLift 7207129
  have htrace : WordTrace (prefixWord ++ tailWord_7207129) baseStart_7207129 baseEnd_7207129 := by
    simpa [prefixWord, tailWord_7207129, baseEnd_7207129] using wordTrace_append hprefix tailTrace_7207129
  have hstable : (prefixWord ++ tailWord_7207129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207129).length < 2 ^ (prefixWord ++ tailWord_7207129).sum := by decide
  have hdescent : baseEnd_7207129 < baseStart_7207129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207162 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_7207162 : Nat := 118140960795 + 7207162 * 2 ^ 59
def prefixEnd_7207162 : Nat := 4983230072969 + 3 ^ 40 * 7207162 * 2
def baseEnd_7207162 : Nat := 3700738260819436179229871

theorem tailTrace_7207162 : CollatzResearch.WordTrace tailWord_7207162 prefixEnd_7207162 3700738260819436179229871 := by
  unfold tailWord_7207162
  simp only [CollatzResearch.WordTrace]
  refine ⟨65716698378922608529731935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175244529010460289412618493 65716698378922608529731935)
  ·
    refine ⟨98575047568383912794597903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65716698378922608529731935 98575047568383912794597903)
    ·
      refine ⟨147862571352575869191896855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98575047568383912794597903 147862571352575869191896855)
      ·
        refine ⟨221793857028863803787845283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147862571352575869191896855 221793857028863803787845283)
        ·
          refine ⟨332690785543295705681767925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221793857028863803787845283 332690785543295705681767925)
          ·
            refine ⟨31189761144683972407665743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 332690785543295705681767925 31189761144683972407665743)
            ·
              refine ⟨46784641717025958611498615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31189761144683972407665743 46784641717025958611498615)
              ·
                refine ⟨70176962575538937917247923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46784641717025958611498615 70176962575538937917247923)
                ·
                  refine ⟨105265443863308406875871885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70176962575538937917247923 105265443863308406875871885)
                  ·
                    refine ⟨39474541448740652578451957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105265443863308406875871885 39474541448740652578451957)
                    ·
                      refine ⟨3700738260819436179229871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39474541448740652578451957 3700738260819436179229871)
                      ·
                        rfl

theorem cell23_7207162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_7207162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207162 prefixEnd_7207162 := by exact prefixLift 7207162
  have htrace : WordTrace (prefixWord ++ tailWord_7207162) baseStart_7207162 baseEnd_7207162 := by
    simpa [prefixWord, tailWord_7207162, baseEnd_7207162] using wordTrace_append hprefix tailTrace_7207162
  have hstable : (prefixWord ++ tailWord_7207162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207162).length < 2 ^ (prefixWord ++ tailWord_7207162).sum := by decide
  have hdescent : baseEnd_7207162 < baseStart_7207162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207197 : List Nat := [1, 4, 2, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_7207197 : Nat := 118140960795 + 7207197 * 2 ^ 59
def prefixEnd_7207197 : Nat := 4983230072969 + 3 ^ 40 * 7207197 * 2
def baseEnd_7207197 : Nat := 3700756232642343542292211

theorem tailTrace_7207197 : CollatzResearch.WordTrace tailWord_7207197 prefixEnd_7207197 3700756232642343542292211 := by
  unfold tailWord_7207197
  simp only [CollatzResearch.WordTrace]
  refine ⟨262868070070563635096451845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175245380047042423397634563 262868070070563635096451845)
  ·
    refine ⟨49287763138230681580584721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262868070070563635096451845 49287763138230681580584721)
    ·
      refine ⟨36965822353673011185438541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49287763138230681580584721 36965822353673011185438541)
      ·
        refine ⟨13862183382627379194539453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36965822353673011185438541 13862183382627379194539453)
        ·
          refine ⟨5198318768485267197952295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13862183382627379194539453 5198318768485267197952295)
          ·
            refine ⟨7797478152727900796928443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5198318768485267197952295 7797478152727900796928443)
            ·
              refine ⟨11696217229091851195392665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7797478152727900796928443 11696217229091851195392665)
              ·
                refine ⟨8772162921818888396544499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11696217229091851195392665 8772162921818888396544499)
                ·
                  refine ⟨13158244382728332594816749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8772162921818888396544499 13158244382728332594816749)
                  ·
                    refine ⟨4934341643523124723056281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13158244382728332594816749 4934341643523124723056281)
                    ·
                      refine ⟨3700756232642343542292211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4934341643523124723056281 3700756232642343542292211)
                      ·
                        rfl

theorem cell23_7207197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_7207197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207197 prefixEnd_7207197 := by exact prefixLift 7207197
  have htrace : WordTrace (prefixWord ++ tailWord_7207197) baseStart_7207197 baseEnd_7207197 := by
    simpa [prefixWord, tailWord_7207197, baseEnd_7207197] using wordTrace_append hprefix tailTrace_7207197
  have hstable : (prefixWord ++ tailWord_7207197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207197).length < 2 ^ (prefixWord ++ tailWord_7207197).sum := by decide
  have hdescent : baseEnd_7207197 < baseStart_7207197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207212 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 1, 7]
def baseStart_7207212 : Nat := 118140960795 + 7207212 * 2 ^ 59
def prefixEnd_7207212 : Nat := 4983230072969 + 3 ^ 40 * 7207212 * 2
def baseEnd_7207212 : Nat := 1233587978284053661201547

theorem tailTrace_7207212 : CollatzResearch.WordTrace tailWord_7207212 prefixEnd_7207212 1233587978284053661201547 := by
  unfold tailWord_7207212
  simp only [CollatzResearch.WordTrace]
  refine ⟨131434308582754646329123945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175245744777006195105498593 131434308582754646329123945)
  ·
    refine ⟨98575731437065984746842959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131434308582754646329123945 98575731437065984746842959)
    ·
      refine ⟨147863597155598977120264439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98575731437065984746842959 147863597155598977120264439)
      ·
        refine ⟨221795395733398465680396659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147863597155598977120264439 221795395733398465680396659)
        ·
          refine ⟨332693093600097698520594989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221795395733398465680396659 332693093600097698520594989)
          ·
            refine ⟨124759910100036636945223121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332693093600097698520594989 124759910100036636945223121)
            ·
              refine ⟨93569932575027477708917341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124759910100036636945223121 93569932575027477708917341)
              ·
                refine ⟨35088724715635304140844003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93569932575027477708917341 35088724715635304140844003)
                ·
                  refine ⟨52633087073452956211266005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35088724715635304140844003 52633087073452956211266005)
                  ·
                    refine ⟨1233587978284053661201547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52633087073452956211266005 1233587978284053661201547)
                    ·
                      rfl

theorem cell23_7207212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_7207212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207212 prefixEnd_7207212 := by exact prefixLift 7207212
  have htrace : WordTrace (prefixWord ++ tailWord_7207212) baseStart_7207212 baseEnd_7207212 := by
    simpa [prefixWord, tailWord_7207212, baseEnd_7207212] using wordTrace_append hprefix tailTrace_7207212
  have hstable : (prefixWord ++ tailWord_7207212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207212).length < 2 ^ (prefixWord ++ tailWord_7207212).sum := by decide
  have hdescent : baseEnd_7207212 < baseStart_7207212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207233 : List Nat := [1, 2, 5, 2, 2, 1, 1, 4, 5]
def baseStart_7207233 : Nat := 118140960795 + 7207233 * 2 ^ 59
def prefixEnd_7207233 : Nat := 4983230072969 + 3 ^ 40 * 7207233 * 2
def baseEnd_7207233 : Nat := 411197190882878377938005

theorem tailTrace_7207233 : CollatzResearch.WordTrace tailWord_7207233 prefixEnd_7207233 411197190882878377938005 := by
  unfold tailWord_7207233
  simp only [CollatzResearch.WordTrace]
  refine ⟨262869383098433213244762353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175246255398955475496508235 262869383098433213244762353)
  ·
    refine ⟨197152037323824909933571765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262869383098433213244762353 197152037323824909933571765)
    ·
      refine ⟨18483003499108585306272353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197152037323824909933571765 18483003499108585306272353)
      ·
        refine ⟨13862252624331438979704265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18483003499108585306272353 13862252624331438979704265)
        ·
          refine ⟨10396689468248579234778199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13862252624331438979704265 10396689468248579234778199)
          ·
            refine ⟨15595034202372868852167299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10396689468248579234778199 15595034202372868852167299)
            ·
              refine ⟨23392551303559303278250949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15595034202372868852167299 23392551303559303278250949)
              ·
                refine ⟨4386103369417369364672053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23392551303559303278250949 4386103369417369364672053)
                ·
                  refine ⟨411197190882878377938005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4386103369417369364672053 411197190882878377938005)
                  ·
                    rfl

theorem cell23_7207233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 5].length) (baseStart_7207233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207233 prefixEnd_7207233 := by exact prefixLift 7207233
  have htrace : WordTrace (prefixWord ++ tailWord_7207233) baseStart_7207233 baseEnd_7207233 := by
    simpa [prefixWord, tailWord_7207233, baseEnd_7207233] using wordTrace_append hprefix tailTrace_7207233
  have hstable : (prefixWord ++ tailWord_7207233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207233).length < 2 ^ (prefixWord ++ tailWord_7207233).sum := by decide
  have hdescent : baseEnd_7207233 < baseStart_7207233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207242 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 4, 8]
def baseStart_7207242 : Nat := 118140960795 + 7207242 * 2 ^ 59
def prefixEnd_7207242 : Nat := 4983230072969 + 3 ^ 40 * 7207242 * 2
def baseEnd_7207242 : Nat := 1233593113090598622076501

theorem tailTrace_7207242 : CollatzResearch.WordTrace tailWord_7207242 prefixEnd_7207242 1233593113090598622076501 := by
  unfold tailWord_7207242
  simp only [CollatzResearch.WordTrace]
  refine ⟨65717427838850151945459995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175246474236933738521226653 65717427838850151945459995)
  ·
    refine ⟨98576141758275227918189993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65717427838850151945459995 98576141758275227918189993)
    ·
      refine ⟨73932106318706420938642495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98576141758275227918189993 73932106318706420938642495)
      ·
        refine ⟨110898159478059631407963743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73932106318706420938642495 110898159478059631407963743)
        ·
          refine ⟨166347239217089447111945615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110898159478059631407963743 166347239217089447111945615)
          ·
            refine ⟨249520858825634170667918423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166347239217089447111945615 249520858825634170667918423)
            ·
              refine ⟨374281288238451256001877635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249520858825634170667918423 374281288238451256001877635)
              ·
                refine ⟨561421932357676884002816453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374281288238451256001877635 561421932357676884002816453)
                ·
                  refine ⟨105266612317064415750528085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 561421932357676884002816453 105266612317064415750528085)
                  ·
                    refine ⟨1233593113090598622076501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105266612317064415750528085 1233593113090598622076501)
                    ·
                      rfl

theorem cell23_7207242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_7207242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207242 prefixEnd_7207242 := by exact prefixLift 7207242
  have htrace : WordTrace (prefixWord ++ tailWord_7207242) baseStart_7207242 baseEnd_7207242 := by
    simpa [prefixWord, tailWord_7207242, baseEnd_7207242] using wordTrace_append hprefix tailTrace_7207242
  have hstable : (prefixWord ++ tailWord_7207242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207242).length < 2 ^ (prefixWord ++ tailWord_7207242).sum := by decide
  have hdescent : baseEnd_7207242 < baseStart_7207242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207266 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_7207266 : Nat := 118140960795 + 7207266 * 2 ^ 59
def prefixEnd_7207266 : Nat := 4983230072969 + 3 ^ 40 * 7207266 * 2
def baseEnd_7207266 : Nat := 3700791662807503772329393

theorem tailTrace_7207266 : CollatzResearch.WordTrace tailWord_7207266 prefixEnd_7207266 3700791662807503772329393 := by
  unfold tailWord_7207266
  simp only [CollatzResearch.WordTrace]
  refine ⟨65717646676828414970178413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175247057804875773253809101 65717646676828414970178413)
  ·
    refine ⟨24644117503810655613816905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65717646676828414970178413 24644117503810655613816905)
    ·
      refine ⟨18483088127857991710362679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24644117503810655613816905 18483088127857991710362679)
      ·
        refine ⟨27724632191786987565544019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18483088127857991710362679 27724632191786987565544019)
        ·
          refine ⟨41586948287680481348316029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27724632191786987565544019 41586948287680481348316029)
          ·
            refine ⟨15595105607880180505618511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41586948287680481348316029 15595105607880180505618511)
            ·
              refine ⟨23392658411820270758427767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15595105607880180505618511 23392658411820270758427767)
              ·
                refine ⟨35088987617730406137641651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23392658411820270758427767 35088987617730406137641651)
                ·
                  refine ⟨52633481426595609206462477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35088987617730406137641651 52633481426595609206462477)
                  ·
                    refine ⟨19737555534973353452423429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52633481426595609206462477 19737555534973353452423429)
                    ·
                      refine ⟨3700791662807503772329393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19737555534973353452423429 3700791662807503772329393)
                      ·
                        rfl

theorem cell23_7207266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_7207266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207266 prefixEnd_7207266 := by exact prefixLift 7207266
  have htrace : WordTrace (prefixWord ++ tailWord_7207266) baseStart_7207266 baseEnd_7207266 := by
    simpa [prefixWord, tailWord_7207266, baseEnd_7207266] using wordTrace_append hprefix tailTrace_7207266
  have hstable : (prefixWord ++ tailWord_7207266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207266).length < 2 ^ (prefixWord ++ tailWord_7207266).sum := by decide
  have hdescent : baseEnd_7207266 < baseStart_7207266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207293 : List Nat := [1, 4, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_7207293 : Nat := 118140960795 + 7207293 * 2 ^ 59
def prefixEnd_7207293 : Nat := 4983230072969 + 3 ^ 40 * 7207293 * 2
def baseEnd_7207293 : Nat := 1233601842261725055563923

theorem tailTrace_7207293 : CollatzResearch.WordTrace tailWord_7207293 prefixEnd_7207293 1233601842261725055563923 := by
  unfold tailWord_7207293
  simp only [CollatzResearch.WordTrace]
  refine ⟨262871571478215843491946533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175247714318810562327964355 262871571478215843491946533)
  ·
    refine ⟨49288419652165470654739975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262871571478215843491946533 49288419652165470654739975)
    ·
      refine ⟨73932629478248205982109963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49288419652165470654739975 73932629478248205982109963)
      ·
        refine ⟨110898944217372308973164945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73932629478248205982109963 110898944217372308973164945)
        ·
          refine ⟨83174208163029231729873709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110898944217372308973164945 83174208163029231729873709)
          ·
            refine ⟨31190328061135961898702641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83174208163029231729873709 31190328061135961898702641)
            ·
              refine ⟨23392746045851971424026981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31190328061135961898702641 23392746045851971424026981)
              ·
                refine ⟨4386139883597244642005059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23392746045851971424026981 4386139883597244642005059)
                ·
                  refine ⟨6579209825395866963007589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4386139883597244642005059 6579209825395866963007589)
                  ·
                    refine ⟨1233601842261725055563923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6579209825395866963007589 1233601842261725055563923)
                    ·
                      rfl

theorem cell23_7207293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_7207293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207293 prefixEnd_7207293 := by exact prefixLift 7207293
  have htrace : WordTrace (prefixWord ++ tailWord_7207293) baseStart_7207293 baseEnd_7207293 := by
    simpa [prefixWord, tailWord_7207293, baseEnd_7207293] using wordTrace_append hprefix tailTrace_7207293
  have hstable : (prefixWord ++ tailWord_7207293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207293).length < 2 ^ (prefixWord ++ tailWord_7207293).sum := by decide
  have hdescent : baseEnd_7207293 < baseStart_7207293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207319 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 3, 5]
def baseStart_7207319 : Nat := 118140960795 + 7207319 * 2 ^ 59
def prefixEnd_7207319 : Nat := 4983230072969 + 3 ^ 40 * 7207319 * 2
def baseEnd_7207319 : Nat := 1233606292427397354988883

theorem tailTrace_7207319 : CollatzResearch.WordTrace tailWord_7207319 prefixEnd_7207319 1233606292427397354988883 := by
  unfold tailWord_7207319
  simp only [CollatzResearch.WordTrace]
  refine ⟨262872519776121649932393011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175248346517414433288262007 262872519776121649932393011)
  ·
    refine ⟨394308779664182474898589517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262872519776121649932393011 394308779664182474898589517)
    ·
      refine ⟨147865792374068428086971069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394308779664182474898589517 147865792374068428086971069)
      ·
        refine ⟨55449672140275660532614151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147865792374068428086971069 55449672140275660532614151)
        ·
          refine ⟨83174508210413490798921227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55449672140275660532614151 83174508210413490798921227)
          ·
            refine ⟨124761762315620236198381841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83174508210413490798921227 124761762315620236198381841)
            ·
              refine ⟨93571321736715177148786381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124761762315620236198381841 93571321736715177148786381)
              ·
                refine ⟨35089245651268191430794893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93571321736715177148786381 35089245651268191430794893)
                ·
                  refine ⟨13158467119225571786548085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35089245651268191430794893 13158467119225571786548085)
                  ·
                    refine ⟨1233606292427397354988883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13158467119225571786548085 1233606292427397354988883)
                    ·
                      rfl

theorem cell23_7207319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_7207319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207319 prefixEnd_7207319 := by exact prefixLift 7207319
  have htrace : WordTrace (prefixWord ++ tailWord_7207319) baseStart_7207319 baseEnd_7207319 := by
    simpa [prefixWord, tailWord_7207319, baseEnd_7207319] using wordTrace_append hprefix tailTrace_7207319
  have hstable : (prefixWord ++ tailWord_7207319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207319).length < 2 ^ (prefixWord ++ tailWord_7207319).sum := by decide
  have hdescent : baseEnd_7207319 < baseStart_7207319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207359 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 3]
def baseStart_7207359 : Nat := 118140960795 + 7207359 * 2 ^ 59
def prefixEnd_7207359 : Nat := 4983230072969 + 3 ^ 40 * 7207359 * 2
def baseEnd_7207359 : Nat := 3700839416508371908466465

theorem tailTrace_7207359 : CollatzResearch.WordTrace tailWord_7207359 prefixEnd_7207359 3700839416508371908466465 := by
  unfold tailWord_7207359
  simp only [CollatzResearch.WordTrace]
  refine ⟨262873978695976736763849131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175249319130651157842566087 262873978695976736763849131)
  ·
    refine ⟨394310968043965105145773697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262873978695976736763849131 394310968043965105145773697)
    ·
      refine ⟨295733226032973828859330273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394310968043965105145773697 295733226032973828859330273)
      ·
        refine ⟨221799919524730371644497705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295733226032973828859330273 221799919524730371644497705)
        ·
          refine ⟨166349939643547778733373279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221799919524730371644497705 166349939643547778733373279)
          ·
            refine ⟨249524909465321668100059919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166349939643547778733373279 249524909465321668100059919)
            ·
              refine ⟨374287364197982502150089879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249524909465321668100059919 374287364197982502150089879)
              ·
                refine ⟨561431046296973753225134819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374287364197982502150089879 561431046296973753225134819)
                ·
                  refine ⟨842146569445460629837702229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561431046296973753225134819 842146569445460629837702229)
                  ·
                    refine ⟨9868905110688991755910573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 842146569445460629837702229 9868905110688991755910573)
                    ·
                      refine ⟨3700839416508371908466465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9868905110688991755910573 3700839416508371908466465)
                      ·
                        rfl

theorem cell23_7207359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_7207359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207359 prefixEnd_7207359 := by exact prefixLift 7207359
  have htrace : WordTrace (prefixWord ++ tailWord_7207359) baseStart_7207359 baseEnd_7207359 := by
    simpa [prefixWord, tailWord_7207359, baseEnd_7207359] using wordTrace_append hprefix tailTrace_7207359
  have hstable : (prefixWord ++ tailWord_7207359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207359).length < 2 ^ (prefixWord ++ tailWord_7207359).sum := by decide
  have hdescent : baseEnd_7207359 < baseStart_7207359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207369 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 6]
def baseStart_7207369 : Nat := 118140960795 + 7207369 * 2 ^ 59
def prefixEnd_7207369 : Nat := 4983230072969 + 3 ^ 40 * 7207369 * 2
def baseEnd_7207369 : Nat := 3700844551314916869341419

theorem tailTrace_7207369 : CollatzResearch.WordTrace tailWord_7207369 prefixEnd_7207369 3700844551314916869341419 := by
  unfold tailWord_7207369
  simp only [CollatzResearch.WordTrace]
  refine ⟨262874343425940508471713161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175249562283960338981142107 262874343425940508471713161)
  ·
    refine ⟨197155757569455381353784871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262874343425940508471713161 197155757569455381353784871)
    ·
      refine ⟨295733636354183072030677307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197155757569455381353784871 295733636354183072030677307)
      ·
        refine ⟨443600454531274608046015961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295733636354183072030677307 443600454531274608046015961)
        ·
          refine ⟨332700340898455956034511971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443600454531274608046015961 332700340898455956034511971)
          ·
            refine ⟨499050511347683934051767957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332700340898455956034511971 499050511347683934051767957)
            ·
              refine ⟨23392992719422684408676623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 499050511347683934051767957 23392992719422684408676623)
              ·
                refine ⟨35089489079134026613014935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23392992719422684408676623 35089489079134026613014935)
                ·
                  refine ⟨52634233618701039919522403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35089489079134026613014935 52634233618701039919522403)
                  ·
                    refine ⟨78951350428051559879283605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52634233618701039919522403 78951350428051559879283605)
                    ·
                      refine ⟨3700844551314916869341419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78951350428051559879283605 3700844551314916869341419)
                      ·
                        rfl

theorem cell23_7207369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_7207369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207369 prefixEnd_7207369 := by exact prefixLift 7207369
  have htrace : WordTrace (prefixWord ++ tailWord_7207369) baseStart_7207369 baseEnd_7207369 := by
    simpa [prefixWord, tailWord_7207369, baseEnd_7207369] using wordTrace_append hprefix tailTrace_7207369
  have hstable : (prefixWord ++ tailWord_7207369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207369).length < 2 ^ (prefixWord ++ tailWord_7207369).sum := by decide
  have hdescent : baseEnd_7207369 < baseStart_7207369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207386 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_7207386 : Nat := 118140960795 + 7207386 * 2 ^ 59
def prefixEnd_7207386 : Nat := 4983230072969 + 3 ^ 40 * 7207386 * 2
def baseEnd_7207386 : Nat := 3700853280486043302828841

theorem tailTrace_7207386 : CollatzResearch.WordTrace tailWord_7207386 prefixEnd_7207386 3700853280486043302828841 := by
  unfold tailWord_7207386
  simp only [CollatzResearch.WordTrace]
  refine ⟨65718740866719730093770503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175249975644585946916721341 65718740866719730093770503)
  ·
    refine ⟨98578111300079595140655755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65718740866719730093770503 98578111300079595140655755)
    ·
      refine ⟨147867166950119392710983633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98578111300079595140655755 147867166950119392710983633)
      ·
        refine ⟨110900375212589544533237725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147867166950119392710983633 110900375212589544533237725)
        ·
          refine ⟨41587640704721079199964147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110900375212589544533237725 41587640704721079199964147)
          ·
            refine ⟨62381461057081618799946221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41587640704721079199964147 62381461057081618799946221)
            ·
              refine ⟨23393047896405607049979833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62381461057081618799946221 23393047896405607049979833)
              ·
                refine ⟨17544785922304205287484875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23393047896405607049979833 17544785922304205287484875)
                ·
                  refine ⟨26317178883456307931227313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17544785922304205287484875 26317178883456307931227313)
                  ·
                    refine ⟨19737884162592230948420485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26317178883456307931227313 19737884162592230948420485)
                    ·
                      refine ⟨3700853280486043302828841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19737884162592230948420485 3700853280486043302828841)
                      ·
                        rfl

theorem cell23_7207386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_7207386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207386 prefixEnd_7207386 := by exact prefixLift 7207386
  have htrace : WordTrace (prefixWord ++ tailWord_7207386) baseStart_7207386 baseEnd_7207386 := by
    simpa [prefixWord, tailWord_7207386, baseEnd_7207386] using wordTrace_append hprefix tailTrace_7207386
  have hstable : (prefixWord ++ tailWord_7207386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207386).length < 2 ^ (prefixWord ++ tailWord_7207386).sum := by decide
  have hdescent : baseEnd_7207386 < baseStart_7207386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207409 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 1, 9]
def baseStart_7207409 : Nat := 118140960795 + 7207409 * 2 ^ 59
def prefixEnd_7207409 : Nat := 4983230072969 + 3 ^ 40 * 7207409 * 2
def baseEnd_7207409 : Nat := 1233621696847032237613745

theorem tailTrace_7207409 : CollatzResearch.WordTrace tailWord_7207409 prefixEnd_7207409 1233621696847032237613745 := by
  unfold tailWord_7207409
  simp only [CollatzResearch.WordTrace]
  refine ⟨262875802345795595303169281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175250534897197063535446187 262875802345795595303169281)
  ·
    refine ⟨197156851759346696477376961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262875802345795595303169281 197156851759346696477376961)
    ·
      refine ⟨147867638819510022358032721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197156851759346696477376961 147867638819510022358032721)
      ·
        refine ⟨110900729114632516768524541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147867638819510022358032721 110900729114632516768524541)
        ·
          refine ⟨41587773417987193788196703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110900729114632516768524541 41587773417987193788196703)
          ·
            refine ⟨62381660126980790682295055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41587773417987193788196703 62381660126980790682295055)
            ·
              refine ⟨93572490190471186023442583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62381660126980790682295055 93572490190471186023442583)
              ·
                refine ⟨140358735285706779035163875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93572490190471186023442583 140358735285706779035163875)
                ·
                  refine ⟨210538102928560168552745813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140358735285706779035163875 210538102928560168552745813)
                  ·
                    refine ⟨1233621696847032237613745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 210538102928560168552745813 1233621696847032237613745)
                    ·
                      rfl

theorem cell23_7207409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_7207409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207409 prefixEnd_7207409 := by exact prefixLift 7207409
  have htrace : WordTrace (prefixWord ++ tailWord_7207409) baseStart_7207409 baseEnd_7207409 := by
    simpa [prefixWord, tailWord_7207409, baseEnd_7207409] using wordTrace_append hprefix tailTrace_7207409
  have hstable : (prefixWord ++ tailWord_7207409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207409).length < 2 ^ (prefixWord ++ tailWord_7207409).sum := by decide
  have hdescent : baseEnd_7207409 < baseStart_7207409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207423 : List Nat := [1, 1, 2, 2, 1, 2, 3, 5, 2, 1, 3]
def baseStart_7207423 : Nat := 118140960795 + 7207423 * 2 ^ 59
def prefixEnd_7207423 : Nat := 4983230072969 + 3 ^ 40 * 7207423 * 2
def baseEnd_7207423 : Nat := 3700872279270259658066171

theorem tailTrace_7207423 : CollatzResearch.WordTrace tailWord_7207423 prefixEnd_7207423 3700872279270259658066171 := by
  unfold tailWord_7207423
  simp only [CollatzResearch.WordTrace]
  refine ⟨262876312967744875694178923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175250875311829917129452615 262876312967744875694178923)
  ·
    refine ⟨394314469451617313541268385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262876312967744875694178923 394314469451617313541268385)
    ·
      refine ⟨295735852088712985155951289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394314469451617313541268385 295735852088712985155951289)
      ·
        refine ⟨221801889066534738866963467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295735852088712985155951289 221801889066534738866963467)
        ·
          refine ⟨332702833599802108300445201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221801889066534738866963467 332702833599802108300445201)
          ·
            refine ⟨249527125199851581225333901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332702833599802108300445201 249527125199851581225333901)
            ·
              refine ⟨93572671949944342959500213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249527125199851581225333901 93572671949944342959500213)
              ·
                refine ⟨8772437995307282152453145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93572671949944342959500213 8772437995307282152453145)
                ·
                  refine ⟨6579328496480461614339859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8772437995307282152453145 6579328496480461614339859)
                  ·
                    refine ⟨9868992744720692421509789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6579328496480461614339859 9868992744720692421509789)
                    ·
                      refine ⟨3700872279270259658066171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9868992744720692421509789 3700872279270259658066171)
                      ·
                        rfl

theorem cell23_7207423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_7207423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207423 prefixEnd_7207423 := by exact prefixLift 7207423
  have htrace : WordTrace (prefixWord ++ tailWord_7207423) baseStart_7207423 baseEnd_7207423 := by
    simpa [prefixWord, tailWord_7207423, baseEnd_7207423] using wordTrace_append hprefix tailTrace_7207423
  have hstable : (prefixWord ++ tailWord_7207423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207423).length < 2 ^ (prefixWord ++ tailWord_7207423).sum := by decide
  have hdescent : baseEnd_7207423 < baseStart_7207423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207439 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 4, 6]
def baseStart_7207439 : Nat := 118140960795 + 7207439 * 2 ^ 59
def prefixEnd_7207439 : Nat := 4983230072969 + 3 ^ 40 * 7207439 * 2
def baseEnd_7207439 : Nat := 1233626831653577198488699

theorem tailTrace_7207439 : CollatzResearch.WordTrace tailWord_7207439 prefixEnd_7207439 1233626831653577198488699 := by
  unfold tailWord_7207439
  simp only [CollatzResearch.WordTrace]
  refine ⟨262876896535686910426761371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175251264357124606951174247 262876896535686910426761371)
  ·
    refine ⟨394315344803530365640142057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262876896535686910426761371 394315344803530365640142057)
    ·
      refine ⟨295736508602647774230106543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394315344803530365640142057 295736508602647774230106543)
      ·
        refine ⟨443604762903971661345159815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295736508602647774230106543 443604762903971661345159815)
        ·
          refine ⟨665407144355957492017739723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443604762903971661345159815 665407144355957492017739723)
          ·
            refine ⟨998110716533936238026609585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665407144355957492017739723 998110716533936238026609585)
            ·
              refine ⟨748583037400452178519957189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998110716533936238026609585 748583037400452178519957189)
              ·
                refine ⟨140359319512584783472491973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 748583037400452178519957189 140359319512584783472491973)
                ·
                  refine ⟨26317372408609646901092245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140359319512584783472491973 26317372408609646901092245)
                  ·
                    refine ⟨1233626831653577198488699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26317372408609646901092245 1233626831653577198488699)
                    ·
                      rfl

theorem cell23_7207439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_7207439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207439 prefixEnd_7207439 := by exact prefixLift 7207439
  have htrace : WordTrace (prefixWord ++ tailWord_7207439) baseStart_7207439 baseEnd_7207439 := by
    simpa [prefixWord, tailWord_7207439, baseEnd_7207439] using wordTrace_append hprefix tailTrace_7207439
  have hstable : (prefixWord ++ tailWord_7207439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207439).length < 2 ^ (prefixWord ++ tailWord_7207439).sum := by decide
  have hdescent : baseEnd_7207439 < baseStart_7207439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207444 : List Nat := [2, 4, 3, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_7207444 : Nat := 118140960795 + 7207444 * 2 ^ 59
def prefixEnd_7207444 : Nat := 4983230072969 + 3 ^ 40 * 7207444 * 2
def baseEnd_7207444 : Nat := 3700883062364004075903575

theorem tailTrace_7207444 : CollatzResearch.WordTrace tailWord_7207444 prefixEnd_7207444 3700883062364004075903575 := by
  unfold tailWord_7207444
  simp only [CollatzResearch.WordTrace]
  refine ⟨131438539450334398140346693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175251385933779197520462257 131438539450334398140346693)
  ·
    refine ⟨24644726146937699651315005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131438539450334398140346693 24644726146937699651315005)
    ·
      refine ⟨9241772305101637369243127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24644726146937699651315005 9241772305101637369243127)
      ·
        refine ⟨13862658457652456053864691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9241772305101637369243127 13862658457652456053864691)
        ·
          refine ⟨20793987686478684080797037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13862658457652456053864691 20793987686478684080797037)
          ·
            refine ⟨7797745382429506530298889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20793987686478684080797037 7797745382429506530298889)
            ·
              refine ⟨5848309036822129897724167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7797745382429506530298889 5848309036822129897724167)
              ·
                refine ⟨8772463555233194846586251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5848309036822129897724167 8772463555233194846586251)
                ·
                  refine ⟨13158695332849792269879377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8772463555233194846586251 13158695332849792269879377)
                  ·
                    refine ⟨9869021499637344202409533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13158695332849792269879377 9869021499637344202409533)
                    ·
                      refine ⟨3700883062364004075903575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9869021499637344202409533 3700883062364004075903575)
                      ·
                        rfl

theorem cell23_7207444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_7207444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207444 prefixEnd_7207444 := by exact prefixLift 7207444
  have htrace : WordTrace (prefixWord ++ tailWord_7207444) baseStart_7207444 baseEnd_7207444 := by
    simpa [prefixWord, tailWord_7207444, baseEnd_7207444] using wordTrace_append hprefix tailTrace_7207444
  have hstable : (prefixWord ++ tailWord_7207444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207444).length < 2 ^ (prefixWord ++ tailWord_7207444).sum := by decide
  have hdescent : baseEnd_7207444 < baseStart_7207444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207496 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_7207496 : Nat := 118140960795 + 7207496 * 2 ^ 59
def prefixEnd_7207496 : Nat := 4983230072969 + 3 ^ 40 * 7207496 * 2
def baseEnd_7207496 : Nat := 3700909763358037872453335

theorem tailTrace_7207496 : CollatzResearch.WordTrace tailWord_7207496 prefixEnd_7207496 3700909763358037872453335 := by
  unfold tailWord_7207496
  simp only [CollatzResearch.WordTrace]
  refine ⟨131439487748240204580793171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175252650330986939441057561 131439487748240204580793171)
  ·
    refine ⟨197159231622360306871189757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131439487748240204580793171 197159231622360306871189757)
    ·
      refine ⟨73934711858385115076696159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197159231622360306871189757 73934711858385115076696159)
      ·
        refine ⟨110902067787577672615044239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73934711858385115076696159 110902067787577672615044239)
        ·
          refine ⟨166353101681366508922566359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110902067787577672615044239 166353101681366508922566359)
          ·
            refine ⟨249529652522049763383849539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166353101681366508922566359 249529652522049763383849539)
            ·
              refine ⟨374294478783074645075774309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249529652522049763383849539 374294478783074645075774309)
              ·
                refine ⟨70180214771826495951707683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 374294478783074645075774309 70180214771826495951707683)
                ·
                  refine ⟨105270322157739743927561525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70180214771826495951707683 105270322157739743927561525)
                  ·
                    refine ⟨9869092702288100993208893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105270322157739743927561525 9869092702288100993208893)
                    ·
                      refine ⟨3700909763358037872453335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9869092702288100993208893 3700909763358037872453335)
                      ·
                        rfl

theorem cell23_7207496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_7207496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207496 prefixEnd_7207496 := by exact prefixLift 7207496
  have htrace : WordTrace (prefixWord ++ tailWord_7207496) baseStart_7207496 baseEnd_7207496 := by
    simpa [prefixWord, tailWord_7207496, baseEnd_7207496] using wordTrace_append hprefix tailTrace_7207496
  have hstable : (prefixWord ++ tailWord_7207496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207496).length < 2 ^ (prefixWord ++ tailWord_7207496).sum := by decide
  have hdescent : baseEnd_7207496 < baseStart_7207496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207503 : List Nat := [1, 1, 2, 1, 1, 2, 7, 3, 5]
def baseStart_7207503 : Nat := 118140960795 + 7207503 * 2 ^ 59
def prefixEnd_7207503 : Nat := 4983230072969 + 3 ^ 40 * 7207503 * 2
def baseEnd_7207503 : Nat := 411212595302513260562867

theorem tailTrace_7207503 : CollatzResearch.WordTrace tailWord_7207503 prefixEnd_7207503 411212595302513260562867 := by
  unfold tailWord_7207503
  simp only [CollatzResearch.WordTrace]
  refine ⟨262879230807455049357091163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175252820538303366238060775 262879230807455049357091163)
  ·
    refine ⟨394318846211182574035636745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262879230807455049357091163 394318846211182574035636745)
    ·
      refine ⟨295739134658386930526727559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394318846211182574035636745 295739134658386930526727559)
      ·
        refine ⟨443608701987580395790091339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295739134658386930526727559 443608701987580395790091339)
        ·
          refine ⟨665413052981370593685137009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443608701987580395790091339 665413052981370593685137009)
          ·
            refine ⟨499059789736027945263852757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665413052981370593685137009 499059789736027945263852757)
            ·
              refine ⟨11696713821938154967121549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 499059789736027945263852757 11696713821938154967121549)
              ·
                refine ⟨4386267683226808112670581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11696713821938154967121549 4386267683226808112670581)
                ·
                  refine ⟨411212595302513260562867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4386267683226808112670581 411212595302513260562867)
                  ·
                    rfl

theorem cell23_7207503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 5].length) (baseStart_7207503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207503 prefixEnd_7207503 := by exact prefixLift 7207503
  have htrace : WordTrace (prefixWord ++ tailWord_7207503) baseStart_7207503 baseEnd_7207503 := by
    simpa [prefixWord, tailWord_7207503, baseEnd_7207503] using wordTrace_append hprefix tailTrace_7207503
  have hstable : (prefixWord ++ tailWord_7207503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207503).length < 2 ^ (prefixWord ++ tailWord_7207503).sum := by decide
  have hdescent : baseEnd_7207503 < baseStart_7207503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207523 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 2, 5, 2]
def baseStart_7207523 : Nat := 118140960795 + 7207523 * 2 ^ 59
def prefixEnd_7207523 : Nat := 4983230072969 + 3 ^ 40 * 7207523 * 2
def baseEnd_7207523 : Nat := 3700923627335709266815711

theorem tailTrace_7207523 : CollatzResearch.WordTrace tailWord_7207523 prefixEnd_7207523 3700923627335709266815711 := by
  unfold tailWord_7207523
  simp only [CollatzResearch.WordTrace]
  refine ⟨262879960267382592772819223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175253306844921728515212815 262879960267382592772819223)
  ·
    refine ⟨394319940401073889159228835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262879960267382592772819223 394319940401073889159228835)
    ·
      refine ⟨591479910601610833738843253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394319940401073889159228835 591479910601610833738843253)
      ·
        refine ⟨55451241618901015663016555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 591479910601610833738843253 55451241618901015663016555)
        ·
          refine ⟨83176862428351523494524833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55451241618901015663016555 83176862428351523494524833)
          ·
            refine ⟨62382646821263642620893625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83176862428351523494524833 62382646821263642620893625)
            ·
              refine ⟨46786985115947731965670219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62382646821263642620893625 46786985115947731965670219)
              ·
                refine ⟨70180477673921597948505329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46786985115947731965670219 70180477673921597948505329)
                ·
                  refine ⟨52635358255441198461378997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70180477673921597948505329 52635358255441198461378997)
                  ·
                    refine ⟨4934564836447612355754281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52635358255441198461378997 4934564836447612355754281)
                    ·
                      refine ⟨3700923627335709266815711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4934564836447612355754281 3700923627335709266815711)
                      ·
                        rfl

theorem cell23_7207523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_7207523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207523 prefixEnd_7207523 := by exact prefixLift 7207523
  have htrace : WordTrace (prefixWord ++ tailWord_7207523) baseStart_7207523 baseEnd_7207523 := by
    simpa [prefixWord, tailWord_7207523, baseEnd_7207523] using wordTrace_append hprefix tailTrace_7207523
  have hstable : (prefixWord ++ tailWord_7207523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207523).length < 2 ^ (prefixWord ++ tailWord_7207523).sum := by decide
  have hdescent : baseEnd_7207523 < baseStart_7207523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207570 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_7207570 : Nat := 118140960795 + 7207570 * 2 ^ 59
def prefixEnd_7207570 : Nat := 4983230072969 + 3 ^ 40 * 7207570 * 2
def baseEnd_7207570 : Nat := 3700947760926470582927995

theorem tailTrace_7207570 : CollatzResearch.WordTrace tailWord_7207570 prefixEnd_7207570 3700947760926470582927995 := by
  unfold tailWord_7207570
  simp only [CollatzResearch.WordTrace]
  refine ⟨65720418624553079949945041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175254449665474879866520109 65720418624553079949945041)
  ·
    refine ⟨49290313968414809962458781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65720418624553079949945041 49290313968414809962458781)
    ·
      refine ⟨18483867738155553735922043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49290313968414809962458781 18483867738155553735922043)
      ·
        refine ⟨27725801607233330603883065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18483867738155553735922043 27725801607233330603883065)
        ·
          refine ⟨20794351205424997952912299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27725801607233330603883065 20794351205424997952912299)
          ·
            refine ⟨31191526808137496929368449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20794351205424997952912299 31191526808137496929368449)
            ·
              refine ⟨23393645106103122697026337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31191526808137496929368449 23393645106103122697026337)
              ·
                refine ⟨17545233829577342022769753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23393645106103122697026337 17545233829577342022769753)
                ·
                  refine ⟨13158925372183006517077315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17545233829577342022769753 13158925372183006517077315)
                  ·
                    refine ⟨19738388058274509775615973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13158925372183006517077315 19738388058274509775615973)
                    ·
                      refine ⟨3700947760926470582927995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19738388058274509775615973 3700947760926470582927995)
                      ·
                        rfl

theorem cell23_7207570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_7207570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207570 prefixEnd_7207570 := by exact prefixLift 7207570
  have htrace : WordTrace (prefixWord ++ tailWord_7207570) baseStart_7207570 baseEnd_7207570 := by
    simpa [prefixWord, tailWord_7207570, baseEnd_7207570] using wordTrace_append hprefix tailTrace_7207570
  have hstable : (prefixWord ++ tailWord_7207570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207570).length < 2 ^ (prefixWord ++ tailWord_7207570).sum := by decide
  have hdescent : baseEnd_7207570 < baseStart_7207570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207607 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 2, 2, 3]
def baseStart_7207607 : Nat := 118140960795 + 7207607 * 2 ^ 59
def prefixEnd_7207607 : Nat := 4983230072969 + 3 ^ 40 * 7207607 * 2
def baseEnd_7207607 : Nat := 3700966759710686938165325

theorem tailTrace_7207607 : CollatzResearch.WordTrace tailWord_7207607 prefixEnd_7207607 3700966759710686938165325 := by
  unfold tailWord_7207607
  simp only [CollatzResearch.WordTrace]
  refine ⟨262883023999078275118877075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175255349332718850079251383 262883023999078275118877075)
  ·
    refine ⟨394324535998617412678315613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262883023999078275118877075 394324535998617412678315613)
    ·
      refine ⟨147871700999481529754368355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394324535998617412678315613 147871700999481529754368355)
      ·
        refine ⟨221807551499222294631552533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147871700999481529754368355 221807551499222294631552533)
        ·
          refine ⟨10397228976526045060854025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 221807551499222294631552533 10397228976526045060854025)
          ·
            refine ⟨7797921732394533795640519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10397228976526045060854025 7797921732394533795640519)
            ·
              refine ⟨11696882598591800693460779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7797921732394533795640519 11696882598591800693460779)
              ·
                refine ⟨17545323897887701040191169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11696882598591800693460779 17545323897887701040191169)
                ·
                  refine ⟨13158992923415775780143377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17545323897887701040191169 13158992923415775780143377)
                  ·
                    refine ⟨9869244692561831835107533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13158992923415775780143377 9869244692561831835107533)
                    ·
                      refine ⟨3700966759710686938165325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9869244692561831835107533 3700966759710686938165325)
                      ·
                        rfl

theorem cell23_7207607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_7207607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207607 prefixEnd_7207607 := by exact prefixLift 7207607
  have htrace : WordTrace (prefixWord ++ tailWord_7207607) baseStart_7207607 baseEnd_7207607 := by
    simpa [prefixWord, tailWord_7207607, baseEnd_7207607] using wordTrace_append hprefix tailTrace_7207607
  have hstable : (prefixWord ++ tailWord_7207607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207607).length < 2 ^ (prefixWord ++ tailWord_7207607).sum := by decide
  have hdescent : baseEnd_7207607 < baseStart_7207607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207670 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_7207670 : Nat := 118140960795 + 7207670 * 2 ^ 59
def prefixEnd_7207670 : Nat := 4983230072969 + 3 ^ 40 * 7207670 * 2
def baseEnd_7207670 : Nat := 1233666369663973397225845

theorem tailTrace_7207670 : CollatzResearch.WordTrace tailWord_7207670 prefixEnd_7207670 1233666369663973397225845 := by
  unfold tailWord_7207670
  simp only [CollatzResearch.WordTrace]
  refine ⟨16430332612365627304901279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175256881198566691252280309 16430332612365627304901279)
  ·
    refine ⟨24645498918548440957351919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16430332612365627304901279 24645498918548440957351919)
    ·
      refine ⟨36968248377822661436027879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24645498918548440957351919 36968248377822661436027879)
      ·
        refine ⟨55452372566733992154041819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36968248377822661436027879 55452372566733992154041819)
        ·
          refine ⟨83178558850100988231062729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55452372566733992154041819 83178558850100988231062729)
          ·
            refine ⟨62383919137575741173297047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83178558850100988231062729 62383919137575741173297047)
            ·
              refine ⟨93575878706363611759945571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62383919137575741173297047 93575878706363611759945571)
              ·
                refine ⟨140363818059545417639918357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93575878706363611759945571 140363818059545417639918357)
                ·
                  refine ⟨6579553971541191451871173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140363818059545417639918357 6579553971541191451871173)
                  ·
                    refine ⟨1233666369663973397225845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6579553971541191451871173 1233666369663973397225845)
                    ·
                      rfl

theorem cell23_7207670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_7207670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207670 prefixEnd_7207670 := by exact prefixLift 7207670
  have htrace : WordTrace (prefixWord ++ tailWord_7207670) baseStart_7207670 baseEnd_7207670 := by
    simpa [prefixWord, tailWord_7207670, baseEnd_7207670] using wordTrace_append hprefix tailTrace_7207670
  have hstable : (prefixWord ++ tailWord_7207670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207670).length < 2 ^ (prefixWord ++ tailWord_7207670).sum := by decide
  have hdescent : baseEnd_7207670 < baseStart_7207670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207673 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 1, 2, 4]
def baseStart_7207673 : Nat := 118140960795 + 7207673 * 2 ^ 59
def prefixEnd_7207673 : Nat := 4983230072969 + 3 ^ 40 * 7207673 * 2
def baseEnd_7207673 : Nat := 3701000649433883679940021

theorem tailTrace_7207673 : CollatzResearch.WordTrace tailWord_7207673 prefixEnd_7207673 3701000649433883679940021 := by
  unfold tailWord_7207673
  simp only [CollatzResearch.WordTrace]
  refine ⟨262885431216839168390779673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175256954144559445593853115 262885431216839168390779673)
  ·
    refine ⟨197164073412629376293084755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262885431216839168390779673 197164073412629376293084755)
    ·
      refine ⟨295746110118944064439627133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197164073412629376293084755 295746110118944064439627133)
      ·
        refine ⟨110904791294604024164860175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295746110118944064439627133 110904791294604024164860175)
        ·
          refine ⟨166357186941906036247290263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110904791294604024164860175 166357186941906036247290263)
          ·
            refine ⟨249535780412859054370935395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166357186941906036247290263 249535780412859054370935395)
            ·
              refine ⟨374303670619288581556403093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249535780412859054370935395 374303670619288581556403093)
              ·
                refine ⟨17545484560279152260456395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 374303670619288581556403093 17545484560279152260456395)
                ·
                  refine ⟨26318226840418728390684593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17545484560279152260456395 26318226840418728390684593)
                  ·
                    refine ⟨19738670130314046293013445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26318226840418728390684593 19738670130314046293013445)
                    ·
                      refine ⟨3701000649433883679940021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19738670130314046293013445 3701000649433883679940021)
                      ·
                        rfl

theorem cell23_7207673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_7207673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207673 prefixEnd_7207673 := by exact prefixLift 7207673
  have htrace : WordTrace (prefixWord ++ tailWord_7207673) baseStart_7207673 baseEnd_7207673 := by
    simpa [prefixWord, tailWord_7207673, baseEnd_7207673] using wordTrace_append hprefix tailTrace_7207673
  have hstable : (prefixWord ++ tailWord_7207673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207673).length < 2 ^ (prefixWord ++ tailWord_7207673).sum := by decide
  have hdescent : baseEnd_7207673 < baseStart_7207673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207714 : List Nat := [3, 3, 1, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_7207714 : Nat := 118140960795 + 7207714 * 2 ^ 59
def prefixEnd_7207714 : Nat := 4983230072969 + 3 ^ 40 * 7207714 * 2
def baseEnd_7207714 : Nat := 3701021702140718019527333

theorem tailTrace_7207714 : CollatzResearch.WordTrace tailWord_7207714 prefixEnd_7207714 3701021702140718019527333 := by
  unfold tailWord_7207714
  simp only [CollatzResearch.WordTrace]
  refine ⟨65721731652422658098255549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175257951073127088262014797 65721731652422658098255549)
  ·
    refine ⟨24645649369658496786845831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65721731652422658098255549 24645649369658496786845831)
    ·
      refine ⟨36968474054487745180268747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24645649369658496786845831 36968474054487745180268747)
      ·
        refine ⟨55452711081731617770403121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36968474054487745180268747 55452711081731617770403121)
        ·
          refine ⟨41589533311298713327802341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55452711081731617770403121 41589533311298713327802341)
          ·
            refine ⟨7798037495868508748962939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41589533311298713327802341 7798037495868508748962939)
            ·
              refine ⟨11697056243802763123444409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7798037495868508748962939 11697056243802763123444409)
              ·
                refine ⟨8772792182852072342583307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11697056243802763123444409 8772792182852072342583307)
                ·
                  refine ⟨13159188274278108513874961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8772792182852072342583307 13159188274278108513874961)
                  ·
                    refine ⟨9869391205708581385406221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13159188274278108513874961 9869391205708581385406221)
                    ·
                      refine ⟨3701021702140718019527333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9869391205708581385406221 3701021702140718019527333)
                      ·
                        rfl

theorem cell23_7207714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_7207714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207714 prefixEnd_7207714 := by exact prefixLift 7207714
  have htrace : WordTrace (prefixWord ++ tailWord_7207714) baseStart_7207714 baseEnd_7207714 := by
    simpa [prefixWord, tailWord_7207714, baseEnd_7207714] using wordTrace_append hprefix tailTrace_7207714
  have hstable : (prefixWord ++ tailWord_7207714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207714).length < 2 ^ (prefixWord ++ tailWord_7207714).sum := by decide
  have hdescent : baseEnd_7207714 < baseStart_7207714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207767 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 1, 4, 2]
def baseStart_7207767 : Nat := 118140960795 + 7207767 * 2 ^ 59
def prefixEnd_7207767 : Nat := 4983230072969 + 3 ^ 40 * 7207767 * 2
def baseEnd_7207767 : Nat := 3701048916615406312164589

theorem tailTrace_7207767 : CollatzResearch.WordTrace tailWord_7207767 prefixEnd_7207767 3701048916615406312164589 := by
  unfold tailWord_7207767
  simp only [CollatzResearch.WordTrace]
  refine ⟨262888859678498622444701555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175259239785665748296467703 262888859678498622444701555)
  ·
    refine ⟨394333289517747933667052333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262888859678498622444701555 394333289517747933667052333)
    ·
      refine ⟨147874983569155475125144625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394333289517747933667052333 147874983569155475125144625)
      ·
        refine ⟨110906237676866606343858469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147874983569155475125144625 110906237676866606343858469)
        ·
          refine ⟨20794919564412488689473463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110906237676866606343858469 20794919564412488689473463)
          ·
            refine ⟨31192379346618733034210195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20794919564412488689473463 31192379346618733034210195)
            ·
              refine ⟨46788569019928099551315293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31192379346618733034210195 46788569019928099551315293)
              ·
                refine ⟨17545713382473037331743235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46788569019928099551315293 17545713382473037331743235)
                ·
                  refine ⟨26318570073709555997614853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17545713382473037331743235 26318570073709555997614853)
                  ·
                    refine ⟨4934731888820541749552785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26318570073709555997614853 4934731888820541749552785)
                    ·
                      refine ⟨3701048916615406312164589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4934731888820541749552785 3701048916615406312164589)
                      ·
                        rfl

theorem cell23_7207767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_7207767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207767 prefixEnd_7207767 := by exact prefixLift 7207767
  have htrace : WordTrace (prefixWord ++ tailWord_7207767) baseStart_7207767 baseEnd_7207767 := by
    simpa [prefixWord, tailWord_7207767, baseEnd_7207767] using wordTrace_append hprefix tailTrace_7207767
  have hstable : (prefixWord ++ tailWord_7207767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207767).length < 2 ^ (prefixWord ++ tailWord_7207767).sum := by decide
  have hdescent : baseEnd_7207767 < baseStart_7207767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207801 : List Nat := [1, 2, 1, 3, 2, 5, 1, 2, 2, 2, 2]
def baseStart_7207801 : Nat := 118140960795 + 7207801 * 2 ^ 59
def prefixEnd_7207801 : Nat := 4983230072969 + 3 ^ 40 * 7207801 * 2
def baseEnd_7207801 : Nat := 3701066374957659179139433

theorem tailTrace_7207801 : CollatzResearch.WordTrace tailWord_7207801 prefixEnd_7207801 3701066374957659179139433 := by
  unfold tailWord_7207801
  simp only [CollatzResearch.WordTrace]
  refine ⟨262890099760375446251439257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175260066506916964167626171 262890099760375446251439257)
  ·
    refine ⟨197167574820281584688579443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262890099760375446251439257 197167574820281584688579443)
    ·
      refine ⟨295751362230422377032869165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197167574820281584688579443 295751362230422377032869165)
      ·
        refine ⟨110906760836408391387325937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295751362230422377032869165 110906760836408391387325937)
        ·
          refine ⟨83180070627306293540494453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110906760836408391387325937 83180070627306293540494453)
          ·
            refine ⟨7798131621309965019421355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83180070627306293540494453 7798131621309965019421355)
            ·
              refine ⟨11697197431964947529132033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7798131621309965019421355 11697197431964947529132033)
              ·
                refine ⟨8772898073973710646849025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11697197431964947529132033 8772898073973710646849025)
                ·
                  refine ⟨6579673555480282985136769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8772898073973710646849025 6579673555480282985136769)
                  ·
                    refine ⟨4934755166610212238852577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6579673555480282985136769 4934755166610212238852577)
                    ·
                      refine ⟨3701066374957659179139433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4934755166610212238852577 3701066374957659179139433)
                      ·
                        rfl

theorem cell23_7207801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_7207801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207801 prefixEnd_7207801 := by exact prefixLift 7207801
  have htrace : WordTrace (prefixWord ++ tailWord_7207801) baseStart_7207801 baseEnd_7207801 := by
    simpa [prefixWord, tailWord_7207801, baseEnd_7207801] using wordTrace_append hprefix tailTrace_7207801
  have hstable : (prefixWord ++ tailWord_7207801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207801).length < 2 ^ (prefixWord ++ tailWord_7207801).sum := by decide
  have hdescent : baseEnd_7207801 < baseStart_7207801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207818 : List Nat := [3, 1, 2, 4, 1, 2, 3, 1, 2, 2, 2]
def baseStart_7207818 : Nat := 118140960795 + 7207818 * 2 ^ 59
def prefixEnd_7207818 : Nat := 4983230072969 + 3 ^ 40 * 7207818 * 2
def baseEnd_7207818 : Nat := 3701075104128785612626855

theorem tailTrace_7207818 : CollatzResearch.WordTrace tailWord_7207818 prefixEnd_7207818 3701075104128785612626855 := by
  unfold tailWord_7207818
  simp only [CollatzResearch.WordTrace]
  refine ⟨65722679950328464538702027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175260479867542572103205405 65722679950328464538702027)
  ·
    refine ⟨98584019925492696808053041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65722679950328464538702027 98584019925492696808053041)
    ·
      refine ⟨73938014944119522606039781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98584019925492696808053041 73938014944119522606039781)
      ·
        refine ⟨13863377802022410488632459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73938014944119522606039781 13863377802022410488632459)
        ·
          refine ⟨20795066703033615732948689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13863377802022410488632459 20795066703033615732948689)
          ·
            refine ⟨15596300027275211799711517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20795066703033615732948689 15596300027275211799711517)
            ·
              refine ⟨5848612510228204424891819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15596300027275211799711517 5848612510228204424891819)
              ·
                refine ⟨8772918765342306637337729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5848612510228204424891819 8772918765342306637337729)
                ·
                  refine ⟨6579689074006729978003297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8772918765342306637337729 6579689074006729978003297)
                  ·
                    refine ⟨4934766805505047483502473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6579689074006729978003297 4934766805505047483502473)
                    ·
                      refine ⟨3701075104128785612626855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4934766805505047483502473 3701075104128785612626855)
                      ·
                        rfl

theorem cell23_7207818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_7207818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207818 prefixEnd_7207818 := by exact prefixLift 7207818
  have htrace : WordTrace (prefixWord ++ tailWord_7207818) baseStart_7207818 baseEnd_7207818 := by
    simpa [prefixWord, tailWord_7207818, baseEnd_7207818] using wordTrace_append hprefix tailTrace_7207818
  have hstable : (prefixWord ++ tailWord_7207818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207818).length < 2 ^ (prefixWord ++ tailWord_7207818).sum := by decide
  have hdescent : baseEnd_7207818 < baseStart_7207818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207833 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 1, 10]
def baseStart_7207833 : Nat := 118140960795 + 7207833 * 2 ^ 59
def prefixEnd_7207833 : Nat := 4983230072969 + 3 ^ 40 * 7207833 * 2
def baseEnd_7207833 : Nat := 1233694268779534351313095

theorem tailTrace_7207833 : CollatzResearch.WordTrace tailWord_7207833 prefixEnd_7207833 1233694268779534351313095 := by
  unfold tailWord_7207833
  simp only [CollatzResearch.WordTrace]
  refine ⟨262891266896259515716604153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175260844597506343811069435 262891266896259515716604153)
  ·
    refine ⟨197168450172194636787453115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262891266896259515716604153 197168450172194636787453115)
    ·
      refine ⟨295752675258291955181179673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197168450172194636787453115 295752675258291955181179673)
      ·
        refine ⟨221814506443718966385884755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295752675258291955181179673 221814506443718966385884755)
        ·
          refine ⟨332721759665578449578827133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221814506443718966385884755 332721759665578449578827133)
          ·
            refine ⟨124770659874591918592060175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332721759665578449578827133 124770659874591918592060175)
            ·
              refine ⟨187155989811887877888090263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124770659874591918592060175 187155989811887877888090263)
              ·
                refine ⟨280733984717831816832135395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187155989811887877888090263 280733984717831816832135395)
                ·
                  refine ⟨421100977076747725248203093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 280733984717831816832135395 421100977076747725248203093)
                  ·
                    refine ⟨1233694268779534351313095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 421100977076747725248203093 1233694268779534351313095)
                    ·
                      rfl

theorem cell23_7207833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_7207833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207833 prefixEnd_7207833 := by exact prefixLift 7207833
  have htrace : WordTrace (prefixWord ++ tailWord_7207833) baseStart_7207833 baseEnd_7207833 := by
    simpa [prefixWord, tailWord_7207833, baseEnd_7207833] using wordTrace_append hprefix tailTrace_7207833
  have hstable : (prefixWord ++ tailWord_7207833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207833).length < 2 ^ (prefixWord ++ tailWord_7207833).sum := by decide
  have hdescent : baseEnd_7207833 < baseStart_7207833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207840 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 4]
def baseStart_7207840 : Nat := 118140960795 + 7207840 * 2 ^ 59
def prefixEnd_7207840 : Nat := 4983230072969 + 3 ^ 40 * 7207840 * 2
def baseEnd_7207840 : Nat := 3701086400703184526551753

theorem tailTrace_7207840 : CollatzResearch.WordTrace tailWord_7207840 prefixEnd_7207840 3701086400703184526551753 := by
  unfold tailWord_7207840
  simp only [CollatzResearch.WordTrace]
  refine ⟨131445761103617077956054487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175261014804822770608072649 131445761103617077956054487)
  ·
    refine ⟨197168641655425616934081731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131445761103617077956054487 197168641655425616934081731)
    ·
      refine ⟨295752962483138425401122597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197168641655425616934081731 295752962483138425401122597)
      ·
        refine ⟨55453680465588454762710487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295752962483138425401122597 55453680465588454762710487)
        ·
          refine ⟨83180520698382682144065731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55453680465588454762710487 83180520698382682144065731)
          ·
            refine ⟨124770781047574023216098597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83180520698382682144065731 124770781047574023216098597)
            ·
              refine ⟨23394521446420129353018487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124770781047574023216098597 23394521446420129353018487)
              ·
                refine ⟨35091782169630194029527731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23394521446420129353018487 35091782169630194029527731)
                ·
                  refine ⟨52637673254445291044291597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35091782169630194029527731 52637673254445291044291597)
                  ·
                    refine ⟨19739127470416984141609349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52637673254445291044291597 19739127470416984141609349)
                    ·
                      refine ⟨3701086400703184526551753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19739127470416984141609349 3701086400703184526551753)
                      ·
                        rfl

theorem cell23_7207840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_7207840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207840 prefixEnd_7207840 := by exact prefixLift 7207840
  have htrace : WordTrace (prefixWord ++ tailWord_7207840) baseStart_7207840 baseEnd_7207840 := by
    simpa [prefixWord, tailWord_7207840, baseEnd_7207840] using wordTrace_append hprefix tailTrace_7207840
  have hstable : (prefixWord ++ tailWord_7207840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207840).length < 2 ^ (prefixWord ++ tailWord_7207840).sum := by decide
  have hdescent : baseEnd_7207840 < baseStart_7207840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207947 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 4]
def baseStart_7207947 : Nat := 118140960795 + 7207947 * 2 ^ 59
def prefixEnd_7207947 : Nat := 4983230072969 + 3 ^ 40 * 7207947 * 2
def baseEnd_7207947 : Nat := 3701141343133215607913761

theorem tailTrace_7207947 : CollatzResearch.WordTrace tailWord_7207947 prefixEnd_7207947 3701141343133215607913761 := by
  unfold tailWord_7207947
  simp only [CollatzResearch.WordTrace]
  refine ⟨262895424817846513186254095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175263616545231008790836063 262895424817846513186254095)
  ·
    refine ⟨394343137226769769779381143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262895424817846513186254095 394343137226769769779381143)
    ·
      refine ⟨591514705840154654669071715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394343137226769769779381143 591514705840154654669071715)
      ·
        refine ⟨887272058760231982003607573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591514705840154654669071715 887272058760231982003607573)
        ·
          refine ⟨41590877754385874156419105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 887272058760231982003607573 41590877754385874156419105)
          ·
            refine ⟨31193158315789405617314329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41590877754385874156419105 31193158315789405617314329)
            ·
              refine ⟨23394868736842054212985747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31193158315789405617314329 23394868736842054212985747)
              ·
                refine ⟨35092303105263081319478621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23394868736842054212985747 35092303105263081319478621)
                ·
                  refine ⟨13159613664473655494804483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35092303105263081319478621 13159613664473655494804483)
                  ·
                    refine ⟨19739420496710483242206725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13159613664473655494804483 19739420496710483242206725)
                    ·
                      refine ⟨3701141343133215607913761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19739420496710483242206725 3701141343133215607913761)
                      ·
                        rfl

theorem cell23_7207947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 4].length) (baseStart_7207947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207947 prefixEnd_7207947 := by exact prefixLift 7207947
  have htrace : WordTrace (prefixWord ++ tailWord_7207947) baseStart_7207947 baseEnd_7207947 := by
    simpa [prefixWord, tailWord_7207947, baseEnd_7207947] using wordTrace_append hprefix tailTrace_7207947
  have hstable : (prefixWord ++ tailWord_7207947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207947).length < 2 ^ (prefixWord ++ tailWord_7207947).sum := by decide
  have hdescent : baseEnd_7207947 < baseStart_7207947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207957 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 1, 6]
def baseStart_7207957 : Nat := 118140960795 + 7207957 * 2 ^ 59
def prefixEnd_7207957 : Nat := 4983230072969 + 3 ^ 40 * 7207957 * 2
def baseEnd_7207957 : Nat := 1233715492646586856262905

theorem tailTrace_7207957 : CollatzResearch.WordTrace tailWord_7207957 prefixEnd_7207957 1233715492646586856262905 := by
  unfold tailWord_7207957
  simp only [CollatzResearch.WordTrace]
  refine ⟨262895789547810284894118125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175263859698540189929412083 262895789547810284894118125)
  ·
    refine ⟨98585921080428856835294297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262895789547810284894118125 98585921080428856835294297)
    ·
      refine ⟨73939440810321642626470723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98585921080428856835294297 73939440810321642626470723)
      ·
        refine ⟨110909161215482463939706085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73939440810321642626470723 110909161215482463939706085)
        ·
          refine ⟨20795467727902961988694891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110909161215482463939706085 20795467727902961988694891)
          ·
            refine ⟨31193201591854442983042337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20795467727902961988694891 31193201591854442983042337)
            ·
              refine ⟨23394901193890832237281753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31193201591854442983042337 23394901193890832237281753)
              ·
                refine ⟨17546175895418124177961315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23394901193890832237281753 17546175895418124177961315)
                ·
                  refine ⟨26319263843127186266941973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17546175895418124177961315 26319263843127186266941973)
                  ·
                    refine ⟨1233715492646586856262905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26319263843127186266941973 1233715492646586856262905)
                    ·
                      rfl

theorem cell23_7207957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_7207957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207957 prefixEnd_7207957 := by exact prefixLift 7207957
  have htrace : WordTrace (prefixWord ++ tailWord_7207957) baseStart_7207957 baseEnd_7207957 := by
    simpa [prefixWord, tailWord_7207957, baseEnd_7207957] using wordTrace_append hprefix tailTrace_7207957
  have hstable : (prefixWord ++ tailWord_7207957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207957).length < 2 ^ (prefixWord ++ tailWord_7207957).sum := by decide
  have hdescent : baseEnd_7207957 < baseStart_7207957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207998 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_7207998 : Nat := 118140960795 + 7207998 * 2 ^ 59
def prefixEnd_7207998 : Nat := 4983230072969 + 3 ^ 40 * 7207998 * 2
def baseEnd_7207998 : Nat := 3701167530646594908376027

theorem tailTrace_7207998 : CollatzResearch.WordTrace tailWord_7207998 prefixEnd_7207998 3701167530646594908376027 := by
  unfold tailWord_7207998
  simp only [CollatzResearch.WordTrace]
  refine ⟨32862160617582718612045081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175264856627107832597573765 32862160617582718612045081)
  ·
    refine ⟨24646620463187038959033811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32862160617582718612045081 24646620463187038959033811)
    ·
      refine ⟨36969930694780558438550717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24646620463187038959033811 36969930694780558438550717)
      ·
        refine ⟨13863724010542709414456519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36969930694780558438550717 13863724010542709414456519)
        ·
          refine ⟨20795586015814064121684779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13863724010542709414456519 20795586015814064121684779)
          ·
            refine ⟨31193379023721096182527169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20795586015814064121684779 31193379023721096182527169)
            ·
              refine ⟨23395034267790822136895377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31193379023721096182527169 23395034267790822136895377)
              ·
                refine ⟨17546275700843116602671533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23395034267790822136895377 17546275700843116602671533)
                ·
                  refine ⟨6579853387816168726001825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17546275700843116602671533 6579853387816168726001825)
                  ·
                    refine ⟨4934890040862126544501369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6579853387816168726001825 4934890040862126544501369)
                    ·
                      refine ⟨3701167530646594908376027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4934890040862126544501369 3701167530646594908376027)
                      ·
                        rfl

theorem cell23_7207998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_7207998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7207998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7207998 prefixEnd_7207998 := by exact prefixLift 7207998
  have htrace : WordTrace (prefixWord ++ tailWord_7207998) baseStart_7207998 baseEnd_7207998 := by
    simpa [prefixWord, tailWord_7207998, baseEnd_7207998] using wordTrace_append hprefix tailTrace_7207998
  have hstable : (prefixWord ++ tailWord_7207998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207998).length < 2 ^ (prefixWord ++ tailWord_7207998).sum := by decide
  have hdescent : baseEnd_7207998 < baseStart_7207998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208014 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_7208014 : Nat := 118140960795 + 7208014 * 2 ^ 59
def prefixEnd_7208014 : Nat := 4983230072969 + 3 ^ 40 * 7208014 * 2
def baseEnd_7208014 : Nat := 3701175746337066845775953

theorem tailTrace_7208014 : CollatzResearch.WordTrace tailWord_7208014 prefixEnd_7208014 3701175746337066845775953 := by
  unfold tailWord_7208014
  simp only [CollatzResearch.WordTrace]
  refine ⟨32862233563575472953617887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175265245672402522419295397 32862233563575472953617887)
  ·
    refine ⟨49293350345363209430426831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32862233563575472953617887 49293350345363209430426831)
    ·
      refine ⟨73940025518044814145640247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49293350345363209430426831 73940025518044814145640247)
      ·
        refine ⟨110910038277067221218460371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73940025518044814145640247 110910038277067221218460371)
        ·
          refine ⟨166365057415600831827690557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110910038277067221218460371 166365057415600831827690557)
          ·
            refine ⟨62386896530850311935383959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166365057415600831827690557 62386896530850311935383959)
            ·
              refine ⟨93580344796275467903075939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62386896530850311935383959 93580344796275467903075939)
              ·
                refine ⟨140370517194413201854613909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93580344796275467903075939 140370517194413201854613909)
                ·
                  refine ⟨6579867993488118836935027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140370517194413201854613909 6579867993488118836935027)
                  ·
                    refine ⟨9869801990232178255402541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6579867993488118836935027 9869801990232178255402541)
                    ·
                      refine ⟨3701175746337066845775953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9869801990232178255402541 3701175746337066845775953)
                      ·
                        rfl

theorem cell23_7208014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_7208014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208014 prefixEnd_7208014 := by exact prefixLift 7208014
  have htrace : WordTrace (prefixWord ++ tailWord_7208014) baseStart_7208014 baseEnd_7208014 := by
    simpa [prefixWord, tailWord_7208014, baseEnd_7208014] using wordTrace_append hprefix tailTrace_7208014
  have hstable : (prefixWord ++ tailWord_7208014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208014).length < 2 ^ (prefixWord ++ tailWord_7208014).sum := by decide
  have hdescent : baseEnd_7208014 < baseStart_7208014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208037 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_7208037 : Nat := 118140960795 + 7208037 * 2 ^ 59
def prefixEnd_7208037 : Nat := 4983230072969 + 3 ^ 40 * 7208037 * 2
def baseEnd_7208037 : Nat := 3701187556392120255788347

theorem tailTrace_7208037 : CollatzResearch.WordTrace tailWord_7208037 prefixEnd_7208037 3701187556392120255788347 := by
  unfold tailWord_7208037
  simp only [CollatzResearch.WordTrace]
  refine ⟨262898707387520458557030365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175265804925013639038020243 262898707387520458557030365)
  ·
    refine ⟨98587015270320171958886387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262898707387520458557030365 98587015270320171958886387)
    ·
      refine ⟨147880522905480257938329581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98587015270320171958886387 147880522905480257938329581)
      ·
        refine ⟨55455196089555096726873593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147880522905480257938329581 55455196089555096726873593)
        ·
          refine ⟨41591397067166322545155195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55455196089555096726873593 41591397067166322545155195)
          ·
            refine ⟨62387095600749483817732793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41591397067166322545155195 62387095600749483817732793)
            ·
              refine ⟨46790321700562112863299595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62387095600749483817732793 46790321700562112863299595)
              ·
                refine ⟨70185482550843169294949393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46790321700562112863299595 70185482550843169294949393)
                ·
                  refine ⟨52639111913132376971212045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70185482550843169294949393 52639111913132376971212045)
                  ·
                    refine ⟨19739666967424641364204517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52639111913132376971212045 19739666967424641364204517)
                    ·
                      refine ⟨3701187556392120255788347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19739666967424641364204517 3701187556392120255788347)
                      ·
                        rfl

theorem cell23_7208037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_7208037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208037 prefixEnd_7208037 := by exact prefixLift 7208037
  have htrace : WordTrace (prefixWord ++ tailWord_7208037) baseStart_7208037 baseEnd_7208037 := by
    simpa [prefixWord, tailWord_7208037, baseEnd_7208037] using wordTrace_append hprefix tailTrace_7208037
  have hstable : (prefixWord ++ tailWord_7208037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208037).length < 2 ^ (prefixWord ++ tailWord_7208037).sum := by decide
  have hdescent : baseEnd_7208037 < baseStart_7208037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208088 : List Nat := [2, 1, 2, 4, 2, 1, 1, 4, 2, 2, 2]
def baseStart_7208088 : Nat := 118140960795 + 7208088 * 2 ^ 59
def prefixEnd_7208088 : Nat := 4983230072969 + 3 ^ 40 * 7208088 * 2
def baseEnd_7208088 : Nat := 3701213743905499556250613

theorem tailTrace_7208088 : CollatzResearch.WordTrace tailWord_7208088 prefixEnd_7208088 3701213743905499556250613 := by
  unfold tailWord_7208088
  simp only [CollatzResearch.WordTrace]
  refine ⟨131450283755167847133568459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175267045006890462844757945 131450283755167847133568459)
  ·
    refine ⟨197175425632751770700352689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131450283755167847133568459 197175425632751770700352689)
    ·
      refine ⟨147881569224563828025264517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197175425632751770700352689 147881569224563828025264517)
      ·
        refine ⟨27727794229605717754737097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147881569224563828025264517 27727794229605717754737097)
        ·
          refine ⟨20795845672204288316052823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27727794229605717754737097 20795845672204288316052823)
          ·
            refine ⟨31193768508306432474079235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20795845672204288316052823 31193768508306432474079235)
            ·
              refine ⟨46790652762459648711118853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31193768508306432474079235 46790652762459648711118853)
              ·
                refine ⟨8773247392961184133334785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46790652762459648711118853 8773247392961184133334785)
                ·
                  refine ⟨6579935544720888100001089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8773247392961184133334785 6579935544720888100001089)
                  ·
                    refine ⟨4934951658540666075000817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6579935544720888100001089 4934951658540666075000817)
                    ·
                      refine ⟨3701213743905499556250613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4934951658540666075000817 3701213743905499556250613)
                      ·
                        rfl

theorem cell23_7208088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_7208088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208088 prefixEnd_7208088 := by exact prefixLift 7208088
  have htrace : WordTrace (prefixWord ++ tailWord_7208088) baseStart_7208088 baseEnd_7208088 := by
    simpa [prefixWord, tailWord_7208088, baseEnd_7208088] using wordTrace_append hprefix tailTrace_7208088
  have hstable : (prefixWord ++ tailWord_7208088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208088).length < 2 ^ (prefixWord ++ tailWord_7208088).sum := by decide
  have hdescent : baseEnd_7208088 < baseStart_7208088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208124 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 1, 7]
def baseStart_7208124 : Nat := 118140960795 + 7208124 * 2 ^ 59
def prefixEnd_7208124 : Nat := 4983230072969 + 3 ^ 40 * 7208124 * 2
def baseEnd_7208124 : Nat := 1233744076403020471800149

theorem tailTrace_7208124 : CollatzResearch.WordTrace tailWord_7208124 prefixEnd_7208124 1233744076403020471800149 := by
  unfold tailWord_7208124
  simp only [CollatzResearch.WordTrace]
  refine ⟨131450940269102636207723713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175267920358803514943631617 131450940269102636207723713)
  ·
    refine ⟨98588205201826977155792785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131450940269102636207723713 98588205201826977155792785)
    ·
      refine ⟨73941153901370232866844589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98588205201826977155792785 73941153901370232866844589)
      ·
        refine ⟨27727932713013837325066721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73941153901370232866844589 27727932713013837325066721)
        ·
          refine ⟨20795949534760377993800041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27727932713013837325066721 20795949534760377993800041)
          ·
            refine ⟨15596962151070283495350031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20795949534760377993800041 15596962151070283495350031)
            ·
              refine ⟨23395443226605425243025047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15596962151070283495350031 23395443226605425243025047)
              ·
                refine ⟨35093164839908137864537571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23395443226605425243025047 35093164839908137864537571)
                ·
                  refine ⟨52639747259862206796806357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35093164839908137864537571 52639747259862206796806357)
                  ·
                    refine ⟨1233744076403020471800149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52639747259862206796806357 1233744076403020471800149)
                    ·
                      rfl

theorem cell23_7208124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_7208124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208124 prefixEnd_7208124 := by exact prefixLift 7208124
  have htrace : WordTrace (prefixWord ++ tailWord_7208124) baseStart_7208124 baseEnd_7208124 := by
    simpa [prefixWord, tailWord_7208124, baseEnd_7208124] using wordTrace_append hprefix tailTrace_7208124
  have hstable : (prefixWord ++ tailWord_7208124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208124).length < 2 ^ (prefixWord ++ tailWord_7208124).sum := by decide
  have hdescent : baseEnd_7208124 < baseStart_7208124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208161 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 2, 4, 2]
def baseStart_7208161 : Nat := 118140960795 + 7208161 * 2 ^ 59
def prefixEnd_7208161 : Nat := 4983230072969 + 3 ^ 40 * 7208161 * 2
def baseEnd_7208161 : Nat := 3701251227993277770637777

theorem tailTrace_7208161 : CollatzResearch.WordTrace tailWord_7208161 prefixEnd_7208161 3701251227993277770637777 := by
  unfold tailWord_7208161
  simp only [CollatzResearch.WordTrace]
  refine ⟨262903230039071227734544337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175268820026047485156362891 262903230039071227734544337)
  ·
    refine ⟨197177422529303420800908253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262903230039071227734544337 197177422529303420800908253)
    ·
      refine ⟨73941533448488782800340595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197177422529303420800908253 73941533448488782800340595)
      ·
        refine ⟨110912300172733174200510893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73941533448488782800340595 110912300172733174200510893)
        ·
          refine ⟨41592112564774940325191585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110912300172733174200510893 41592112564774940325191585)
          ·
            refine ⟨31194084423581205243893689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41592112564774940325191585 31194084423581205243893689)
            ·
              refine ⟨23395563317685903932920267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31194084423581205243893689 23395563317685903932920267)
              ·
                refine ⟨35093344976528855899380401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23395563317685903932920267 35093344976528855899380401)
                ·
                  refine ⟨26320008732396641924535301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35093344976528855899380401 26320008732396641924535301)
                  ·
                    refine ⟨4935001637324370360850369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26320008732396641924535301 4935001637324370360850369)
                    ·
                      refine ⟨3701251227993277770637777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4935001637324370360850369 3701251227993277770637777)
                      ·
                        rfl

theorem cell23_7208161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_7208161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208161 prefixEnd_7208161 := by exact prefixLift 7208161
  have htrace : WordTrace (prefixWord ++ tailWord_7208161) baseStart_7208161 baseEnd_7208161 := by
    simpa [prefixWord, tailWord_7208161, baseEnd_7208161] using wordTrace_append hprefix tailTrace_7208161
  have hstable : (prefixWord ++ tailWord_7208161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208161).length < 2 ^ (prefixWord ++ tailWord_7208161).sum := by decide
  have hdescent : baseEnd_7208161 < baseStart_7208161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208164 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_7208164 : Nat := 118140960795 + 7208164 * 2 ^ 59
def prefixEnd_7208164 : Nat := 4983230072969 + 3 ^ 40 * 7208164 * 2
def baseEnd_7208164 : Nat := 3701252768435241258900263

theorem tailTrace_7208164 : CollatzResearch.WordTrace tailWord_7208164 prefixEnd_7208164 3701252768435241258900263 := by
  unfold tailWord_7208164
  simp only [CollatzResearch.WordTrace]
  refine ⟨131451669729030179623451773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175268892972040239497935697 131451669729030179623451773)
  ·
    refine ⟨49294376148386317358794415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131451669729030179623451773 49294376148386317358794415)
    ·
      refine ⟨73941564222579476038191623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49294376148386317358794415 73941564222579476038191623)
      ·
        refine ⟨110912346333869214057287435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73941564222579476038191623 110912346333869214057287435)
        ·
          refine ⟨166368519500803821085931153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110912346333869214057287435 166368519500803821085931153)
          ·
            refine ⟨124776389625602865814448365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166368519500803821085931153 124776389625602865814448365)
            ·
              refine ⟨46791146109601074680418137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124776389625602865814448365 46791146109601074680418137)
              ·
                refine ⟨35093359582200806010313603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46791146109601074680418137 35093359582200806010313603)
                ·
                  refine ⟨52640039373301209015470405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35093359582200806010313603 52640039373301209015470405)
                  ·
                    refine ⟨9870007382493976690400701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52640039373301209015470405 9870007382493976690400701)
                    ·
                      refine ⟨3701252768435241258900263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9870007382493976690400701 3701252768435241258900263)
                      ·
                        rfl

theorem cell23_7208164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_7208164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208164 prefixEnd_7208164 := by exact prefixLift 7208164
  have htrace : WordTrace (prefixWord ++ tailWord_7208164) baseStart_7208164 baseEnd_7208164 := by
    simpa [prefixWord, tailWord_7208164, baseEnd_7208164] using wordTrace_append hprefix tailTrace_7208164
  have hstable : (prefixWord ++ tailWord_7208164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208164).length < 2 ^ (prefixWord ++ tailWord_7208164).sum := by decide
  have hdescent : baseEnd_7208164 < baseStart_7208164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208207 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 7]
def baseStart_7208207 : Nat := 118140960795 + 7208207 * 2 ^ 59
def prefixEnd_7208207 : Nat := 4983230072969 + 3 ^ 40 * 7208207 * 2
def baseEnd_7208207 : Nat := 3701274848103384590662565

theorem tailTrace_7208207 : CollatzResearch.WordTrace tailWord_7208207 prefixEnd_7208207 3701274848103384590662565 := by
  unfold tailWord_7208207
  simp only [CollatzResearch.WordTrace]
  refine ⟨262904907796904577590718875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175269938531269718393812583 262904907796904577590718875)
  ·
    refine ⟨394357361695356866386078313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262904907796904577590718875 394357361695356866386078313)
    ·
      refine ⟨295768021271517649789558735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394357361695356866386078313 295768021271517649789558735)
      ·
        refine ⟨443652031907276474684338103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295768021271517649789558735 443652031907276474684338103)
        ·
          refine ⟨665478047860914712026507155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443652031907276474684338103 665478047860914712026507155)
          ·
            refine ⟨998217071791372068039760733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665478047860914712026507155 998217071791372068039760733)
            ·
              refine ⟨374331401921764525514910275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 998217071791372068039760733 374331401921764525514910275)
              ·
                refine ⟨561497102882646788272365413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374331401921764525514910275 561497102882646788272365413)
                ·
                  refine ⟨105280706790496272801068515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 561497102882646788272365413 105280706790496272801068515)
                  ·
                    refine ⟨157921060185744409201602773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105280706790496272801068515 157921060185744409201602773)
                    ·
                      refine ⟨3701274848103384590662565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157921060185744409201602773 3701274848103384590662565)
                      ·
                        rfl

theorem cell23_7208207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_7208207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208207 prefixEnd_7208207 := by exact prefixLift 7208207
  have htrace : WordTrace (prefixWord ++ tailWord_7208207) baseStart_7208207 baseEnd_7208207 := by
    simpa [prefixWord, tailWord_7208207, baseEnd_7208207] using wordTrace_append hprefix tailTrace_7208207
  have hstable : (prefixWord ++ tailWord_7208207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208207).length < 2 ^ (prefixWord ++ tailWord_7208207).sum := by decide
  have hdescent : baseEnd_7208207 < baseStart_7208207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208217 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 10]
def baseStart_7208217 : Nat := 118140960795 + 7208217 * 2 ^ 59
def prefixEnd_7208217 : Nat := 4983230072969 + 3 ^ 40 * 7208217 * 2
def baseEnd_7208217 : Nat := 3701279982909929551537519

theorem tailTrace_7208217 : CollatzResearch.WordTrace tailWord_7208217 prefixEnd_7208217 3701279982909929551537519 := by
  unfold tailWord_7208217
  simp only [CollatzResearch.WordTrace]
  refine ⟨262905272526868349298582905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175270181684578899532388603 262905272526868349298582905)
  ·
    refine ⟨197178954395151261973937179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262905272526868349298582905 197178954395151261973937179)
    ·
      refine ⟨295768431592726892960905769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197178954395151261973937179 295768431592726892960905769)
      ·
        refine ⟨221826323694545169720679327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295768431592726892960905769 221826323694545169720679327)
        ·
          refine ⟨332739485541817754581018991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221826323694545169720679327 332739485541817754581018991)
          ·
            refine ⟨499109228312726631871528487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332739485541817754581018991 499109228312726631871528487)
            ·
              refine ⟨748663842469089947807292731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499109228312726631871528487 748663842469089947807292731)
              ·
                refine ⟨1122995763703634921710939097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748663842469089947807292731 1122995763703634921710939097)
                ·
                  refine ⟨842246822777726191283204323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1122995763703634921710939097 842246822777726191283204323)
                  ·
                    refine ⟨1263370234166589286924806485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 842246822777726191283204323 1263370234166589286924806485)
                    ·
                      refine ⟨3701279982909929551537519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1263370234166589286924806485 3701279982909929551537519)
                      ·
                        rfl

theorem cell23_7208217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_7208217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208217 prefixEnd_7208217 := by exact prefixLift 7208217
  have htrace : WordTrace (prefixWord ++ tailWord_7208217) baseStart_7208217 baseEnd_7208217 := by
    simpa [prefixWord, tailWord_7208217, baseEnd_7208217] using wordTrace_append hprefix tailTrace_7208217
  have hstable : (prefixWord ++ tailWord_7208217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208217).length < 2 ^ (prefixWord ++ tailWord_7208217).sum := by decide
  have hdescent : baseEnd_7208217 < baseStart_7208217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208218 : List Nat := [3, 1, 1, 3, 3, 3, 2, 1, 6]
def baseStart_7208218 : Nat := 118140960795 + 7208218 * 2 ^ 59
def prefixEnd_7208218 : Nat := 4983230072969 + 3 ^ 40 * 7208218 * 2
def baseEnd_7208218 : Nat := 411253388487842671958335

theorem tailTrace_7208218 : CollatzResearch.WordTrace tailWord_7208218 prefixEnd_7208218 411253388487842671958335 := by
  unfold tailWord_7208218
  simp only [CollatzResearch.WordTrace]
  refine ⟨65726327249966181617342327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175270205999909817646246205 65726327249966181617342327)
  ·
    refine ⟨98589490874949272426013491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65726327249966181617342327 98589490874949272426013491)
    ·
      refine ⟨147884236312423908639020237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98589490874949272426013491 147884236312423908639020237)
      ·
        refine ⟨55456588617158965739632589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147884236312423908639020237 55456588617158965739632589)
        ·
          refine ⟨20796220731434612152362221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55456588617158965739632589 20796220731434612152362221)
          ·
            refine ⟨7798582774287979557135833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20796220731434612152362221 7798582774287979557135833)
            ·
              refine ⟨5848937080715984667851875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7798582774287979557135833 5848937080715984667851875)
              ·
                refine ⟨8773405621073977001777813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5848937080715984667851875 8773405621073977001777813)
                ·
                  refine ⟨411253388487842671958335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8773405621073977001777813 411253388487842671958335)
                  ·
                    rfl

theorem cell23_7208218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 6].length) (baseStart_7208218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208218 prefixEnd_7208218 := by exact prefixLift 7208218
  have htrace : WordTrace (prefixWord ++ tailWord_7208218) baseStart_7208218 baseEnd_7208218 := by
    simpa [prefixWord, tailWord_7208218, baseEnd_7208218] using wordTrace_append hprefix tailTrace_7208218
  have hstable : (prefixWord ++ tailWord_7208218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208218).length < 2 ^ (prefixWord ++ tailWord_7208218).sum := by decide
  have hdescent : baseEnd_7208218 < baseStart_7208218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208264 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_7208264 : Nat := 118140960795 + 7208264 * 2 ^ 59
def prefixEnd_7208264 : Nat := 4983230072969 + 3 ^ 40 * 7208264 * 2
def baseEnd_7208264 : Nat := 3701304116500690867649803

theorem tailTrace_7208264 : CollatzResearch.WordTrace tailWord_7208264 prefixEnd_7208264 3701304116500690867649803 := by
  unfold tailWord_7208264
  simp only [CollatzResearch.WordTrace]
  refine ⟨131453493378849038162771923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175271324505132050883695897 131453493378849038162771923)
  ·
    refine ⟨197180240068273557244157885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131453493378849038162771923 197180240068273557244157885)
    ·
      refine ⟨73942590025602583966559207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197180240068273557244157885 73942590025602583966559207)
      ·
        refine ⟨110913885038403875949838811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73942590025602583966559207 110913885038403875949838811)
        ·
          refine ⟨166370827557605813924758217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110913885038403875949838811 166370827557605813924758217)
          ·
            refine ⟨124778120668204360443568663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166370827557605813924758217 124778120668204360443568663)
            ·
              refine ⟨187167181002306540665352995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124778120668204360443568663 187167181002306540665352995)
              ·
                refine ⟨280750771503459810998029493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187167181002306540665352995 280750771503459810998029493)
                ·
                  refine ⟨26320384828449357281065265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 280750771503459810998029493 26320384828449357281065265)
                  ·
                    refine ⟨19740288621337017960798949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26320384828449357281065265 19740288621337017960798949)
                    ·
                      refine ⟨3701304116500690867649803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19740288621337017960798949 3701304116500690867649803)
                      ·
                        rfl

theorem cell23_7208264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_7208264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208264 prefixEnd_7208264 := by exact prefixLift 7208264
  have htrace : WordTrace (prefixWord ++ tailWord_7208264) baseStart_7208264 baseEnd_7208264 := by
    simpa [prefixWord, tailWord_7208264, baseEnd_7208264] using wordTrace_append hprefix tailTrace_7208264
  have hstable : (prefixWord ++ tailWord_7208264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208264).length < 2 ^ (prefixWord ++ tailWord_7208264).sum := by decide
  have hdescent : baseEnd_7208264 < baseStart_7208264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208291 : List Nat := [1, 1, 1, 5, 2, 3, 3, 7]
def baseStart_7208291 : Nat := 118140960795 + 7208291 * 2 ^ 59
def prefixEnd_7208291 : Nat := 4983230072969 + 3 ^ 40 * 7208291 * 2
def baseEnd_7208291 : Nat := 137085851128828231926377

theorem tailTrace_7208291 : CollatzResearch.WordTrace tailWord_7208291 prefixEnd_7208291 137085851128828231926377 := by
  unfold tailWord_7208291
  simp only [CollatzResearch.WordTrace]
  refine ⟨262907971528600259936776727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175271981019066839957851151 262907971528600259936776727)
  ·
    refine ⟨394361957292900389905165091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262907971528600259936776727 394361957292900389905165091)
    ·
      refine ⟨591542935939350584857747637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394361957292900389905165091 591542935939350584857747637)
      ·
        refine ⟨55457150244314117330413841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 591542935939350584857747637 55457150244314117330413841)
        ·
          refine ⟨41592862683235587997810381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55457150244314117330413841 41592862683235587997810381)
          ·
            refine ⟨15597323506213345499178893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41592862683235587997810381 15597323506213345499178893)
            ·
              refine ⟨5848996314830004562192085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15597323506213345499178893 5848996314830004562192085)
              ·
                refine ⟨137085851128828231926377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5848996314830004562192085 137085851128828231926377)
                ·
                  rfl

theorem cell23_7208291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 7].length) (baseStart_7208291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208291 prefixEnd_7208291 := by exact prefixLift 7208291
  have htrace : WordTrace (prefixWord ++ tailWord_7208291) baseStart_7208291 baseEnd_7208291 := by
    simpa [prefixWord, tailWord_7208291, baseEnd_7208291] using wordTrace_append hprefix tailTrace_7208291
  have hstable : (prefixWord ++ tailWord_7208291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208291).length < 2 ^ (prefixWord ++ tailWord_7208291).sum := by decide
  have hdescent : baseEnd_7208291 < baseStart_7208291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208314 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_7208314 : Nat := 118140960795 + 7208314 * 2 ^ 59
def prefixEnd_7208314 : Nat := 4983230072969 + 3 ^ 40 * 7208314 * 2
def baseEnd_7208314 : Nat := 3701329790533415672024573

theorem tailTrace_7208314 : CollatzResearch.WordTrace tailWord_7208314 prefixEnd_7208314 3701329790533415672024573 := by
  unfold tailWord_7208314
  simp only [CollatzResearch.WordTrace]
  refine ⟨65727202601879233716215999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175272540271677956576575997 65727202601879233716215999)
  ·
    refine ⟨98590803902818850574323999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65727202601879233716215999 98590803902818850574323999)
    ·
      refine ⟨147886205854228275861485999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98590803902818850574323999 147886205854228275861485999)
      ·
        refine ⟨221829308781342413792228999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147886205854228275861485999 221829308781342413792228999)
        ·
          refine ⟨332743963172013620688343499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221829308781342413792228999 332743963172013620688343499)
          ·
            refine ⟨499115944758020431032515249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332743963172013620688343499 499115944758020431032515249)
            ·
              refine ⟨374336958568515323274386437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499115944758020431032515249 374336958568515323274386437)
              ·
                refine ⟨70188179731596623113947457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 374336958568515323274386437 70188179731596623113947457)
                ·
                  refine ⟨52641134798697467335460593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70188179731596623113947457 52641134798697467335460593)
                  ·
                    refine ⟨39480851099023100501595445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52641134798697467335460593 39480851099023100501595445)
                    ·
                      refine ⟨3701329790533415672024573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39480851099023100501595445 3701329790533415672024573)
                      ·
                        rfl

theorem cell23_7208314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_7208314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208314 prefixEnd_7208314 := by exact prefixLift 7208314
  have htrace : WordTrace (prefixWord ++ tailWord_7208314) baseStart_7208314 baseEnd_7208314 := by
    simpa [prefixWord, tailWord_7208314, baseEnd_7208314] using wordTrace_append hprefix tailTrace_7208314
  have hstable : (prefixWord ++ tailWord_7208314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208314).length < 2 ^ (prefixWord ++ tailWord_7208314).sum := by decide
  have hdescent : baseEnd_7208314 < baseStart_7208314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208345 : List Nat := [1, 2, 1, 2, 1, 6, 2, 2, 1, 3, 2]
def baseStart_7208345 : Nat := 118140960795 + 7208345 * 2 ^ 59
def prefixEnd_7208345 : Nat := 4983230072969 + 3 ^ 40 * 7208345 * 2
def baseEnd_7208345 : Nat := 3701345708433705050736931

theorem tailTrace_7208345 : CollatzResearch.WordTrace tailWord_7208345 prefixEnd_7208345 3701345708433705050736931 := by
  unfold tailWord_7208345
  simp only [CollatzResearch.WordTrace]
  refine ⟨262909941070404627159242489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175273294046936418106161659 262909941070404627159242489)
  ·
    refine ⟨197182455802803470369431867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262909941070404627159242489 197182455802803470369431867)
    ·
      refine ⟨295773683704205205554147801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197182455802803470369431867 295773683704205205554147801)
      ·
        refine ⟨221830262778153904165610851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295773683704205205554147801 221830262778153904165610851)
        ·
          refine ⟨332745394167230856248416277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221830262778153904165610851 332745394167230856248416277)
          ·
            refine ⟨15597440351588946386644513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 332745394167230856248416277 15597440351588946386644513)
            ·
              refine ⟨11698080263691709789983385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15597440351588946386644513 11698080263691709789983385)
              ·
                refine ⟨8773560197768782342487539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11698080263691709789983385 8773560197768782342487539)
                ·
                  refine ⟨13160340296653173513731309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8773560197768782342487539 13160340296653173513731309)
                  ·
                    refine ⟨4935127611244940067649241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13160340296653173513731309 4935127611244940067649241)
                    ·
                      refine ⟨3701345708433705050736931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4935127611244940067649241 3701345708433705050736931)
                      ·
                        rfl

theorem cell23_7208345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 3, 2].length) (baseStart_7208345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208345 prefixEnd_7208345 := by exact prefixLift 7208345
  have htrace : WordTrace (prefixWord ++ tailWord_7208345) baseStart_7208345 baseEnd_7208345 := by
    simpa [prefixWord, tailWord_7208345, baseEnd_7208345] using wordTrace_append hprefix tailTrace_7208345
  have hstable : (prefixWord ++ tailWord_7208345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208345).length < 2 ^ (prefixWord ++ tailWord_7208345).sum := by decide
  have hdescent : baseEnd_7208345 < baseStart_7208345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208364 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 9]
def baseStart_7208364 : Nat := 118140960795 + 7208364 * 2 ^ 59
def prefixEnd_7208364 : Nat := 4983230072969 + 3 ^ 40 * 7208364 * 2
def baseEnd_7208364 : Nat := 411261718285126719599927

theorem tailTrace_7208364 : CollatzResearch.WordTrace tailWord_7208364 prefixEnd_7208364 411261718285126719599927 := by
  unfold tailWord_7208364
  simp only [CollatzResearch.WordTrace]
  refine ⟨131455317028667896702092073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175273756038223862269456097 131455317028667896702092073)
  ·
    refine ⟨98591487771500922526569055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131455317028667896702092073 98591487771500922526569055)
    ·
      refine ⟨147887231657251383789853583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98591487771500922526569055 147887231657251383789853583)
      ·
        refine ⟨221830847485877075684780375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147887231657251383789853583 221830847485877075684780375)
        ·
          refine ⟨332746271228815613527170563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221830847485877075684780375 332746271228815613527170563)
          ·
            refine ⟨499119406843223420290755845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332746271228815613527170563 499119406843223420290755845)
            ·
              refine ⟨93584888783104391304516721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 499119406843223420290755845 93584888783104391304516721)
              ·
                refine ⟨70188666587328293478387541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93584888783104391304516721 70188666587328293478387541)
                ·
                  refine ⟨411261718285126719599927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70188666587328293478387541 411261718285126719599927)
                  ·
                    rfl

theorem cell23_7208364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_7208364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208364 prefixEnd_7208364 := by exact prefixLift 7208364
  have htrace : WordTrace (prefixWord ++ tailWord_7208364) baseStart_7208364 baseEnd_7208364 := by
    simpa [prefixWord, tailWord_7208364, baseEnd_7208364] using wordTrace_append hprefix tailTrace_7208364
  have hstable : (prefixWord ++ tailWord_7208364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208364).length < 2 ^ (prefixWord ++ tailWord_7208364).sum := by decide
  have hdescent : baseEnd_7208364 < baseStart_7208364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208375 : List Nat := [1, 1, 3, 1, 3, 2, 2, 4, 2, 2, 2]
def baseStart_7208375 : Nat := 118140960795 + 7208375 * 2 ^ 59
def prefixEnd_7208375 : Nat := 4983230072969 + 3 ^ 40 * 7208375 * 2
def baseEnd_7208375 : Nat := 3701361112853339933361793

theorem tailTrace_7208375 : CollatzResearch.WordTrace tailWord_7208375 prefixEnd_7208375 3701361112853339933361793 := by
  unfold tailWord_7208375
  simp only [CollatzResearch.WordTrace]
  refine ⟨262911035260295942282834579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175274023506863961521889719 262911035260295942282834579)
  ·
    refine ⟨394366552890443913424251869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262911035260295942282834579 394366552890443913424251869)
    ·
      refine ⟨147887457333916467534094451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394366552890443913424251869 147887457333916467534094451)
      ·
        refine ⟨221831186000874701301141677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147887457333916467534094451 221831186000874701301141677)
        ·
          refine ⟨83186694750328012987928129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221831186000874701301141677 83186694750328012987928129)
          ·
            refine ⟨62390021062746009740946097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83186694750328012987928129 62390021062746009740946097)
            ·
              refine ⟨46792515797059507305709573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62390021062746009740946097 46792515797059507305709573)
              ·
                refine ⟨8773596711948657619820545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46792515797059507305709573 8773596711948657619820545)
                ·
                  refine ⟨6580197533961493214865409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8773596711948657619820545 6580197533961493214865409)
                  ·
                    refine ⟨4935148150471119911149057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6580197533961493214865409 4935148150471119911149057)
                    ·
                      refine ⟨3701361112853339933361793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4935148150471119911149057 3701361112853339933361793)
                      ·
                        rfl

theorem cell23_7208375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 2, 2].length) (baseStart_7208375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208375 prefixEnd_7208375 := by exact prefixLift 7208375
  have htrace : WordTrace (prefixWord ++ tailWord_7208375) baseStart_7208375 baseEnd_7208375 := by
    simpa [prefixWord, tailWord_7208375, baseEnd_7208375] using wordTrace_append hprefix tailTrace_7208375
  have hstable : (prefixWord ++ tailWord_7208375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208375).length < 2 ^ (prefixWord ++ tailWord_7208375).sum := by decide
  have hdescent : baseEnd_7208375 < baseStart_7208375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208391 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_7208391 : Nat := 118140960795 + 7208391 * 2 ^ 59
def prefixEnd_7208391 : Nat := 4983230072969 + 3 ^ 40 * 7208391 * 2
def baseEnd_7208391 : Nat := 3701369328543811870761719

theorem tailTrace_7208391 : CollatzResearch.WordTrace tailWord_7208391 prefixEnd_7208391 3701369328543811870761719 := by
  unfold tailWord_7208391
  simp only [CollatzResearch.WordTrace]
  refine ⟨262911618828237977015417027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175274412552158651343611351 262911618828237977015417027)
  ·
    refine ⟨394367428242356965523125541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262911618828237977015417027 394367428242356965523125541)
    ·
      refine ⟨73943892795441931035586039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394367428242356965523125541 73943892795441931035586039)
      ·
        refine ⟨110915839193162896553379059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73943892795441931035586039 110915839193162896553379059)
        ·
          refine ⟨166373758789744344830068589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110915839193162896553379059 166373758789744344830068589)
          ·
            refine ⟨62390159546154129311275721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166373758789744344830068589 62390159546154129311275721)
            ·
              refine ⟨46792619659615596983456791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62390159546154129311275721 46792619659615596983456791)
              ·
                refine ⟨70188929489423395475185187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46792619659615596983456791 70188929489423395475185187)
                ·
                  refine ⟨105283394234135093212777781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70188929489423395475185187 105283394234135093212777781)
                  ·
                    refine ⟨9870318209450164988697917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105283394234135093212777781 9870318209450164988697917)
                    ·
                      refine ⟨3701369328543811870761719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9870318209450164988697917 3701369328543811870761719)
                      ·
                        rfl

theorem cell23_7208391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_7208391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208391 prefixEnd_7208391 := by exact prefixLift 7208391
  have htrace : WordTrace (prefixWord ++ tailWord_7208391) baseStart_7208391 baseEnd_7208391 := by
    simpa [prefixWord, tailWord_7208391, baseEnd_7208391] using wordTrace_append hprefix tailTrace_7208391
  have hstable : (prefixWord ++ tailWord_7208391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208391).length < 2 ^ (prefixWord ++ tailWord_7208391).sum := by decide
  have hdescent : baseEnd_7208391 < baseStart_7208391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208438 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_7208438 : Nat := 118140960795 + 7208438 * 2 ^ 59
def prefixEnd_7208438 : Nat := 4983230072969 + 3 ^ 40 * 7208438 * 2
def baseEnd_7208438 : Nat := 3701393462134573186874003

theorem tailTrace_7208438 : CollatzResearch.WordTrace tailWord_7208438 prefixEnd_7208438 3701393462134573186874003 := by
  unfold tailWord_7208438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16432083316191731502648623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175275555372711802694918645 16432083316191731502648623)
  ·
    refine ⟨24648124974287597253972935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16432083316191731502648623 24648124974287597253972935)
    ·
      refine ⟨36972187461431395880959403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24648124974287597253972935 36972187461431395880959403)
      ·
        refine ⟨55458281192147093821439105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36972187461431395880959403 55458281192147093821439105)
        ·
          refine ⟨41593710894110320366079329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55458281192147093821439105 41593710894110320366079329)
          ·
            refine ⟨31195283170582740274559497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41593710894110320366079329 31195283170582740274559497)
            ·
              refine ⟨23396462377937055205919623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31195283170582740274559497 23396462377937055205919623)
              ·
                refine ⟨35094693566905582808879435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23396462377937055205919623 35094693566905582808879435)
                ·
                  refine ⟨52642040350358374213319153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35094693566905582808879435 52642040350358374213319153)
                  ·
                    refine ⟨39481530262768780659989365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52642040350358374213319153 39481530262768780659989365)
                    ·
                      refine ⟨3701393462134573186874003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39481530262768780659989365 3701393462134573186874003)
                      ·
                        rfl

theorem cell23_7208438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_7208438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208438 prefixEnd_7208438 := by exact prefixLift 7208438
  have htrace : WordTrace (prefixWord ++ tailWord_7208438) baseStart_7208438 baseEnd_7208438 := by
    simpa [prefixWord, tailWord_7208438, baseEnd_7208438] using wordTrace_append hprefix tailTrace_7208438
  have hstable : (prefixWord ++ tailWord_7208438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208438).length < 2 ^ (prefixWord ++ tailWord_7208438).sum := by decide
  have hdescent : baseEnd_7208438 < baseStart_7208438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208458 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 5, 4]
def baseStart_7208458 : Nat := 118140960795 + 7208458 * 2 ^ 59
def prefixEnd_7208458 : Nat := 4983230072969 + 3 ^ 40 * 7208458 * 2
def baseEnd_7208458 : Nat := 1233801243915887702874637

theorem tailTrace_7208458 : CollatzResearch.WordTrace tailWord_7208458 prefixEnd_7208458 1233801243915887702874637 := by
  unfold tailWord_7208458
  simp only [CollatzResearch.WordTrace]
  refine ⟨65728515629748811864526507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175276041679330164972070685 65728515629748811864526507)
  ·
    refine ⟨98592773444623217796789761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65728515629748811864526507 98592773444623217796789761)
    ·
      refine ⟨73944580083467413347592321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98592773444623217796789761 73944580083467413347592321)
      ·
        refine ⟨55458435062600560010694241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73944580083467413347592321 55458435062600560010694241)
        ·
          refine ⟨41593826296950420008020681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55458435062600560010694241 41593826296950420008020681)
          ·
            refine ⟨31195369722712815006015511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41593826296950420008020681 31195369722712815006015511)
            ·
              refine ⟨46793054584069222509023267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31195369722712815006015511 46793054584069222509023267)
              ·
                refine ⟨70189581876103833763534901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46793054584069222509023267 70189581876103833763534901)
                ·
                  refine ⟨6580273300884734415331397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70189581876103833763534901 6580273300884734415331397)
                  ·
                    refine ⟨1233801243915887702874637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6580273300884734415331397 1233801243915887702874637)
                    ·
                      rfl

theorem cell23_7208458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_7208458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208458 prefixEnd_7208458 := by exact prefixLift 7208458
  have htrace : WordTrace (prefixWord ++ tailWord_7208458) baseStart_7208458 baseEnd_7208458 := by
    simpa [prefixWord, tailWord_7208458, baseEnd_7208458] using wordTrace_append hprefix tailTrace_7208458
  have hstable : (prefixWord ++ tailWord_7208458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208458).length < 2 ^ (prefixWord ++ tailWord_7208458).sum := by decide
  have hdescent : baseEnd_7208458 < baseStart_7208458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208462 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_7208462 : Nat := 118140960795 + 7208462 * 2 ^ 59
def prefixEnd_7208462 : Nat := 4983230072969 + 3 ^ 40 * 7208462 * 2
def baseEnd_7208462 : Nat := 1233801928556760364324631

theorem tailTrace_7208462 : CollatzResearch.WordTrace tailWord_7208462 prefixEnd_7208462 1233801928556760364324631 := by
  unfold tailWord_7208462
  simp only [CollatzResearch.WordTrace]
  refine ⟨32864276051372594517656455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175276138940653837427501093 32864276051372594517656455)
  ·
    refine ⟨49296414077058891776484683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32864276051372594517656455 49296414077058891776484683)
    ·
      refine ⟨73944621115588337664727025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49296414077058891776484683 73944621115588337664727025)
      ·
        refine ⟨55458465836691253248545269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73944621115588337664727025 55458465836691253248545269)
        ·
          refine ⟨5199231172189804992051119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55458465836691253248545269 5199231172189804992051119)
          ·
            refine ⟨7798846758284707488076679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5199231172189804992051119 7798846758284707488076679)
            ·
              refine ⟨11698270137427061232115019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7798846758284707488076679 11698270137427061232115019)
              ·
                refine ⟨17547405206140591848172529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11698270137427061232115019 17547405206140591848172529)
                ·
                  refine ⟨13160553904605443886129397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17547405206140591848172529 13160553904605443886129397)
                  ·
                    refine ⟨1233801928556760364324631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13160553904605443886129397 1233801928556760364324631)
                    ·
                      rfl

theorem cell23_7208462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_7208462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208462 prefixEnd_7208462 := by exact prefixLift 7208462
  have htrace : WordTrace (prefixWord ++ tailWord_7208462) baseStart_7208462 baseEnd_7208462 := by
    simpa [prefixWord, tailWord_7208462, baseEnd_7208462] using wordTrace_append hprefix tailTrace_7208462
  have hstable : (prefixWord ++ tailWord_7208462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208462).length < 2 ^ (prefixWord ++ tailWord_7208462).sum := by decide
  have hdescent : baseEnd_7208462 < baseStart_7208462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208505 : List Nat := [1, 2, 1, 5, 1, 3, 3, 1, 6]
def baseStart_7208505 : Nat := 118140960795 + 7208505 * 2 ^ 59
def prefixEnd_7208505 : Nat := 4983230072969 + 3 ^ 40 * 7208505 * 2
def baseEnd_7208505 : Nat := 411269762815380491637355

theorem tailTrace_7208505 : CollatzResearch.WordTrace tailWord_7208505 prefixEnd_7208505 411269762815380491637355 := by
  unfold tailWord_7208505
  simp only [CollatzResearch.WordTrace]
  refine ⟨262915776749824974485066969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175277184499883316323377979 262915776749824974485066969)
  ·
    refine ⟨197186832562368730863800227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262915776749824974485066969 197186832562368730863800227)
    ·
      refine ⟨295780248843553096295700341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197186832562368730863800227 295780248843553096295700341)
      ·
        refine ⟨27729398329083102777721907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295780248843553096295700341 27729398329083102777721907)
        ·
          refine ⟨41594097493624654166582861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27729398329083102777721907 41594097493624654166582861)
          ·
            refine ⟨15597786560109245312468573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41594097493624654166582861 15597786560109245312468573)
            ·
              refine ⟨5849169960040966992175715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15597786560109245312468573 5849169960040966992175715)
              ·
                refine ⟨8773754940061450488263573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5849169960040966992175715 8773754940061450488263573)
                ·
                  refine ⟨411269762815380491637355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8773754940061450488263573 411269762815380491637355)
                  ·
                    rfl

theorem cell23_7208505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 6].length) (baseStart_7208505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208505 prefixEnd_7208505 := by exact prefixLift 7208505
  have htrace : WordTrace (prefixWord ++ tailWord_7208505) baseStart_7208505 baseEnd_7208505 := by
    simpa [prefixWord, tailWord_7208505, baseEnd_7208505] using wordTrace_append hprefix tailTrace_7208505
  have hstable : (prefixWord ++ tailWord_7208505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208505).length < 2 ^ (prefixWord ++ tailWord_7208505).sum := by decide
  have hdescent : baseEnd_7208505 < baseStart_7208505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208521 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 2, 5, 4]
def baseStart_7208521 : Nat := 118140960795 + 7208521 * 2 ^ 59
def prefixEnd_7208521 : Nat := 4983230072969 + 3 ^ 40 * 7208521 * 2
def baseEnd_7208521 : Nat := 3701436081028896362136121

theorem tailTrace_7208521 : CollatzResearch.WordTrace tailWord_7208521 prefixEnd_7208521 3701436081028896362136121 := by
  unfold tailWord_7208521
  simp only [CollatzResearch.WordTrace]
  refine ⟨262916360317767009217649417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175277573545178006145099611 262916360317767009217649417)
  ·
    refine ⟨197187270238325256913237063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262916360317767009217649417 197187270238325256913237063)
    ·
      refine ⟨295780905357487885369855595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197187270238325256913237063 295780905357487885369855595)
      ·
        refine ⟨443671358036231828054783393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295780905357487885369855595 443671358036231828054783393)
        ·
          refine ⟨332753518527173871041087545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443671358036231828054783393 332753518527173871041087545)
          ·
            refine ⟨249565138895380403280815659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332753518527173871041087545 249565138895380403280815659)
            ·
              refine ⟨374347708343070604921223489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249565138895380403280815659 374347708343070604921223489)
              ·
                refine ⟨280760781257302953690917617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374347708343070604921223489 280760781257302953690917617)
                ·
                  refine ⟨210570585942977215268188213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280760781257302953690917617 210570585942977215268188213)
                  ·
                    refine ⟨19740992432154113931392645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 210570585942977215268188213 19740992432154113931392645)
                    ·
                      refine ⟨3701436081028896362136121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19740992432154113931392645 3701436081028896362136121)
                      ·
                        rfl

theorem cell23_7208521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_7208521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208521 prefixEnd_7208521 := by exact prefixLift 7208521
  have htrace : WordTrace (prefixWord ++ tailWord_7208521) baseStart_7208521 baseEnd_7208521 := by
    simpa [prefixWord, tailWord_7208521, baseEnd_7208521] using wordTrace_append hprefix tailTrace_7208521
  have hstable : (prefixWord ++ tailWord_7208521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208521).length < 2 ^ (prefixWord ++ tailWord_7208521).sum := by decide
  have hdescent : baseEnd_7208521 < baseStart_7208521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208591 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 3, 9]
def baseStart_7208591 : Nat := 118140960795 + 7208591 * 2 ^ 59
def prefixEnd_7208591 : Nat := 4983230072969 + 3 ^ 40 * 7208591 * 2
def baseEnd_7208591 : Nat := 1233824008224903696086933

theorem tailTrace_7208591 : CollatzResearch.WordTrace tailWord_7208591 prefixEnd_7208591 1233824008224903696086933 := by
  unfold tailWord_7208591
  simp only [CollatzResearch.WordTrace]
  refine ⟨262918913427513411172697627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175279275618342274115131751 262918913427513411172697627)
  ·
    refine ⟨394378370141270116759046441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262918913427513411172697627 394378370141270116759046441)
    ·
      refine ⟨295783777605952587569284831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394378370141270116759046441 295783777605952587569284831)
      ·
        refine ⟨443675666408928881353927247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295783777605952587569284831 443675666408928881353927247)
        ·
          refine ⟨665513499613393322030890871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443675666408928881353927247 665513499613393322030890871)
          ·
            refine ⟨998270249420089983046336307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665513499613393322030890871 998270249420089983046336307)
            ·
              refine ⟨1497405374130134974569504461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998270249420089983046336307 1497405374130134974569504461)
              ·
                refine ⟨561527015298800615463564173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1497405374130134974569504461 561527015298800615463564173)
                ·
                  refine ⟨210572630737050230798836565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561527015298800615463564173 210572630737050230798836565)
                  ·
                    refine ⟨1233824008224903696086933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 210572630737050230798836565 1233824008224903696086933)
                    ·
                      rfl

theorem cell23_7208591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_7208591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208591 prefixEnd_7208591 := by exact prefixLift 7208591
  have htrace : WordTrace (prefixWord ++ tailWord_7208591) baseStart_7208591 baseEnd_7208591 := by
    simpa [prefixWord, tailWord_7208591, baseEnd_7208591] using wordTrace_append hprefix tailTrace_7208591
  have hstable : (prefixWord ++ tailWord_7208591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208591).length < 2 ^ (prefixWord ++ tailWord_7208591).sum := by decide
  have hdescent : baseEnd_7208591 < baseStart_7208591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208608 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 2, 7]
def baseStart_7208608 : Nat := 118140960795 + 7208608 * 2 ^ 59
def prefixEnd_7208608 : Nat := 4983230072969 + 3 ^ 40 * 7208608 * 2
def baseEnd_7208608 : Nat := 1233826917948612507249407

theorem tailTrace_7208608 : CollatzResearch.WordTrace tailWord_7208608 prefixEnd_7208608 1233826917948612507249407 := by
  unfold tailWord_7208608
  simp only [CollatzResearch.WordTrace]
  refine ⟨131459766734225911538033239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175279688978967882050710985 131459766734225911538033239)
  ·
    refine ⟨197189650101338867307049859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131459766734225911538033239 197189650101338867307049859)
    ·
      refine ⟨295784475152008300960574789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197189650101338867307049859 295784475152008300960574789)
      ·
        refine ⟨55459589091001556430107773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295784475152008300960574789 55459589091001556430107773)
        ·
          refine ⟨20797345909125583661290415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55459589091001556430107773 20797345909125583661290415)
          ·
            refine ⟨31196018863688375491935623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20797345909125583661290415 31196018863688375491935623)
            ·
              refine ⟨46794028295532563237903435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31196018863688375491935623 46794028295532563237903435)
              ·
                refine ⟨70191042443298844856855153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46794028295532563237903435 70191042443298844856855153)
                ·
                  refine ⟨52643281832474133642641365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70191042443298844856855153 52643281832474133642641365)
                  ·
                    refine ⟨1233826917948612507249407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52643281832474133642641365 1233826917948612507249407)
                    ·
                      rfl

theorem cell23_7208608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_7208608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208608 prefixEnd_7208608 := by exact prefixLift 7208608
  have htrace : WordTrace (prefixWord ++ tailWord_7208608) baseStart_7208608 baseEnd_7208608 := by
    simpa [prefixWord, tailWord_7208608, baseEnd_7208608] using wordTrace_append hprefix tailTrace_7208608
  have hstable : (prefixWord ++ tailWord_7208608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208608).length < 2 ^ (prefixWord ++ tailWord_7208608).sum := by decide
  have hdescent : baseEnd_7208608 < baseStart_7208608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208648 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_7208648 : Nat := 118140960795 + 7208648 * 2 ^ 59
def prefixEnd_7208648 : Nat := 4983230072969 + 3 ^ 40 * 7208648 * 2
def baseEnd_7208648 : Nat := 3701501293072017365248037

theorem tailTrace_7208648 : CollatzResearch.WordTrace tailWord_7208648 prefixEnd_7208648 3701501293072017365248037 := by
  unfold tailWord_7208648
  simp only [CollatzResearch.WordTrace]
  refine ⟨131460496194153454953761299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175280661592204606605015065 131460496194153454953761299)
  ·
    refine ⟨197190744291230182430641949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131460496194153454953761299 197190744291230182430641949)
    ·
      refine ⟨73946529109211318411490731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197190744291230182430641949 73946529109211318411490731)
      ·
        refine ⟨110919793663816977617236097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73946529109211318411490731 110919793663816977617236097)
        ·
          refine ⟨83189845247862733212927073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110919793663816977617236097 83189845247862733212927073)
          ·
            refine ⟨62392383935897049909695305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83189845247862733212927073 62392383935897049909695305)
            ·
              refine ⟨46794287951922787432271479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62392383935897049909695305 46794287951922787432271479)
              ·
                refine ⟨70191431927884181148407219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46794287951922787432271479 70191431927884181148407219)
                ·
                  refine ⟨105287147891826271722610829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70191431927884181148407219 105287147891826271722610829)
                  ·
                    refine ⟨39482680459434851895979061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105287147891826271722610829 39482680459434851895979061)
                    ·
                      refine ⟨3701501293072017365248037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39482680459434851895979061 3701501293072017365248037)
                      ·
                        rfl

theorem cell23_7208648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_7208648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208648 prefixEnd_7208648 := by exact prefixLift 7208648
  have htrace : WordTrace (prefixWord ++ tailWord_7208648) baseStart_7208648 baseEnd_7208648 := by
    simpa [prefixWord, tailWord_7208648, baseEnd_7208648] using wordTrace_append hprefix tailTrace_7208648
  have hstable : (prefixWord ++ tailWord_7208648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208648).length < 2 ^ (prefixWord ++ tailWord_7208648).sum := by decide
  have hdescent : baseEnd_7208648 < baseStart_7208648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208685 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 7]
def baseStart_7208685 : Nat := 118140960795 + 7208685 * 2 ^ 59
def prefixEnd_7208685 : Nat := 4983230072969 + 3 ^ 40 * 7208685 * 2
def baseEnd_7208685 : Nat := 411280032428470413387263

theorem tailTrace_7208685 : CollatzResearch.WordTrace tailWord_7208685 prefixEnd_7208685 411280032428470413387263 := by
  unfold tailWord_7208685
  simp only [CollatzResearch.WordTrace]
  refine ⟨262922341889172865226619509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175281561259448576817746339 262922341889172865226619509)
  ·
    refine ⟨24648969552109956114995579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262922341889172865226619509 24648969552109956114995579)
    ·
      refine ⟨36973454328164934172493369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24648969552109956114995579 36973454328164934172493369)
      ·
        refine ⟨27730090746123700629370027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36973454328164934172493369 27730090746123700629370027)
        ·
          refine ⟨41595136119185550944055041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27730090746123700629370027 41595136119185550944055041)
          ·
            refine ⟨31196352089389163208041281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41595136119185550944055041 31196352089389163208041281)
            ·
              refine ⟨23397264067041872406030961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31196352089389163208041281 23397264067041872406030961)
              ·
                refine ⟨17547948050281404304523221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23397264067041872406030961 17547948050281404304523221)
                ·
                  refine ⟨411280032428470413387263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17547948050281404304523221 411280032428470413387263)
                  ·
                    rfl

theorem cell23_7208685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_7208685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208685 prefixEnd_7208685 := by exact prefixLift 7208685
  have htrace : WordTrace (prefixWord ++ tailWord_7208685) baseStart_7208685 baseEnd_7208685 := by
    simpa [prefixWord, tailWord_7208685, baseEnd_7208685] using wordTrace_append hprefix tailTrace_7208685
  have hstable : (prefixWord ++ tailWord_7208685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208685).length < 2 ^ (prefixWord ++ tailWord_7208685).sum := by decide
  have hdescent : baseEnd_7208685 < baseStart_7208685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208725 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_7208725 : Nat := 118140960795 + 7208725 * 2 ^ 59
def prefixEnd_7208725 : Nat := 4983230072969 + 3 ^ 40 * 7208725 * 2
def baseEnd_7208725 : Nat := 3701540831082413563985183

theorem tailTrace_7208725 : CollatzResearch.WordTrace tailWord_7208725 prefixEnd_7208725 3701540831082413563985183 := by
  unfold tailWord_7208725
  simp only [CollatzResearch.WordTrace]
  refine ⟨262923800809027952058075629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175282533872685301372050419 262923800809027952058075629)
  ·
    refine ⟨98596425303385482021778361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262923800809027952058075629 98596425303385482021778361)
    ·
      refine ⟨73947318977539111516333771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98596425303385482021778361 73947318977539111516333771)
      ·
        refine ⟨110920978466308667274500657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73947318977539111516333771 110920978466308667274500657)
        ·
          refine ⟨83190733849731500455875493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110920978466308667274500657 83190733849731500455875493)
          ·
            refine ⟨15598262596824656335476655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83190733849731500455875493 15598262596824656335476655)
            ·
              refine ⟨23397393895236984503214983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15598262596824656335476655 23397393895236984503214983)
              ·
                refine ⟨35096090842855476754822475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23397393895236984503214983 35096090842855476754822475)
                ·
                  refine ⟨52644136264283215132233713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35096090842855476754822475 52644136264283215132233713)
                  ·
                    refine ⟨39483102198212411349175285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52644136264283215132233713 39483102198212411349175285)
                    ·
                      refine ⟨3701540831082413563985183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39483102198212411349175285 3701540831082413563985183)
                      ·
                        rfl

theorem cell23_7208725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_7208725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208725 prefixEnd_7208725 := by exact prefixLift 7208725
  have htrace : WordTrace (prefixWord ++ tailWord_7208725) baseStart_7208725 baseEnd_7208725 := by
    simpa [prefixWord, tailWord_7208725, baseEnd_7208725] using wordTrace_append hprefix tailTrace_7208725
  have hstable : (prefixWord ++ tailWord_7208725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208725).length < 2 ^ (prefixWord ++ tailWord_7208725).sum := by decide
  have hdescent : baseEnd_7208725 < baseStart_7208725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208735 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 4]
def baseStart_7208735 : Nat := 118140960795 + 7208735 * 2 ^ 59
def prefixEnd_7208735 : Nat := 4983230072969 + 3 ^ 40 * 7208735 * 2
def baseEnd_7208735 : Nat := 3701545965888958524860137

theorem tailTrace_7208735 : CollatzResearch.WordTrace tailWord_7208735 prefixEnd_7208735 3701545965888958524860137 := by
  unfold tailWord_7208735
  simp only [CollatzResearch.WordTrace]
  refine ⟨262924165538991723765939659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175282777025994482510626439 262924165538991723765939659)
  ·
    refine ⟨394386248308487585648909489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262924165538991723765939659 394386248308487585648909489)
    ·
      refine ⟨295789686231365689236682117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394386248308487585648909489 295789686231365689236682117)
      ·
        refine ⟨55460566168381066731877897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295789686231365689236682117 55460566168381066731877897)
        ·
          refine ⟨41595424626285800048908423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55460566168381066731877897 41595424626285800048908423)
          ·
            refine ⟨62393136939428700073362635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41595424626285800048908423 62393136939428700073362635)
            ·
              refine ⟨93589705409143050110043953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62393136939428700073362635 93589705409143050110043953)
              ·
                refine ⟨70192279056857287582532965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93589705409143050110043953 70192279056857287582532965)
                ·
                  refine ⟨13161052323160741421724931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70192279056857287582532965 13161052323160741421724931)
                  ·
                    refine ⟨19741578484741112132587397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13161052323160741421724931 19741578484741112132587397)
                    ·
                      refine ⟨3701545965888958524860137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19741578484741112132587397 3701545965888958524860137)
                      ·
                        rfl

theorem cell23_7208735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_7208735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208735 prefixEnd_7208735 := by exact prefixLift 7208735
  have htrace : WordTrace (prefixWord ++ tailWord_7208735) baseStart_7208735 baseEnd_7208735 := by
    simpa [prefixWord, tailWord_7208735, baseEnd_7208735] using wordTrace_append hprefix tailTrace_7208735
  have hstable : (prefixWord ++ tailWord_7208735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208735).length < 2 ^ (prefixWord ++ tailWord_7208735).sum := by decide
  have hdescent : baseEnd_7208735 < baseStart_7208735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208775 : List Nat := [1, 1, 4, 1, 2, 1, 3, 4, 6]
def baseStart_7208775 : Nat := 118140960795 + 7208775 * 2 ^ 59
def prefixEnd_7208775 : Nat := 4983230072969 + 3 ^ 40 * 7208775 * 2
def baseEnd_7208775 : Nat := 411285167235015374262217

theorem tailTrace_7208775 : CollatzResearch.WordTrace tailWord_7208775 prefixEnd_7208775 411285167235015374262217 := by
  unfold tailWord_7208775
  simp only [CollatzResearch.WordTrace]
  refine ⟨262925624458846810597395779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175283749639231207064930519 262925624458846810597395779)
  ·
    refine ⟨394388436688270215896093669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262925624458846810597395779 394388436688270215896093669)
    ·
      refine ⟨73947831879050665480517563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394388436688270215896093669 73947831879050665480517563)
      ·
        refine ⟨110921747818575998220776345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73947831879050665480517563 110921747818575998220776345)
        ·
          refine ⟨83191310863931998665582259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110921747818575998220776345 83191310863931998665582259)
          ·
            refine ⟨124786966295897997998373389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83191310863931998665582259 124786966295897997998373389)
            ·
              refine ⟨46795112360961749249390021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124786966295897997998373389 46795112360961749249390021)
              ·
                refine ⟨8774083567680327984260629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46795112360961749249390021 8774083567680327984260629)
                ·
                  refine ⟨411285167235015374262217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8774083567680327984260629 411285167235015374262217)
                  ·
                    rfl

theorem cell23_7208775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 6].length) (baseStart_7208775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208775 prefixEnd_7208775 := by exact prefixLift 7208775
  have htrace : WordTrace (prefixWord ++ tailWord_7208775) baseStart_7208775 baseEnd_7208775 := by
    simpa [prefixWord, tailWord_7208775, baseEnd_7208775] using wordTrace_append hprefix tailTrace_7208775
  have hstable : (prefixWord ++ tailWord_7208775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208775).length < 2 ^ (prefixWord ++ tailWord_7208775).sum := by decide
  have hdescent : baseEnd_7208775 < baseStart_7208775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208836 : List Nat := [2, 3, 2, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_7208836 : Nat := 118140960795 + 7208836 * 2 ^ 59
def prefixEnd_7208836 : Nat := 4983230072969 + 3 ^ 40 * 7208836 * 2
def baseEnd_7208836 : Nat := 3701597827435062629697173

theorem tailTrace_7208836 : CollatzResearch.WordTrace tailWord_7208836 prefixEnd_7208836 3701597827435062629697173 := by
  unfold tailWord_7208836
  simp only [CollatzResearch.WordTrace]
  refine ⟨131463924655812909007683181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175285232874417212010244241 131463924655812909007683181)
  ·
    refine ⟨49298971745929840877881193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131463924655812909007683181 49298971745929840877881193)
    ·
      refine ⟨36974228809447380658410895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49298971745929840877881193 36974228809447380658410895)
      ·
        refine ⟨55461343214171070987616343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36974228809447380658410895 55461343214171070987616343)
        ·
          refine ⟨83192014821256606481424515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55461343214171070987616343 83192014821256606481424515)
          ·
            refine ⟨124788022231884909722136773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83192014821256606481424515 124788022231884909722136773)
            ·
              refine ⟨23397754168478420572900645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124788022231884909722136773 23397754168478420572900645)
              ·
                refine ⟨4387078906589703857418871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23397754168478420572900645 4387078906589703857418871)
                ·
                  refine ⟨6580618359884555786128307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387078906589703857418871 6580618359884555786128307)
                  ·
                    refine ⟨9870927539826833679192461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6580618359884555786128307 9870927539826833679192461)
                    ·
                      refine ⟨3701597827435062629697173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9870927539826833679192461 3701597827435062629697173)
                      ·
                        rfl

theorem cell23_7208836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_7208836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208836 prefixEnd_7208836 := by exact prefixLift 7208836
  have htrace : WordTrace (prefixWord ++ tailWord_7208836) baseStart_7208836 baseEnd_7208836 := by
    simpa [prefixWord, tailWord_7208836, baseEnd_7208836] using wordTrace_append hprefix tailTrace_7208836
  have hstable : (prefixWord ++ tailWord_7208836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208836).length < 2 ^ (prefixWord ++ tailWord_7208836).sum := by decide
  have hdescent : baseEnd_7208836 < baseStart_7208836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208856 : List Nat := [2, 1, 2, 6, 1, 1, 2, 2, 1, 5]
def baseStart_7208856 : Nat := 118140960795 + 7208856 * 2 ^ 59
def prefixEnd_7208856 : Nat := 4983230072969 + 3 ^ 40 * 7208856 * 2
def baseEnd_7208856 : Nat := 1233869365682717517149027

theorem tailTrace_7208856 : CollatzResearch.WordTrace tailWord_7208856 prefixEnd_7208856 1233869365682717517149027 := by
  unfold tailWord_7208856
  simp only [CollatzResearch.WordTrace]
  refine ⟨131464289385776680715547211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175285719181035574287396281 131464289385776680715547211)
  ·
    refine ⟨197196434078665021073320817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131464289385776680715547211 197196434078665021073320817)
    ·
      refine ⟨147897325558998765804990613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197196434078665021073320817 147897325558998765804990613)
      ·
        refine ⟨6932687135578067147108935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147897325558998765804990613 6932687135578067147108935)
        ·
          refine ⟨10399030703367100720663403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6932687135578067147108935 10399030703367100720663403)
          ·
            refine ⟨15598546055050651080995105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10399030703367100720663403 15598546055050651080995105)
            ·
              refine ⟨11698909541287988310746329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15598546055050651080995105 11698909541287988310746329)
              ·
                refine ⟨8774182155965991233059747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11698909541287988310746329 8774182155965991233059747)
                ·
                  refine ⟨13161273233948986849589621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8774182155965991233059747 13161273233948986849589621)
                  ·
                    refine ⟨1233869365682717517149027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13161273233948986849589621 1233869365682717517149027)
                    ·
                      rfl

theorem cell23_7208856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_7208856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208856 prefixEnd_7208856 := by exact prefixLift 7208856
  have htrace : WordTrace (prefixWord ++ tailWord_7208856) baseStart_7208856 baseEnd_7208856 := by
    simpa [prefixWord, tailWord_7208856, baseEnd_7208856] using wordTrace_append hprefix tailTrace_7208856
  have hstable : (prefixWord ++ tailWord_7208856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208856).length < 2 ^ (prefixWord ++ tailWord_7208856).sum := by decide
  have hdescent : baseEnd_7208856 < baseStart_7208856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208893 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 3, 2, 2]
def baseStart_7208893 : Nat := 118140960795 + 7208893 * 2 ^ 59
def prefixEnd_7208893 : Nat := 4983230072969 + 3 ^ 40 * 7208893 * 2
def baseEnd_7208893 : Nat := 3701627095832368906684411

theorem tailTrace_7208893 : CollatzResearch.WordTrace tailWord_7208893 prefixEnd_7208893 3701627095832368906684411 := by
  unfold tailWord_7208893
  simp only [CollatzResearch.WordTrace]
  refine ⟨262929928272419316750191333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175286618848279544500127555 262929928272419316750191333)
  ·
    refine ⟨49299361551078621890660875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262929928272419316750191333 49299361551078621890660875)
    ·
      refine ⟨73949042326617932835991313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49299361551078621890660875 73949042326617932835991313)
      ·
        refine ⟨55461781744963449626993485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73949042326617932835991313 55461781744963449626993485)
        ·
          refine ⟨20798168154361293610122557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55461781744963449626993485 20798168154361293610122557)
          ·
            refine ⟨7799313057885485103795959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20798168154361293610122557 7799313057885485103795959)
            ·
              refine ⟨11698969586828227655693939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7799313057885485103795959 11698969586828227655693939)
              ·
                refine ⟨17548454380242341483540909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11698969586828227655693939 17548454380242341483540909)
                ·
                  refine ⟨6580670392590878056327841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17548454380242341483540909 6580670392590878056327841)
                  ·
                    refine ⟨4935502794443158542245881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6580670392590878056327841 4935502794443158542245881)
                    ·
                      refine ⟨3701627095832368906684411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4935502794443158542245881 3701627095832368906684411)
                      ·
                        rfl

theorem cell23_7208893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_7208893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208893 prefixEnd_7208893 := by exact prefixLift 7208893
  have htrace : WordTrace (prefixWord ++ tailWord_7208893) baseStart_7208893 baseEnd_7208893 := by
    simpa [prefixWord, tailWord_7208893, baseEnd_7208893] using wordTrace_append hprefix tailTrace_7208893
  have hstable : (prefixWord ++ tailWord_7208893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208893).length < 2 ^ (prefixWord ++ tailWord_7208893).sum := by decide
  have hdescent : baseEnd_7208893 < baseStart_7208893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208895 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 2, 7]
def baseStart_7208895 : Nat := 118140960795 + 7208895 * 2 ^ 59
def prefixEnd_7208895 : Nat := 4983230072969 + 3 ^ 40 * 7208895 * 2
def baseEnd_7208895 : Nat := 1233876040931225966286467

theorem tailTrace_7208895 : CollatzResearch.WordTrace tailWord_7208895 prefixEnd_7208895 1233876040931225966286467 := by
  unfold tailWord_7208895
  simp only [CollatzResearch.WordTrace]
  refine ⟨262930001218412071091764139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175286667478941380727842759 262930001218412071091764139)
  ·
    refine ⟨394395001827618106637646209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262930001218412071091764139 394395001827618106637646209)
    ·
      refine ⟨295796251370713579978234657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394395001827618106637646209 295796251370713579978234657)
      ·
        refine ⟨221847188528035184983675993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295796251370713579978234657 221847188528035184983675993)
        ·
          refine ⟨166385391396026388737756995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221847188528035184983675993 166385391396026388737756995)
          ·
            refine ⟨249578087094039583106635493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166385391396026388737756995 249578087094039583106635493)
            ·
              refine ⟨46795891330132421832494155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249578087094039583106635493 46795891330132421832494155)
              ·
                refine ⟨70193836995198632748741233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46795891330132421832494155 70193836995198632748741233)
                ·
                  refine ⟨52645377746398974561555925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70193836995198632748741233 52645377746398974561555925)
                  ·
                    refine ⟨1233876040931225966286467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52645377746398974561555925 1233876040931225966286467)
                    ·
                      rfl

theorem cell23_7208895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_7208895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208895 prefixEnd_7208895 := by exact prefixLift 7208895
  have htrace : WordTrace (prefixWord ++ tailWord_7208895) baseStart_7208895 baseEnd_7208895 := by
    simpa [prefixWord, tailWord_7208895, baseEnd_7208895] using wordTrace_append hprefix tailTrace_7208895
  have hstable : (prefixWord ++ tailWord_7208895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208895).length < 2 ^ (prefixWord ++ tailWord_7208895).sum := by decide
  have hdescent : baseEnd_7208895 < baseStart_7208895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208905 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 5]
def baseStart_7208905 : Nat := 118140960795 + 7208905 * 2 ^ 59
def prefixEnd_7208905 : Nat := 4983230072969 + 3 ^ 40 * 7208905 * 2
def baseEnd_7208905 : Nat := 3701633257600222859734355

theorem tailTrace_7208905 : CollatzResearch.WordTrace tailWord_7208905 prefixEnd_7208905 3701633257600222859734355 := by
  unfold tailWord_7208905
  simp only [CollatzResearch.WordTrace]
  refine ⟨262930365948375842799628169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175286910632250561866418779 262930365948375842799628169)
  ·
    refine ⟨197197774461281882099721127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262930365948375842799628169 197197774461281882099721127)
    ·
      refine ⟨295796661691922823149581691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197197774461281882099721127 295796661691922823149581691)
      ·
        refine ⟨443694992537884234724372537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295796661691922823149581691 443694992537884234724372537)
        ·
          refine ⟨332771244403413176043279403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443694992537884234724372537 332771244403413176043279403)
          ·
            refine ⟨499156866605119764064919105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332771244403413176043279403 499156866605119764064919105)
            ·
              refine ⟨374367649953839823048689329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499156866605119764064919105 374367649953839823048689329)
              ·
                refine ⟨280775737465379867286516997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374367649953839823048689329 280775737465379867286516997)
                ·
                  refine ⟨52645450774758725116221937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280775737465379867286516997 52645450774758725116221937)
                  ·
                    refine ⟨39484088081069043837166453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52645450774758725116221937 39484088081069043837166453)
                    ·
                      refine ⟨3701633257600222859734355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39484088081069043837166453 3701633257600222859734355)
                      ·
                        rfl

theorem cell23_7208905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_7208905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208905 prefixEnd_7208905 := by exact prefixLift 7208905
  have htrace : WordTrace (prefixWord ++ tailWord_7208905) baseStart_7208905 baseEnd_7208905 := by
    simpa [prefixWord, tailWord_7208905, baseEnd_7208905] using wordTrace_append hprefix tailTrace_7208905
  have hstable : (prefixWord ++ tailWord_7208905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208905).length < 2 ^ (prefixWord ++ tailWord_7208905).sum := by decide
  have hdescent : baseEnd_7208905 < baseStart_7208905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208919 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 3, 3, 2]
def baseStart_7208919 : Nat := 118140960795 + 7208919 * 2 ^ 59
def prefixEnd_7208919 : Nat := 4983230072969 + 3 ^ 40 * 7208919 * 2
def baseEnd_7208919 : Nat := 3701640446329385804959291

theorem tailTrace_7208919 : CollatzResearch.WordTrace tailWord_7208919 prefixEnd_7208919 3701640446329385804959291 := by
  unfold tailWord_7208919
  simp only [CollatzResearch.WordTrace]
  refine ⟨262930876570325123190637811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175287251046883415460425207 262930876570325123190637811)
  ·
    refine ⟨394396314855487684785956717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262930876570325123190637811 394396314855487684785956717)
    ·
      refine ⟨147898618070807881794733769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394396314855487684785956717 147898618070807881794733769)
      ·
        refine ⟨110923963553105911346050327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147898618070807881794733769 110923963553105911346050327)
        ·
          refine ⟨166385945329658867019075491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110923963553105911346050327 166385945329658867019075491)
          ·
            refine ⟨249578917994488300528613237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166385945329658867019075491 249578917994488300528613237)
            ·
              refine ⟨23398023561983278174557491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249578917994488300528613237 23398023561983278174557491)
              ·
                refine ⟨35097035342974917261836237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23398023561983278174557491 35097035342974917261836237)
                ·
                  refine ⟨13161388253615593973188589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35097035342974917261836237 13161388253615593973188589)
                  ·
                    refine ⟨4935520595105847739945721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13161388253615593973188589 4935520595105847739945721)
                    ·
                      refine ⟨3701640446329385804959291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4935520595105847739945721 3701640446329385804959291)
                      ·
                        rfl

theorem cell23_7208919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_7208919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208919 prefixEnd_7208919 := by exact prefixLift 7208919
  have htrace : WordTrace (prefixWord ++ tailWord_7208919) baseStart_7208919 baseEnd_7208919 := by
    simpa [prefixWord, tailWord_7208919, baseEnd_7208919] using wordTrace_append hprefix tailTrace_7208919
  have hstable : (prefixWord ++ tailWord_7208919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208919).length < 2 ^ (prefixWord ++ tailWord_7208919).sum := by decide
  have hdescent : baseEnd_7208919 < baseStart_7208919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208930 : List Nat := [3, 3, 3, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_7208930 : Nat := 118140960795 + 7208930 * 2 ^ 59
def prefixEnd_7208930 : Nat := 4983230072969 + 3 ^ 40 * 7208930 * 2
def baseEnd_7208930 : Nat := 3701646094616585261921741

theorem tailTrace_7208930 : CollatzResearch.WordTrace tailWord_7208930 prefixEnd_7208930 3701646094616585261921741 := by
  unfold tailWord_7208930
  simp only [CollatzResearch.WordTrace]
  refine ⟨65732819443321318017322061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175287518515523514712858829 65732819443321318017322061)
  ·
    refine ⟨24649807291245494256495773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65732819443321318017322061 24649807291245494256495773)
    ·
      refine ⟨9243677734217060346185915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24649807291245494256495773 9243677734217060346185915)
      ·
        refine ⟨13865516601325590519278873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9243677734217060346185915 13865516601325590519278873)
        ·
          refine ⟨10399137450994192889459155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13865516601325590519278873 10399137450994192889459155)
          ·
            refine ⟨15598706176491289334188733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10399137450994192889459155 15598706176491289334188733)
            ·
              refine ⟨5849514816184233500320775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15598706176491289334188733 5849514816184233500320775)
              ·
                refine ⟨8774272224276350250481163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5849514816184233500320775 8774272224276350250481163)
                ·
                  refine ⟨13161408336414525375721745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8774272224276350250481163 13161408336414525375721745)
                  ·
                    refine ⟨9871056252310894031791309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13161408336414525375721745 9871056252310894031791309)
                    ·
                      refine ⟨3701646094616585261921741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9871056252310894031791309 3701646094616585261921741)
                      ·
                        rfl

theorem cell23_7208930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_7208930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208930 prefixEnd_7208930 := by exact prefixLift 7208930
  have htrace : WordTrace (prefixWord ++ tailWord_7208930) baseStart_7208930 baseEnd_7208930 := by
    simpa [prefixWord, tailWord_7208930, baseEnd_7208930] using wordTrace_append hprefix tailTrace_7208930
  have hstable : (prefixWord ++ tailWord_7208930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208930).length < 2 ^ (prefixWord ++ tailWord_7208930).sum := by decide
  have hdescent : baseEnd_7208930 < baseStart_7208930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208952 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 2, 4, 3]
def baseStart_7208952 : Nat := 118140960795 + 7208952 * 2 ^ 59
def prefixEnd_7208952 : Nat := 4983230072969 + 3 ^ 40 * 7208952 * 2
def baseEnd_7208952 : Nat := 3701657391190984175846639

theorem tailTrace_7208952 : CollatzResearch.WordTrace tailWord_7208952 prefixEnd_7208952 3701657391190984175846639 := by
  unfold tailWord_7208952
  simp only [CollatzResearch.WordTrace]
  refine ⟨131466040089602784913294555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175288053452803713217726073 131466040089602784913294555)
  ·
    refine ⟨197199060134404177369941833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131466040089602784913294555 197199060134404177369941833)
    ·
      refine ⟨147899295100803133027456375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197199060134404177369941833 147899295100803133027456375)
      ·
        refine ⟨221848942651204699541184563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147899295100803133027456375 221848942651204699541184563)
        ·
          refine ⟨332773413976807049311776845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221848942651204699541184563 332773413976807049311776845)
          ·
            refine ⟨124790030241302643491916317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332773413976807049311776845 124790030241302643491916317)
            ·
              refine ⟨46796261340488491309468619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124790030241302643491916317 46796261340488491309468619)
              ·
                refine ⟨70194392010732736964202929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46796261340488491309468619 70194392010732736964202929)
                ·
                  refine ⟨52645794008049552723152197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70194392010732736964202929 52645794008049552723152197)
                  ·
                    refine ⟨9871086376509291135591037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52645794008049552723152197 9871086376509291135591037)
                    ·
                      refine ⟨3701657391190984175846639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9871086376509291135591037 3701657391190984175846639)
                      ·
                        rfl

theorem cell23_7208952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_7208952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208952 prefixEnd_7208952 := by exact prefixLift 7208952
  have htrace : WordTrace (prefixWord ++ tailWord_7208952) baseStart_7208952 baseEnd_7208952 := by
    simpa [prefixWord, tailWord_7208952, baseEnd_7208952] using wordTrace_append hprefix tailTrace_7208952
  have hstable : (prefixWord ++ tailWord_7208952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208952).length < 2 ^ (prefixWord ++ tailWord_7208952).sum := by decide
  have hdescent : baseEnd_7208952 < baseStart_7208952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7208972 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 7]
def baseStart_7208972 : Nat := 118140960795 + 7208972 * 2 ^ 59
def prefixEnd_7208972 : Nat := 4983230072969 + 3 ^ 40 * 7208972 * 2
def baseEnd_7208972 : Nat := 411296406756008233066283

theorem tailTrace_7208972 : CollatzResearch.WordTrace tailWord_7208972 prefixEnd_7208972 411296406756008233066283 := by
  unfold tailWord_7208972
  simp only [CollatzResearch.WordTrace]
  refine ⟨131466404819566556621158585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175288539759422075494878113 131466404819566556621158585)
  ·
    refine ⟨98599803614674917465868939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131466404819566556621158585 98599803614674917465868939)
    ·
      refine ⟨147899705422012376198803409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98599803614674917465868939 147899705422012376198803409)
      ·
        refine ⟨110924779066509282149102557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147899705422012376198803409 110924779066509282149102557)
        ·
          refine ⟨41596792149940980805913459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110924779066509282149102557 41596792149940980805913459)
          ·
            refine ⟨62395188224911471208870189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41596792149940980805913459 62395188224911471208870189)
            ·
              refine ⟨23398195584341801703326321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62395188224911471208870189 23398195584341801703326321)
              ·
                refine ⟨17548646688256351277494741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23398195584341801703326321 17548646688256351277494741)
                ·
                  refine ⟨411296406756008233066283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17548646688256351277494741 411296406756008233066283)
                  ·
                    rfl

theorem cell23_7208972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_7208972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7208972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7208972 prefixEnd_7208972 := by exact prefixLift 7208972
  have htrace : WordTrace (prefixWord ++ tailWord_7208972) baseStart_7208972 baseEnd_7208972 := by
    simpa [prefixWord, tailWord_7208972, baseEnd_7208972] using wordTrace_append hprefix tailTrace_7208972
  have hstable : (prefixWord ++ tailWord_7208972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7208972).length < 2 ^ (prefixWord ++ tailWord_7208972).sum := by decide
  have hdescent : baseEnd_7208972 < baseStart_7208972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7208972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209000 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_7209000 : Nat := 118140960795 + 7209000 * 2 ^ 59
def prefixEnd_7209000 : Nat := 4983230072969 + 3 ^ 40 * 7209000 * 2
def baseEnd_7209000 : Nat := 3701682038262399988046419

theorem tailTrace_7209000 : CollatzResearch.WordTrace tailWord_7209000 prefixEnd_7209000 3701682038262399988046419 := by
  unfold tailWord_7209000
  simp only [CollatzResearch.WordTrace]
  refine ⟨131466915441515837012168227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175289220588687782682890969 131466915441515837012168227)
  ·
    refine ⟨197200373162273755518252341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131466915441515837012168227 197200373162273755518252341)
    ·
      refine ⟨18487534983963164579836157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197200373162273755518252341 18487534983963164579836157)
      ·
        refine ⟨6932825618986186717438559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18487534983963164579836157 6932825618986186717438559)
        ·
          refine ⟨10399238428479280076157839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6932825618986186717438559 10399238428479280076157839)
          ·
            refine ⟨15598857642718920114236759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10399238428479280076157839 15598857642718920114236759)
            ·
              refine ⟨23398286464078380171355139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15598857642718920114236759 23398286464078380171355139)
              ·
                refine ⟨35097429696117570257032709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23398286464078380171355139 35097429696117570257032709)
                ·
                  refine ⟨6580768068022044423193633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35097429696117570257032709 6580768068022044423193633)
                  ·
                    refine ⟨4935576051016533317395225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6580768068022044423193633 4935576051016533317395225)
                    ·
                      refine ⟨3701682038262399988046419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4935576051016533317395225 3701682038262399988046419)
                      ·
                        rfl

theorem cell23_7209000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_7209000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209000 prefixEnd_7209000 := by exact prefixLift 7209000
  have htrace : WordTrace (prefixWord ++ tailWord_7209000) baseStart_7209000 baseEnd_7209000 := by
    simpa [prefixWord, tailWord_7209000, baseEnd_7209000] using wordTrace_append hprefix tailTrace_7209000
  have hstable : (prefixWord ++ tailWord_7209000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209000).length < 2 ^ (prefixWord ++ tailWord_7209000).sum := by decide
  have hdescent : baseEnd_7209000 < baseStart_7209000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209006 : List Nat := [4, 1, 3, 1, 1, 2, 2, 4, 5]
def baseStart_7209006 : Nat := 118140960795 + 7209006 * 2 ^ 59
def prefixEnd_7209006 : Nat := 4983230072969 + 3 ^ 40 * 7209006 * 2
def baseEnd_7209006 : Nat := 411298346571814107174599

theorem tailTrace_7209006 : CollatzResearch.WordTrace tailWord_7209006 prefixEnd_7209006 411298346571814107174599 := by
  unfold tailWord_7209006
  simp only [CollatzResearch.WordTrace]
  refine ⟨32866756215126242131131859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175289366480673291366036581 32866756215126242131131859)
  ·
    refine ⟨49300134322689363196697789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32866756215126242131131859 49300134322689363196697789)
    ·
      refine ⟨18487550371008511198761671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49300134322689363196697789 18487550371008511198761671)
      ·
        refine ⟨27731325556512766798142507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18487550371008511198761671 27731325556512766798142507)
        ·
          refine ⟨41596988334769150197213761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27731325556512766798142507 41596988334769150197213761)
          ·
            refine ⟨31197741251076862647910321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41596988334769150197213761 31197741251076862647910321)
            ·
              refine ⟨23398305938307646985932741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31197741251076862647910321 23398305938307646985932741)
              ·
                refine ⟨4387182363432683809862389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23398305938307646985932741 4387182363432683809862389)
                ·
                  refine ⟨411298346571814107174599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4387182363432683809862389 411298346571814107174599)
                  ·
                    rfl

theorem cell23_7209006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_7209006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209006 prefixEnd_7209006 := by exact prefixLift 7209006
  have htrace : WordTrace (prefixWord ++ tailWord_7209006) baseStart_7209006 baseEnd_7209006 := by
    simpa [prefixWord, tailWord_7209006, baseEnd_7209006] using wordTrace_append hprefix tailTrace_7209006
  have hstable : (prefixWord ++ tailWord_7209006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209006).length < 2 ^ (prefixWord ++ tailWord_7209006).sum := by decide
  have hdescent : baseEnd_7209006 < baseStart_7209006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209059 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 3]
def baseStart_7209059 : Nat := 118140960795 + 7209059 * 2 ^ 59
def prefixEnd_7209059 : Nat := 4983230072969 + 3 ^ 40 * 7209059 * 2
def baseEnd_7209059 : Nat := 3701712333621015257208647

theorem tailTrace_7209059 : CollatzResearch.WordTrace tailWord_7209059 prefixEnd_7209059 3701712333621015257208647 := by
  unfold tailWord_7209059
  simp only [CollatzResearch.WordTrace]
  refine ⟨262935982789817927100734231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175290655193211951400489487 262935982789817927100734231)
  ·
    refine ⟨394403974184726890651101347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262935982789817927100734231 394403974184726890651101347)
    ·
      refine ⟨591605961277090335976652021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394403974184726890651101347 591605961277090335976652021)
      ·
        refine ⟨55463058869727218997811127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 591605961277090335976652021 55463058869727218997811127)
        ·
          refine ⟨83194588304590828496716691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55463058869727218997811127 83194588304590828496716691)
          ·
            refine ⟨124791882456886242745075037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83194588304590828496716691 124791882456886242745075037)
            ·
              refine ⟨46796955921332341029403139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124791882456886242745075037 46796955921332341029403139)
              ·
                refine ⟨70195433881998511544104709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46796955921332341029403139 70195433881998511544104709)
                ·
                  refine ⟨13161643852874720914519633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70195433881998511544104709 13161643852874720914519633)
                  ·
                    refine ⟨9871232889656040685889725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13161643852874720914519633 9871232889656040685889725)
                    ·
                      refine ⟨3701712333621015257208647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9871232889656040685889725 3701712333621015257208647)
                      ·
                        rfl

theorem cell23_7209059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_7209059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209059 prefixEnd_7209059 := by exact prefixLift 7209059
  have htrace : WordTrace (prefixWord ++ tailWord_7209059) baseStart_7209059 baseEnd_7209059 := by
    simpa [prefixWord, tailWord_7209059, baseEnd_7209059] using wordTrace_append hprefix tailTrace_7209059
  have hstable : (prefixWord ++ tailWord_7209059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209059).length < 2 ^ (prefixWord ++ tailWord_7209059).sum := by decide
  have hdescent : baseEnd_7209059 < baseStart_7209059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209079 : List Nat := [1, 1, 3, 1, 1, 6, 1, 3, 6]
def baseStart_7209079 : Nat := 118140960795 + 7209079 * 2 ^ 59
def prefixEnd_7209079 : Nat := 4983230072969 + 3 ^ 40 * 7209079 * 2
def baseEnd_7209079 : Nat := 411302511470456130995395

theorem tailTrace_7209079 : CollatzResearch.WordTrace tailWord_7209079 prefixEnd_7209079 411302511470456130995395 := by
  unfold tailWord_7209079
  simp only [CollatzResearch.WordTrace]
  refine ⟨262936712249745470516462291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175291141499830313677641527 262936712249745470516462291)
  ·
    refine ⟨394405068374618205774693437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262936712249745470516462291 394405068374618205774693437)
    ·
      refine ⟨147901900640481827165510039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394405068374618205774693437 147901900640481827165510039)
      ·
        refine ⟨221852850960722740748265059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147901900640481827165510039 221852850960722740748265059)
        ·
          refine ⟨332779276441084111122397589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221852850960722740748265059 332779276441084111122397589)
          ·
            refine ⟨15599028583175817708862387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 332779276441084111122397589 15599028583175817708862387)
            ·
              refine ⟨23398542874763726563293581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15599028583175817708862387 23398542874763726563293581)
              ·
                refine ⟨8774453578036397461235093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23398542874763726563293581 8774453578036397461235093)
                ·
                  refine ⟨411302511470456130995395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8774453578036397461235093 411302511470456130995395)
                  ·
                    rfl

theorem cell23_7209079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 6].length) (baseStart_7209079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209079 prefixEnd_7209079 := by exact prefixLift 7209079
  have htrace : WordTrace (prefixWord ++ tailWord_7209079) baseStart_7209079 baseEnd_7209079 := by
    simpa [prefixWord, tailWord_7209079, baseEnd_7209079] using wordTrace_append hprefix tailTrace_7209079
  have hstable : (prefixWord ++ tailWord_7209079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209079).length < 2 ^ (prefixWord ++ tailWord_7209079).sum := by decide
  have hdescent : baseEnd_7209079 < baseStart_7209079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209139 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 6, 4]
def baseStart_7209139 : Nat := 118140960795 + 7209139 * 2 ^ 59
def prefixEnd_7209139 : Nat := 4983230072969 + 3 ^ 40 * 7209139 * 2
def baseEnd_7209139 : Nat := 1233917804024458314736093

theorem tailTrace_7209139 : CollatzResearch.WordTrace tailWord_7209139 prefixEnd_7209139 1233917804024458314736093 := by
  unfold tailWord_7209139
  simp only [CollatzResearch.WordTrace]
  refine ⟨262938900629528100763646471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175292600419685400509097647 262938900629528100763646471)
  ·
    refine ⟨394408350944292151145469707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262938900629528100763646471 394408350944292151145469707)
    ·
      refine ⟨591612526416438226718204561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394408350944292151145469707 591612526416438226718204561)
      ·
        refine ⟨443709394812328670038653421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591612526416438226718204561 443709394812328670038653421)
        ·
          refine ⟨166391023054623251264495033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443709394812328670038653421 166391023054623251264495033)
          ·
            refine ⟨124793267290967438448371275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166391023054623251264495033 124793267290967438448371275)
            ·
              refine ⟨187189900936451157672556913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124793267290967438448371275 187189900936451157672556913)
              ·
                refine ⟨140392425702338368254417685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187189900936451157672556913 140392425702338368254417685)
                ·
                  refine ⟨6580894954797111011925829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140392425702338368254417685 6580894954797111011925829)
                  ·
                    refine ⟨1233917804024458314736093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6580894954797111011925829 1233917804024458314736093)
                    ·
                      rfl

theorem cell23_7209139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 4].length) (baseStart_7209139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209139 prefixEnd_7209139 := by exact prefixLift 7209139
  have htrace : WordTrace (prefixWord ++ tailWord_7209139) baseStart_7209139 baseEnd_7209139 := by
    simpa [prefixWord, tailWord_7209139, baseEnd_7209139] using wordTrace_append hprefix tailTrace_7209139
  have hstable : (prefixWord ++ tailWord_7209139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209139).length < 2 ^ (prefixWord ++ tailWord_7209139).sum := by decide
  have hdescent : baseEnd_7209139 < baseStart_7209139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209156 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_7209156 : Nat := 118140960795 + 7209156 * 2 ^ 59
def prefixEnd_7209156 : Nat := 4983230072969 + 3 ^ 40 * 7209156 * 2
def baseEnd_7209156 : Nat := 1233920713748167125898567

theorem tailTrace_7209156 : CollatzResearch.WordTrace tailWord_7209156 prefixEnd_7209156 1233920713748167125898567 := by
  unfold tailWord_7209156
  simp only [CollatzResearch.WordTrace]
  refine ⟨131469760335233256333507661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175293013780311008444676881 131469760335233256333507661)
  ·
    refine ⟨49301160125712471125065373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131469760335233256333507661 49301160125712471125065373)
    ·
      refine ⟨18487935047142176671899515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49301160125712471125065373 18487935047142176671899515)
      ·
        refine ⟨27731902570713265007849273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18487935047142176671899515 27731902570713265007849273)
        ·
          refine ⟨20798926928034948755886955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27731902570713265007849273 20798926928034948755886955)
          ·
            refine ⟨31198390392052423133830433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20798926928034948755886955 31198390392052423133830433)
            ·
              refine ⟨23398792794039317350372825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31198390392052423133830433 23398792794039317350372825)
              ·
                refine ⟨17549094595529488012779619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23398792794039317350372825 17549094595529488012779619)
                ·
                  refine ⟨26323641893294232019169429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17549094595529488012779619 26323641893294232019169429)
                  ·
                    refine ⟨1233920713748167125898567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26323641893294232019169429 1233920713748167125898567)
                    ·
                      rfl

theorem cell23_7209156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_7209156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209156 prefixEnd_7209156 := by exact prefixLift 7209156
  have htrace : WordTrace (prefixWord ++ tailWord_7209156) baseStart_7209156 baseEnd_7209156 := by
    simpa [prefixWord, tailWord_7209156, baseEnd_7209156] using wordTrace_append hprefix tailTrace_7209156
  have hstable : (prefixWord ++ tailWord_7209156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209156).length < 2 ^ (prefixWord ++ tailWord_7209156).sum := by decide
  have hdescent : baseEnd_7209156 < baseStart_7209156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209173 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 4, 4]
def baseStart_7209173 : Nat := 118140960795 + 7209173 * 2 ^ 59
def prefixEnd_7209173 : Nat := 4983230072969 + 3 ^ 40 * 7209173 * 2
def baseEnd_7209173 : Nat := 1233923623471875937061041

theorem tailTrace_7209173 : CollatzResearch.WordTrace tailWord_7209173 prefixEnd_7209173 1233923623471875937061041 := by
  unfold tailWord_7209173
  simp only [CollatzResearch.WordTrace]
  refine ⟨262940140711404924570384173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175293427140936616380256115 262940140711404924570384173)
  ·
    refine ⟨98602552766776846713894065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262940140711404924570384173 98602552766776846713894065)
    ·
      refine ⟨73951914575082635035420549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98602552766776846713894065 73951914575082635035420549)
      ·
        refine ⟨13865983982827994069141353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73951914575082635035420549 13865983982827994069141353)
        ·
          refine ⟨10399487987120995551856015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13865983982827994069141353 10399487987120995551856015)
          ·
            refine ⟨15599231980681493327784023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10399487987120995551856015 15599231980681493327784023)
            ·
              refine ⟨23398847971022239991676035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15599231980681493327784023 23398847971022239991676035)
              ·
                refine ⟨35098271956533359987514053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23398847971022239991676035 35098271956533359987514053)
                ·
                  refine ⟨6580925991850004997658885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35098271956533359987514053 6580925991850004997658885)
                  ·
                    refine ⟨1233923623471875937061041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6580925991850004997658885 1233923623471875937061041)
                    ·
                      rfl

theorem cell23_7209173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_7209173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209173 prefixEnd_7209173 := by exact prefixLift 7209173
  have htrace : WordTrace (prefixWord ++ tailWord_7209173) baseStart_7209173 baseEnd_7209173 := by
    simpa [prefixWord, tailWord_7209173, baseEnd_7209173] using wordTrace_append hprefix tailTrace_7209173
  have hstable : (prefixWord ++ tailWord_7209173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209173).length < 2 ^ (prefixWord ++ tailWord_7209173).sum := by decide
  have hdescent : baseEnd_7209173 < baseStart_7209173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209179 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 3]
def baseStart_7209179 : Nat := 118140960795 + 7209179 * 2 ^ 59
def prefixEnd_7209179 : Nat := 4983230072969 + 3 ^ 40 * 7209179 * 2
def baseEnd_7209179 : Nat := 3701773951299554787708095

theorem tailTrace_7209179 : CollatzResearch.WordTrace tailWord_7209179 prefixEnd_7209179 3701773951299554787708095 := by
  unfold tailWord_7209179
  simp only [CollatzResearch.WordTrace]
  refine ⟨262940359549383187595102591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175293573032922125063401727 262940359549383187595102591)
  ·
    refine ⟨394410539324074781392653887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262940359549383187595102591 394410539324074781392653887)
    ·
      refine ⟨591615808986112172088980831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394410539324074781392653887 591615808986112172088980831)
      ·
        refine ⟨887423713479168258133471247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591615808986112172088980831 887423713479168258133471247)
        ·
          refine ⟨1331135570218752387200206871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887423713479168258133471247 1331135570218752387200206871)
          ·
            refine ⟨1996703355328128580800310307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331135570218752387200206871 1996703355328128580800310307)
            ·
              refine ⟨2995055032992192871200465461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996703355328128580800310307 2995055032992192871200465461)
              ·
                refine ⟨280786409343018081675043637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2995055032992192871200465461 280786409343018081675043637)
                ·
                  refine ⟨26323725875907945157035341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 280786409343018081675043637 26323725875907945157035341)
                  ·
                    refine ⟨9871397203465479433888253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26323725875907945157035341 9871397203465479433888253)
                    ·
                      refine ⟨3701773951299554787708095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9871397203465479433888253 3701773951299554787708095)
                      ·
                        rfl

theorem cell23_7209179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 3].length) (baseStart_7209179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209179 prefixEnd_7209179 := by exact prefixLift 7209179
  have htrace : WordTrace (prefixWord ++ tailWord_7209179) baseStart_7209179 baseEnd_7209179 := by
    simpa [prefixWord, tailWord_7209179, baseEnd_7209179] using wordTrace_append hprefix tailTrace_7209179
  have hstable : (prefixWord ++ tailWord_7209179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209179).length < 2 ^ (prefixWord ++ tailWord_7209179).sum := by decide
  have hdescent : baseEnd_7209179 < baseStart_7209179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209247 : List Nat := [1, 1, 2, 4, 3, 3, 2, 1, 2, 1, 3]
def baseStart_7209247 : Nat := 118140960795 + 7209247 * 2 ^ 59
def prefixEnd_7209247 : Nat := 4983230072969 + 3 ^ 40 * 7209247 * 2
def baseEnd_7209247 : Nat := 3701808867984060521657783

theorem tailTrace_7209247 : CollatzResearch.WordTrace tailWord_7209247 prefixEnd_7209247 3701808867984060521657783 := by
  unfold tailWord_7209247
  simp only [CollatzResearch.WordTrace]
  refine ⟨262942839713136835208577995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175295226475424556805718663 262942839713136835208577995)
  ·
    refine ⟨394414259569705252812866993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262942839713136835208577995 394414259569705252812866993)
    ·
      refine ⟨295810694677278939609650245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394414259569705252812866993 295810694677278939609650245)
      ·
        refine ⟨55464505251989801176809421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295810694677278939609650245 55464505251989801176809421)
        ·
          refine ⟨20799189469496175441303533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55464505251989801176809421 20799189469496175441303533)
          ·
            refine ⟨7799696051061065790488825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20799189469496175441303533 7799696051061065790488825)
            ·
              refine ⟨5849772038295799342866619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7799696051061065790488825 5849772038295799342866619)
              ·
                refine ⟨8774658057443699014299929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5849772038295799342866619 8774658057443699014299929)
                ·
                  refine ⟨6580993543082774260724947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8774658057443699014299929 6580993543082774260724947)
                  ·
                    refine ⟨9871490314624161391087421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6580993543082774260724947 9871490314624161391087421)
                    ·
                      refine ⟨3701808867984060521657783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9871490314624161391087421 3701808867984060521657783)
                      ·
                        rfl

theorem cell23_7209247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_7209247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209247 prefixEnd_7209247 := by exact prefixLift 7209247
  have htrace : WordTrace (prefixWord ++ tailWord_7209247) baseStart_7209247 baseEnd_7209247 := by
    simpa [prefixWord, tailWord_7209247, baseEnd_7209247] using wordTrace_append hprefix tailTrace_7209247
  have hstable : (prefixWord ++ tailWord_7209247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209247).length < 2 ^ (prefixWord ++ tailWord_7209247).sum := by decide
  have hdescent : baseEnd_7209247 < baseStart_7209247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209289 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 3, 7]
def baseStart_7209289 : Nat := 118140960795 + 7209289 * 2 ^ 59
def prefixEnd_7209289 : Nat := 4983230072969 + 3 ^ 40 * 7209289 * 2
def baseEnd_7209289 : Nat := 1233943478057183119110863

theorem tailTrace_7209289 : CollatzResearch.WordTrace tailWord_7209289 prefixEnd_7209289 1233943478057183119110863 := by
  unfold tailWord_7209289
  simp only [CollatzResearch.WordTrace]
  refine ⟨262944371578984676381606921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175296247719323117587737947 262944371578984676381606921)
  ·
    refine ⟨197208278684238507286205191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262944371578984676381606921 197208278684238507286205191)
    ·
      refine ⟨295812418026357760929307787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197208278684238507286205191 295812418026357760929307787)
      ·
        refine ⟨443718627039536641393961681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295812418026357760929307787 443718627039536641393961681)
        ·
          refine ⟨332788970279652481045471261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443718627039536641393961681 332788970279652481045471261)
          ·
            refine ⟨124795863854869680392051723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332788970279652481045471261 124795863854869680392051723)
            ·
              refine ⟨187193795782304520588077585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124795863854869680392051723 187193795782304520588077585)
              ·
                refine ⟨140395346836728390441058189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187193795782304520588077585 140395346836728390441058189)
                ·
                  refine ⟨52648255063773146415396821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140395346836728390441058189 52648255063773146415396821)
                  ·
                    refine ⟨1233943478057183119110863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52648255063773146415396821 1233943478057183119110863)
                    ·
                      rfl

theorem cell23_7209289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_7209289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209289 prefixEnd_7209289 := by exact prefixLift 7209289
  have htrace : WordTrace (prefixWord ++ tailWord_7209289) baseStart_7209289 baseEnd_7209289 := by
    simpa [prefixWord, tailWord_7209289, baseEnd_7209289] using wordTrace_append hprefix tailTrace_7209289
  have hstable : (prefixWord ++ tailWord_7209289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209289).length < 2 ^ (prefixWord ++ tailWord_7209289).sum := by decide
  have hdescent : baseEnd_7209289 < baseStart_7209289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209299 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 7]
def baseStart_7209299 : Nat := 118140960795 + 7209299 * 2 ^ 59
def prefixEnd_7209299 : Nat := 4983230072969 + 3 ^ 40 * 7209299 * 2
def baseEnd_7209299 : Nat := 3701835568978094318207543

theorem tailTrace_7209299 : CollatzResearch.WordTrace tailWord_7209299 prefixEnd_7209299 3701835568978094318207543 := by
  unfold tailWord_7209299
  simp only [CollatzResearch.WordTrace]
  refine ⟨262944736308948448089470951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175296490872632298726313967 262944736308948448089470951)
  ·
    refine ⟨394417104463422672134206427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262944736308948448089470951 394417104463422672134206427)
    ·
      refine ⟨591625656695134008201309641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394417104463422672134206427 591625656695134008201309641)
      ·
        refine ⟨443719242521350506150982231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591625656695134008201309641 443719242521350506150982231)
        ·
          refine ⟨665578863782025759226473347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443719242521350506150982231 665578863782025759226473347)
          ·
            refine ⟨998368295673038638839710021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665578863782025759226473347 998368295673038638839710021)
            ·
              refine ⟨187194055438694744782445629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 998368295673038638839710021 187194055438694744782445629)
              ·
                refine ⟨70197770789510529293417111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187194055438694744782445629 70197770789510529293417111)
                ·
                  refine ⟨105296656184265793940125667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70197770789510529293417111 105296656184265793940125667)
                  ·
                    refine ⟨157944984276398690910188501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105296656184265793940125667 157944984276398690910188501)
                    ·
                      refine ⟨3701835568978094318207543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157944984276398690910188501 3701835568978094318207543)
                      ·
                        rfl

theorem cell23_7209299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_7209299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209299 prefixEnd_7209299 := by exact prefixLift 7209299
  have htrace : WordTrace (prefixWord ++ tailWord_7209299) baseStart_7209299 baseEnd_7209299 := by
    simpa [prefixWord, tailWord_7209299, baseEnd_7209299] using wordTrace_append hprefix tailTrace_7209299
  have hstable : (prefixWord ++ tailWord_7209299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209299).length < 2 ^ (prefixWord ++ tailWord_7209299).sum := by decide
  have hdescent : baseEnd_7209299 < baseStart_7209299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209353 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 3, 4]
def baseStart_7209353 : Nat := 118140960795 + 7209353 * 2 ^ 59
def prefixEnd_7209353 : Nat := 4983230072969 + 3 ^ 40 * 7209353 * 2
def baseEnd_7209353 : Nat := 1233954432311145702310765

theorem tailTrace_7209353 : CollatzResearch.WordTrace tailWord_7209353 prefixEnd_7209353 1233954432311145702310765 := by
  unfold tailWord_7209353
  simp only [CollatzResearch.WordTrace]
  refine ⟨262946705850752815311936713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175297803900501876874624475 262946705850752815311936713)
  ·
    refine ⟨197210029388064611483952535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262946705850752815311936713 197210029388064611483952535)
    ·
      refine ⟨295815044082096917225928803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197210029388064611483952535 295815044082096917225928803)
      ·
        refine ⟨443722566123145375838893205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295815044082096917225928803 443722566123145375838893205)
        ·
          refine ⟨20799495287022439492448119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 443722566123145375838893205 20799495287022439492448119)
          ·
            refine ⟨31199242930533659238672179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20799495287022439492448119 31199242930533659238672179)
            ·
              refine ⟨46798864395800488858008269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31199242930533659238672179 46798864395800488858008269)
              ·
                refine ⟨17549574148425183321753101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46798864395800488858008269 17549574148425183321753101)
                ·
                  refine ⟨6581090305659443745657413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17549574148425183321753101 6581090305659443745657413)
                  ·
                    refine ⟨1233954432311145702310765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6581090305659443745657413 1233954432311145702310765)
                    ·
                      rfl

theorem cell23_7209353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 4].length) (baseStart_7209353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209353 prefixEnd_7209353 := by exact prefixLift 7209353
  have htrace : WordTrace (prefixWord ++ tailWord_7209353) baseStart_7209353 baseEnd_7209353 := by
    simpa [prefixWord, tailWord_7209353, baseEnd_7209353] using wordTrace_append hprefix tailTrace_7209353
  have hstable : (prefixWord ++ tailWord_7209353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209353).length < 2 ^ (prefixWord ++ tailWord_7209353).sum := by decide
  have hdescent : baseEnd_7209353 < baseStart_7209353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209404 : List Nat := [2, 2, 2, 4, 1, 2, 3, 2, 1, 4]
def baseStart_7209404 : Nat := 118140960795 + 7209404 * 2 ^ 59
def prefixEnd_7209404 : Nat := 4983230072969 + 3 ^ 40 * 7209404 * 2
def baseEnd_7209404 : Nat := 1233963161482272135798187

theorem tailTrace_7209404 : CollatzResearch.WordTrace tailWord_7209404 prefixEnd_7209404 1233963161482272135798187 := by
  unfold tailWord_7209404
  simp only [CollatzResearch.WordTrace]
  refine ⟨131474282986784025511021633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175299043982378700681362177 131474282986784025511021633)
  ·
    refine ⟨98605712240088019133266225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131474282986784025511021633 98605712240088019133266225)
    ·
      refine ⟨73954284180066014349949669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98605712240088019133266225 73954284180066014349949669)
      ·
        refine ⟨13866428283762377690615563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73954284180066014349949669 13866428283762377690615563)
        ·
          refine ⟨20799642425643566535923345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13866428283762377690615563 20799642425643566535923345)
          ·
            refine ⟨15599731819232674901942509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20799642425643566535923345 15599731819232674901942509)
            ·
              refine ⟨5849899432212253088228441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15599731819232674901942509 5849899432212253088228441)
              ·
                refine ⟨4387424574159189816171331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5849899432212253088228441 4387424574159189816171331)
                ·
                  refine ⟨6581136861238784724256997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387424574159189816171331 6581136861238784724256997)
                  ·
                    refine ⟨1233963161482272135798187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6581136861238784724256997 1233963161482272135798187)
                    ·
                      rfl

theorem cell23_7209404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_7209404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209404 prefixEnd_7209404 := by exact prefixLift 7209404
  have htrace : WordTrace (prefixWord ++ tailWord_7209404) baseStart_7209404 baseEnd_7209404 := by
    simpa [prefixWord, tailWord_7209404, baseEnd_7209404] using wordTrace_append hprefix tailTrace_7209404
  have hstable : (prefixWord ++ tailWord_7209404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209404).length < 2 ^ (prefixWord ++ tailWord_7209404).sum := by decide
  have hdescent : baseEnd_7209404 < baseStart_7209404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209430 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_7209430 : Nat := 118140960795 + 7209430 * 2 ^ 59
def prefixEnd_7209430 : Nat := 4983230072969 + 3 ^ 40 * 7209430 * 2
def baseEnd_7209430 : Nat := 1233967611647944435223147

theorem tailTrace_7209430 : CollatzResearch.WordTrace tailWord_7209430 prefixEnd_7209430 1233967611647944435223147 := by
  unfold tailWord_7209430
  simp only [CollatzResearch.WordTrace]
  refine ⟨16434344641967116091405609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175299676180982571641659829 16434344641967116091405609)
  ·
    refine ⟨12325758481475337068554207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16434344641967116091405609 12325758481475337068554207)
    ·
      refine ⟨18488637722213005602831311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12325758481475337068554207 18488637722213005602831311)
      ·
        refine ⟨27732956583319508404246967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18488637722213005602831311 27732956583319508404246967)
        ·
          refine ⟨41599434874979262606370451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27732956583319508404246967 41599434874979262606370451)
          ·
            refine ⟨62399152312468893909555677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41599434874979262606370451 62399152312468893909555677)
            ·
              refine ⟨23399682117175835216083379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62399152312468893909555677 23399682117175835216083379)
              ·
                refine ⟨35099523175763752824125069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23399682117175835216083379 35099523175763752824125069)
                ·
                  refine ⟨13162321190911407309046901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35099523175763752824125069 13162321190911407309046901)
                  ·
                    refine ⟨1233967611647944435223147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13162321190911407309046901 1233967611647944435223147)
                    ·
                      rfl

theorem cell23_7209430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_7209430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209430 prefixEnd_7209430 := by exact prefixLift 7209430
  have htrace : WordTrace (prefixWord ++ tailWord_7209430) baseStart_7209430 baseEnd_7209430 := by
    simpa [prefixWord, tailWord_7209430, baseEnd_7209430] using wordTrace_append hprefix tailTrace_7209430
  have hstable : (prefixWord ++ tailWord_7209430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209430).length < 2 ^ (prefixWord ++ tailWord_7209430).sum := by decide
  have hdescent : baseEnd_7209430 < baseStart_7209430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209433 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 3, 1, 4]
def baseStart_7209433 : Nat := 118140960795 + 7209433 * 2 ^ 59
def prefixEnd_7209433 : Nat := 4983230072969 + 3 ^ 40 * 7209433 * 2
def baseEnd_7209433 : Nat := 3701904375385796793931927

theorem tailTrace_7209433 : CollatzResearch.WordTrace tailWord_7209433 prefixEnd_7209433 3701904375385796793931927 := by
  unfold tailWord_7209433
  simp only [CollatzResearch.WordTrace]
  refine ⟨262949623690462988974848953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175299749126975325983232635 262949623690462988974848953)
  ·
    refine ⟨197212217767847241731136715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262949623690462988974848953 197212217767847241731136715)
    ·
      refine ⟨295818326651770862596705073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197212217767847241731136715 295818326651770862596705073)
      ·
        refine ⟨221863744988828146947528805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295818326651770862596705073 221863744988828146947528805)
        ·
          refine ⟨41599452185405277552661651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221863744988828146947528805 41599452185405277552661651)
          ·
            refine ⟨62399178278107916328992477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41599452185405277552661651 62399178278107916328992477)
            ·
              refine ⟨23399691854290468623372179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62399178278107916328992477 23399691854290468623372179)
              ·
                refine ⟨35099537781435702935058269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23399691854290468623372179 35099537781435702935058269)
                ·
                  refine ⟨13162326668038388600646851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35099537781435702935058269 13162326668038388600646851)
                  ·
                    refine ⟨19743490002057582900970277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13162326668038388600646851 19743490002057582900970277)
                    ·
                      refine ⟨3701904375385796793931927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19743490002057582900970277 3701904375385796793931927)
                      ·
                        rfl

theorem cell23_7209433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_7209433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209433 prefixEnd_7209433 := by exact prefixLift 7209433
  have htrace : WordTrace (prefixWord ++ tailWord_7209433) baseStart_7209433 baseEnd_7209433 := by
    simpa [prefixWord, tailWord_7209433, baseEnd_7209433] using wordTrace_append hprefix tailTrace_7209433
  have hstable : (prefixWord ++ tailWord_7209433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209433).length < 2 ^ (prefixWord ++ tailWord_7209433).sum := by decide
  have hdescent : baseEnd_7209433 < baseStart_7209433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209437 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_7209437 : Nat := 118140960795 + 7209437 * 2 ^ 59
def prefixEnd_7209437 : Nat := 4983230072969 + 3 ^ 40 * 7209437 * 2
def baseEnd_7209437 : Nat := 3701906429308414778281909

theorem tailTrace_7209437 : CollatzResearch.WordTrace tailWord_7209437 prefixEnd_7209437 3701906429308414778281909 := by
  unfold tailWord_7209437
  simp only [CollatzResearch.WordTrace]
  refine ⟨262949769582448497657994565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175299846388298998438663043 262949769582448497657994565)
  ·
    refine ⟨49303081796709093310873981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262949769582448497657994565 49303081796709093310873981)
    ·
      refine ⟨18488655673765909991577743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49303081796709093310873981 18488655673765909991577743)
      ·
        refine ⟨27732983510648864987366615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18488655673765909991577743 27732983510648864987366615)
        ·
          refine ⟨41599475265973297481049923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27732983510648864987366615 41599475265973297481049923)
          ·
            refine ⟨62399212898959946221574885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41599475265973297481049923 62399212898959946221574885)
            ·
              refine ⟨11699852418554989916545291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62399212898959946221574885 11699852418554989916545291)
              ·
                refine ⟨17549778627832484874817937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11699852418554989916545291 17549778627832484874817937)
                ·
                  refine ⟨13162333970874363656113453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17549778627832484874817937 13162333970874363656113453)
                  ·
                    refine ⟨4935875239077886371042545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13162333970874363656113453 4935875239077886371042545)
                    ·
                      refine ⟨3701906429308414778281909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4935875239077886371042545 3701906429308414778281909)
                      ·
                        rfl

theorem cell23_7209437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_7209437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209437 prefixEnd_7209437 := by exact prefixLift 7209437
  have htrace : WordTrace (prefixWord ++ tailWord_7209437) baseStart_7209437 baseEnd_7209437 := by
    simpa [prefixWord, tailWord_7209437, baseEnd_7209437] using wordTrace_append hprefix tailTrace_7209437
  have hstable : (prefixWord ++ tailWord_7209437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209437).length < 2 ^ (prefixWord ++ tailWord_7209437).sum := by decide
  have hdescent : baseEnd_7209437 < baseStart_7209437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209461 : List Nat := [1, 3, 5, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_7209461 : Nat := 118140960795 + 7209461 * 2 ^ 59
def prefixEnd_7209461 : Nat := 4983230072969 + 3 ^ 40 * 7209461 * 2
def baseEnd_7209461 : Nat := 3701918752844122684381799

theorem tailTrace_7209461 : CollatzResearch.WordTrace tailWord_7209461 prefixEnd_7209461 3701918752844122684381799 := by
  unfold tailWord_7209461
  simp only [CollatzResearch.WordTrace]
  refine ⟨262950644934361549756868237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175300429956241033171245491 262950644934361549756868237)
  ·
    refine ⟨98606491850385581158825589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262950644934361549756868237 98606491850385581158825589)
    ·
      refine ⟨9244358610973648233639899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98606491850385581158825589 9244358610973648233639899)
      ·
        refine ⟨13866537916460472350459849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9244358610973648233639899 13866537916460472350459849)
        ·
          refine ⟨10399903437345354262844887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13866537916460472350459849 10399903437345354262844887)
          ·
            refine ⟨15599855156018031394267331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10399903437345354262844887 15599855156018031394267331)
            ·
              refine ⟨23399782734027047091400997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15599855156018031394267331 23399782734027047091400997)
              ·
                refine ⟨4387459262630071329637687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23399782734027047091400997 4387459262630071329637687)
                ·
                  refine ⟨6581188893945106994456531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387459262630071329637687 6581188893945106994456531)
                  ·
                    refine ⟨9871783340917660491684797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6581188893945106994456531 9871783340917660491684797)
                    ·
                      refine ⟨3701918752844122684381799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9871783340917660491684797 3701918752844122684381799)
                      ·
                        rfl

theorem cell23_7209461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_7209461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209461 prefixEnd_7209461 := by exact prefixLift 7209461
  have htrace : WordTrace (prefixWord ++ tailWord_7209461) baseStart_7209461 baseEnd_7209461 := by
    simpa [prefixWord, tailWord_7209461, baseEnd_7209461] using wordTrace_append hprefix tailTrace_7209461
  have hstable : (prefixWord ++ tailWord_7209461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209461).length < 2 ^ (prefixWord ++ tailWord_7209461).sum := by decide
  have hdescent : baseEnd_7209461 < baseStart_7209461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209466 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_7209466 : Nat := 118140960795 + 7209466 * 2 ^ 59
def prefixEnd_7209466 : Nat := 4983230072969 + 3 ^ 40 * 7209466 * 2
def baseEnd_7209466 : Nat := 3701921320247395164819275

theorem tailTrace_7209466 : CollatzResearch.WordTrace tailWord_7209466 prefixEnd_7209466 3701921320247395164819275 := by
  unfold tailWord_7209466
  simp only [CollatzResearch.WordTrace]
  refine ⟨65737706824835858902700063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175300551532895623740533501 65737706824835858902700063)
  ·
    refine ⟨98606560237253788354050095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65737706824835858902700063 98606560237253788354050095)
    ·
      refine ⟨147909840355880682531075143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98606560237253788354050095 147909840355880682531075143)
      ·
        refine ⟨221864760533821023796612715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147909840355880682531075143 221864760533821023796612715)
        ·
          refine ⟨332797140800731535694919073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221864760533821023796612715 332797140800731535694919073)
          ·
            refine ⟨249597855600548651771189305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332797140800731535694919073 249597855600548651771189305)
            ·
              refine ⟨187198391700411488828391979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249597855600548651771189305 187198391700411488828391979)
              ·
                refine ⟨280797587550617233242587969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187198391700411488828391979 280797587550617233242587969)
                ·
                  refine ⟨210598190662962924931940977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 280797587550617233242587969 210598190662962924931940977)
                  ·
                    refine ⟨157948642997222193698955733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 210598190662962924931940977 157948642997222193698955733)
                    ·
                      refine ⟨3701921320247395164819275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157948642997222193698955733 3701921320247395164819275)
                      ·
                        rfl

theorem cell23_7209466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_7209466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209466 prefixEnd_7209466 := by exact prefixLift 7209466
  have htrace : WordTrace (prefixWord ++ tailWord_7209466) baseStart_7209466 baseEnd_7209466 := by
    simpa [prefixWord, tailWord_7209466, baseEnd_7209466] using wordTrace_append hprefix tailTrace_7209466
  have hstable : (prefixWord ++ tailWord_7209466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209466).length < 2 ^ (prefixWord ++ tailWord_7209466).sum := by decide
  have hdescent : baseEnd_7209466 < baseStart_7209466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209473 : List Nat := [1, 2, 4, 1, 3, 1, 3, 8]
def baseStart_7209473 : Nat := 118140960795 + 7209473 * 2 ^ 59
def prefixEnd_7209473 : Nat := 4983230072969 + 3 ^ 40 * 7209473 * 2
def baseEnd_7209473 : Nat := 137108330170813949534509

theorem tailTrace_7209473 : CollatzResearch.WordTrace tailWord_7209473 prefixEnd_7209473 137108330170813949534509 := by
  unfold tailWord_7209473
  simp only [CollatzResearch.WordTrace]
  refine ⟨262951082610318075806305073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175300721740212050537536715 262951082610318075806305073)
  ·
    refine ⟨197213311957738556854728805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262951082610318075806305073 197213311957738556854728805)
    ·
      refine ⟨36977495992075979410261651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197213311957738556854728805 36977495992075979410261651)
      ·
        refine ⟨55466243988113969115392477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36977495992075979410261651 55466243988113969115392477)
        ·
          refine ⟨20799841495542738418272179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55466243988113969115392477 20799841495542738418272179)
          ·
            refine ⟨31199762243314107627408269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20799841495542738418272179 31199762243314107627408269)
            ·
              refine ⟨11699910841242790360278101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31199762243314107627408269 11699910841242790360278101)
              ·
                refine ⟨137108330170813949534509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11699910841242790360278101 137108330170813949534509)
                ·
                  rfl

theorem cell23_7209473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 8].length) (baseStart_7209473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209473 prefixEnd_7209473 := by exact prefixLift 7209473
  have htrace : WordTrace (prefixWord ++ tailWord_7209473) baseStart_7209473 baseEnd_7209473 := by
    simpa [prefixWord, tailWord_7209473, baseEnd_7209473] using wordTrace_append hprefix tailTrace_7209473
  have hstable : (prefixWord ++ tailWord_7209473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209473).length < 2 ^ (prefixWord ++ tailWord_7209473).sum := by decide
  have hdescent : baseEnd_7209473 < baseStart_7209473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209500 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_7209500 : Nat := 118140960795 + 7209500 * 2 ^ 59
def prefixEnd_7209500 : Nat := 4983230072969 + 3 ^ 40 * 7209500 * 2
def baseEnd_7209500 : Nat := 3701938778589648031794119

theorem tailTrace_7209500 : CollatzResearch.WordTrace tailWord_7209500 prefixEnd_7209500 3701938778589648031794119 := by
  unfold tailWord_7209500
  simp only [CollatzResearch.WordTrace]
  refine ⟨131476033690610129708768977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175301378254146839611691969 131476033690610129708768977)
  ·
    refine ⟨98607025267957597281576733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131476033690610129708768977 98607025267957597281576733)
    ·
      refine ⟨36977634475484098980591275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98607025267957597281576733 36977634475484098980591275)
      ·
        refine ⟨55466451713226148470886913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36977634475484098980591275 55466451713226148470886913)
        ·
          refine ⟨41599838784919611353165185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55466451713226148470886913 41599838784919611353165185)
          ·
            refine ⟨31199879088689708514873889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41599838784919611353165185 31199879088689708514873889)
            ·
              refine ⟨23399909316517281386155417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31199879088689708514873889 23399909316517281386155417)
              ·
                refine ⟨17549931987387961039616563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23399909316517281386155417 17549931987387961039616563)
                ·
                  refine ⟨26324897981081941559424845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17549931987387961039616563 26324897981081941559424845)
                  ·
                    refine ⟨9871836742905728084784317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26324897981081941559424845 9871836742905728084784317)
                    ·
                      refine ⟨3701938778589648031794119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9871836742905728084784317 3701938778589648031794119)
                      ·
                        rfl

theorem cell23_7209500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_7209500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209500 prefixEnd_7209500 := by exact prefixLift 7209500
  have htrace : WordTrace (prefixWord ++ tailWord_7209500) baseStart_7209500 baseEnd_7209500 := by
    simpa [prefixWord, tailWord_7209500, baseEnd_7209500] using wordTrace_append hprefix tailTrace_7209500
  have hstable : (prefixWord ++ tailWord_7209500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209500).length < 2 ^ (prefixWord ++ tailWord_7209500).sum := by decide
  have hdescent : baseEnd_7209500 < baseStart_7209500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209501 : List Nat := [1, 4, 2, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_7209501 : Nat := 118140960795 + 7209501 * 2 ^ 59
def prefixEnd_7209501 : Nat := 4983230072969 + 3 ^ 40 * 7209501 * 2
def baseEnd_7209501 : Nat := 3701939292070302527881615

theorem tailTrace_7209501 : CollatzResearch.WordTrace tailWord_7209501 prefixEnd_7209501 3701939292070302527881615 := by
  unfold tailWord_7209501
  simp only [CollatzResearch.WordTrace]
  refine ⟨262952103854216636588324357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175301402569477757725549571 262952103854216636588324357)
  ·
    refine ⟨49303519472665619360310817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262952103854216636588324357 49303519472665619360310817)
    ·
      refine ⟨36977639604499214520233113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49303519472665619360310817 36977639604499214520233113)
      ·
        refine ⟨27733229703374410890174835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36977639604499214520233113 27733229703374410890174835)
        ·
          refine ⟨41599844555061616335262253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27733229703374410890174835 41599844555061616335262253)
          ·
            refine ⟨15599941708148106125723345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41599844555061616335262253 15599941708148106125723345)
            ·
              refine ⟨11699956281111079594292509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15599941708148106125723345 11699956281111079594292509)
              ·
                refine ⟨4387483605416654847859691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11699956281111079594292509 4387483605416654847859691)
                ·
                  refine ⟨6581225408124982271789537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387483605416654847859691 6581225408124982271789537)
                  ·
                    refine ⟨4935919056093736703842153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6581225408124982271789537 4935919056093736703842153)
                    ·
                      refine ⟨3701939292070302527881615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4935919056093736703842153 3701939292070302527881615)
                      ·
                        rfl

theorem cell23_7209501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_7209501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209501 prefixEnd_7209501 := by exact prefixLift 7209501
  have htrace : WordTrace (prefixWord ++ tailWord_7209501) baseStart_7209501 baseEnd_7209501 := by
    simpa [prefixWord, tailWord_7209501, baseEnd_7209501] using wordTrace_append hprefix tailTrace_7209501
  have hstable : (prefixWord ++ tailWord_7209501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209501).length < 2 ^ (prefixWord ++ tailWord_7209501).sum := by decide
  have hdescent : baseEnd_7209501 < baseStart_7209501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209511 : List Nat := [1, 1, 7, 2, 1, 2, 1, 2, 2, 4]
def baseStart_7209511 : Nat := 118140960795 + 7209511 * 2 ^ 59
def prefixEnd_7209511 : Nat := 4983230072969 + 3 ^ 40 * 7209511 * 2
def baseEnd_7209511 : Nat := 1233981475625615829585523

theorem tailTrace_7209511 : CollatzResearch.WordTrace tailWord_7209511 prefixEnd_7209511 1233981475625615829585523 := by
  unfold tailWord_7209511
  simp only [CollatzResearch.WordTrace]
  refine ⟨262952468584180408296188387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175301645722786938864125591 262952468584180408296188387)
  ·
    refine ⟨394428702876270612444282581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262952468584180408296188387 394428702876270612444282581)
    ·
      refine ⟨9244422723662592479162873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 394428702876270612444282581 9244422723662592479162873)
      ·
        refine ⟨6933317042746944359372155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9244422723662592479162873 6933317042746944359372155)
        ·
          refine ⟨10399975564120416539058233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6933317042746944359372155 10399975564120416539058233)
          ·
            refine ⟨7799981673090312404293675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10399975564120416539058233 7799981673090312404293675)
            ·
              refine ⟨11699972509635468606440513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7799981673090312404293675 11699972509635468606440513)
              ·
                refine ⟨8774979382226601454830385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11699972509635468606440513 8774979382226601454830385)
                ·
                  refine ⟨6581234536669951091122789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8774979382226601454830385 6581234536669951091122789)
                  ·
                    refine ⟨1233981475625615829585523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6581234536669951091122789 1233981475625615829585523)
                    ·
                      rfl

theorem cell23_7209511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_7209511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209511 prefixEnd_7209511 := by exact prefixLift 7209511
  have htrace : WordTrace (prefixWord ++ tailWord_7209511) baseStart_7209511 baseEnd_7209511 := by
    simpa [prefixWord, tailWord_7209511, baseEnd_7209511] using wordTrace_append hprefix tailTrace_7209511
  have hstable : (prefixWord ++ tailWord_7209511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209511).length < 2 ^ (prefixWord ++ tailWord_7209511).sum := by decide
  have hdescent : baseEnd_7209511 < baseStart_7209511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209557 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 4, 2, 2]
def baseStart_7209557 : Nat := 118140960795 + 7209557 * 2 ^ 59
def prefixEnd_7209557 : Nat := 4983230072969 + 3 ^ 40 * 7209557 * 2
def baseEnd_7209557 : Nat := 3701968046986954308781357

theorem tailTrace_7209557 : CollatzResearch.WordTrace tailWord_7209557 prefixEnd_7209557 3701968046986954308781357 := by
  unfold tailWord_7209557
  simp only [CollatzResearch.WordTrace]
  refine ⟨262954146342013758152362925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175302764228009172101575283 262954146342013758152362925)
  ·
    refine ⟨98607804878255159307136097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262954146342013758152362925 98607804878255159307136097)
    ·
      refine ⟨73955853658691369480352073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98607804878255159307136097 73955853658691369480352073)
      ·
        refine ⟨55466890244018527110264055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73955853658691369480352073 55466890244018527110264055)
        ·
          refine ⟨83200335366027790665396083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55466890244018527110264055 83200335366027790665396083)
          ·
            refine ⟨124800503049041685998094125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83200335366027790665396083 124800503049041685998094125)
            ·
              refine ⟨46800188643390632249285297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124800503049041685998094125 46800188643390632249285297)
              ·
                refine ⟨35100141482542974186963973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46800188643390632249285297 35100141482542974186963973)
                ·
                  refine ⟨6581276527976807660055745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35100141482542974186963973 6581276527976807660055745)
                  ·
                    refine ⟨4935957395982605745041809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6581276527976807660055745 4935957395982605745041809)
                    ·
                      refine ⟨3701968046986954308781357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4935957395982605745041809 3701968046986954308781357)
                      ·
                        rfl

theorem cell23_7209557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_7209557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209557 prefixEnd_7209557 := by exact prefixLift 7209557
  have htrace : WordTrace (prefixWord ++ tailWord_7209557) baseStart_7209557 baseEnd_7209557 := by
    simpa [prefixWord, tailWord_7209557, baseEnd_7209557] using wordTrace_append hprefix tailTrace_7209557
  have hstable : (prefixWord ++ tailWord_7209557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209557).length < 2 ^ (prefixWord ++ tailWord_7209557).sum := by decide
  have hdescent : baseEnd_7209557 < baseStart_7209557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209580 : List Nat := [2, 2, 1, 1, 3, 1, 2, 6, 5]
def baseStart_7209580 : Nat := 118140960795 + 7209580 * 2 ^ 59
def prefixEnd_7209580 : Nat := 4983230072969 + 3 ^ 40 * 7209580 * 2
def baseEnd_7209580 : Nat := 411331095226889746532639

theorem tailTrace_7209580 : CollatzResearch.WordTrace tailWord_7209580 prefixEnd_7209580 411331095226889746532639 := by
  unfold tailWord_7209580
  simp only [CollatzResearch.WordTrace]
  refine ⟨131477492610465216540225097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175303323480620288720300129 131477492610465216540225097)
  ·
    refine ⟨98608119457848912405168823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131477492610465216540225097 98608119457848912405168823)
    ·
      refine ⟨147912179186773368607753235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98608119457848912405168823 147912179186773368607753235)
      ·
        refine ⟨221868268780160052911629853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147912179186773368607753235 221868268780160052911629853)
        ·
          refine ⟨83200600792560019841861195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221868268780160052911629853 83200600792560019841861195)
          ·
            refine ⟨124800901188840029762791793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83200600792560019841861195 124800901188840029762791793)
            ·
              refine ⟨93600675891630022322093845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124800901188840029762791793 93600675891630022322093845)
              ·
                refine ⟨4387531682420157296348149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93600675891630022322093845 4387531682420157296348149)
                ·
                  refine ⟨411331095226889746532639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4387531682420157296348149 411331095226889746532639)
                  ·
                    rfl

theorem cell23_7209580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 5].length) (baseStart_7209580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209580 prefixEnd_7209580 := by exact prefixLift 7209580
  have htrace : WordTrace (prefixWord ++ tailWord_7209580) baseStart_7209580 baseEnd_7209580 := by
    simpa [prefixWord, tailWord_7209580, baseEnd_7209580] using wordTrace_append hprefix tailTrace_7209580
  have hstable : (prefixWord ++ tailWord_7209580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209580).length < 2 ^ (prefixWord ++ tailWord_7209580).sum := by decide
  have hdescent : baseEnd_7209580 < baseStart_7209580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209647 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 2, 4, 2]
def baseStart_7209647 : Nat := 118140960795 + 7209647 * 2 ^ 59
def prefixEnd_7209647 : Nat := 4983230072969 + 3 ^ 40 * 7209647 * 2
def baseEnd_7209647 : Nat := 3702014260245858956655943

theorem tailTrace_7209647 : CollatzResearch.WordTrace tailWord_7209647 prefixEnd_7209647 3702014260245858956655943 := by
  unfold tailWord_7209647
  simp only [CollatzResearch.WordTrace]
  refine ⟨262957428911687703523139195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175304952607791802348759463 262957428911687703523139195)
  ·
    refine ⟨394436143367531555284708793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262957428911687703523139195 394436143367531555284708793)
    ·
      refine ⟨295827107525648666463531595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394436143367531555284708793 295827107525648666463531595)
      ·
        refine ⟨443740661288472999695297393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295827107525648666463531595 443740661288472999695297393)
        ·
          refine ⟨332805495966354749771473045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443740661288472999695297393 332805495966354749771473045)
          ·
            refine ⟨15600257623422878895537799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 332805495966354749771473045 15600257623422878895537799)
            ·
              refine ⟨23400386435134318343306699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15600257623422878895537799 23400386435134318343306699)
              ·
                refine ⟨35100579652701477514960049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23400386435134318343306699 35100579652701477514960049)
                ·
                  refine ⟨26325434739526108136220037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35100579652701477514960049 26325434739526108136220037)
                  ·
                    refine ⟨4936019013661145275541257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26325434739526108136220037 4936019013661145275541257)
                    ·
                      refine ⟨3702014260245858956655943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936019013661145275541257 3702014260245858956655943)
                      ·
                        rfl

theorem cell23_7209647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 4, 2].length) (baseStart_7209647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209647 prefixEnd_7209647 := by exact prefixLift 7209647
  have htrace : WordTrace (prefixWord ++ tailWord_7209647) baseStart_7209647 baseEnd_7209647 := by
    simpa [prefixWord, tailWord_7209647, baseEnd_7209647] using wordTrace_append hprefix tailTrace_7209647
  have hstable : (prefixWord ++ tailWord_7209647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209647).length < 2 ^ (prefixWord ++ tailWord_7209647).sum := by decide
  have hdescent : baseEnd_7209647 < baseStart_7209647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209650 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_7209650 : Nat := 118140960795 + 7209650 * 2 ^ 59
def prefixEnd_7209650 : Nat := 4983230072969 + 3 ^ 40 * 7209650 * 2
def baseEnd_7209650 : Nat := 3702015800687822444918429

theorem tailTrace_7209650 : CollatzResearch.WordTrace tailWord_7209650 prefixEnd_7209650 3702015800687822444918429 := by
  unfold tailWord_7209650
  simp only [CollatzResearch.WordTrace]
  refine ⟨65739384582669208758874601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175305025553784556690332269 65739384582669208758874601)
  ·
    refine ⟨49304538437001906569155951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65739384582669208758874601 49304538437001906569155951)
    ·
      refine ⟨73956807655502859853733927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49304538437001906569155951 73956807655502859853733927)
      ·
        refine ⟨110935211483254289780600891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73956807655502859853733927 110935211483254289780600891)
        ·
          refine ⟨166402817224881434670901337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110935211483254289780600891 166402817224881434670901337)
          ·
            refine ⟨124802112918661076003176003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166402817224881434670901337 124802112918661076003176003)
            ·
              refine ⟨187203169377991614004764005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124802112918661076003176003 187203169377991614004764005)
              ·
                refine ⟨35100594258373427625893251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187203169377991614004764005 35100594258373427625893251)
                ·
                  refine ⟨52650891387560141438839877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35100594258373427625893251 52650891387560141438839877)
                  ·
                    refine ⟨9872042135167526519782477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52650891387560141438839877 9872042135167526519782477)
                    ·
                      refine ⟨3702015800687822444918429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9872042135167526519782477 3702015800687822444918429)
                      ·
                        rfl

theorem cell23_7209650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_7209650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209650 prefixEnd_7209650 := by exact prefixLift 7209650
  have htrace : WordTrace (prefixWord ++ tailWord_7209650) baseStart_7209650 baseEnd_7209650 := by
    simpa [prefixWord, tailWord_7209650, baseEnd_7209650] using wordTrace_append hprefix tailTrace_7209650
  have hstable : (prefixWord ++ tailWord_7209650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209650).length < 2 ^ (prefixWord ++ tailWord_7209650).sum := by decide
  have hdescent : baseEnd_7209650 < baseStart_7209650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209673 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 6]
def baseStart_7209673 : Nat := 118140960795 + 7209673 * 2 ^ 59
def prefixEnd_7209673 : Nat := 4983230072969 + 3 ^ 40 * 7209673 * 2
def baseEnd_7209673 : Nat := 3702027610742875854930823

theorem tailTrace_7209673 : CollatzResearch.WordTrace tailWord_7209673 prefixEnd_7209673 3702027610742875854930823 := by
  unfold tailWord_7209673
  simp only [CollatzResearch.WordTrace]
  refine ⟨262958377209593509963585673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175305584806395673309057115 262958377209593509963585673)
  ·
    refine ⟨197218782907195132472689255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262958377209593509963585673 197218782907195132472689255)
    ·
      refine ⟨295828174360792698709033883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197218782907195132472689255 295828174360792698709033883)
      ·
        refine ⟨443742261541189048063550825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295828174360792698709033883 443742261541189048063550825)
        ·
          refine ⟨332806696155891786047663119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443742261541189048063550825 332806696155891786047663119)
          ·
            refine ⟨499210044233837679071494679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332806696155891786047663119 499210044233837679071494679)
            ·
              refine ⟨748815066350756518607242019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499210044233837679071494679 748815066350756518607242019)
              ·
                refine ⟨1123222599526134777910863029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748815066350756518607242019 1123222599526134777910863029)
                ·
                  refine ⟨105302118705575135429143409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1123222599526134777910863029 105302118705575135429143409)
                  ·
                    refine ⟨78976589029181351571857557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105302118705575135429143409 78976589029181351571857557)
                    ·
                      refine ⟨3702027610742875854930823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78976589029181351571857557 3702027610742875854930823)
                      ·
                        rfl

theorem cell23_7209673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_7209673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209673 prefixEnd_7209673 := by exact prefixLift 7209673
  have htrace : WordTrace (prefixWord ++ tailWord_7209673) baseStart_7209673 baseEnd_7209673 := by
    simpa [prefixWord, tailWord_7209673, baseEnd_7209673] using wordTrace_append hprefix tailTrace_7209673
  have hstable : (prefixWord ++ tailWord_7209673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209673).length < 2 ^ (prefixWord ++ tailWord_7209673).sum := by decide
  have hdescent : baseEnd_7209673 < baseStart_7209673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209674 : List Nat := [3, 1, 2, 1, 4, 1, 1, 5, 1, 4]
def baseStart_7209674 : Nat := 118140960795 + 7209674 * 2 ^ 59
def prefixEnd_7209674 : Nat := 4983230072969 + 3 ^ 40 * 7209674 * 2
def baseEnd_7209674 : Nat := 1234009374741176783672773

theorem tailTrace_7209674 : CollatzResearch.WordTrace tailWord_7209674 prefixEnd_7209674 1234009374741176783672773 := by
  unfold tailWord_7209674
  simp only [CollatzResearch.WordTrace]
  refine ⟨65739603420647471783593019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175305609121726591422914717 65739603420647471783593019)
  ·
    refine ⟨98609405130971207675389529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65739603420647471783593019 98609405130971207675389529)
    ·
      refine ⟨73957053848228405756542147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98609405130971207675389529 73957053848228405756542147)
      ·
        refine ⟨110935580772342608634813221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73957053848228405756542147 110935580772342608634813221)
        ·
          refine ⟨20800421394814239119027479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110935580772342608634813221 20800421394814239119027479)
          ·
            refine ⟨31200632092221358678541219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20800421394814239119027479 31200632092221358678541219)
            ·
              refine ⟨46800948138332038017811829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31200632092221358678541219 46800948138332038017811829)
              ·
                refine ⟨4387588887968628564169859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46800948138332038017811829 4387588887968628564169859)
                ·
                  refine ⟨6581383331952942846254789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387588887968628564169859 6581383331952942846254789)
                  ·
                    refine ⟨1234009374741176783672773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6581383331952942846254789 1234009374741176783672773)
                    ·
                      rfl

theorem cell23_7209674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_7209674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209674 prefixEnd_7209674 := by exact prefixLift 7209674
  have htrace : WordTrace (prefixWord ++ tailWord_7209674) baseStart_7209674 baseEnd_7209674 := by
    simpa [prefixWord, tailWord_7209674, baseEnd_7209674] using wordTrace_append hprefix tailTrace_7209674
  have hstable : (prefixWord ++ tailWord_7209674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209674).length < 2 ^ (prefixWord ++ tailWord_7209674).sum := by decide
  have hdescent : baseEnd_7209674 < baseStart_7209674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209687 : List Nat := [1, 1, 3, 2, 1, 6, 1, 2, 6]
def baseStart_7209687 : Nat := 118140960795 + 7209687 * 2 ^ 59
def prefixEnd_7209687 : Nat := 4983230072969 + 3 ^ 40 * 7209687 * 2
def baseEnd_7209687 : Nat := 411337199941337644461751

theorem tailTrace_7209687 : CollatzResearch.WordTrace tailWord_7209687 prefixEnd_7209687 411337199941337644461751 := by
  unfold tailWord_7209687
  simp only [CollatzResearch.WordTrace]
  refine ⟨262958887831542790354595315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175305925221028526903063543 262958887831542790354595315)
  ·
    refine ⟨394438331747314185531892973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262958887831542790354595315 394438331747314185531892973)
    ·
      refine ⟨147914374405242819574459865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394438331747314185531892973 147914374405242819574459865)
      ·
        refine ⟨110935780803932114680844899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147914374405242819574459865 110935780803932114680844899)
        ·
          refine ⟨166403671205898172021267349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110935780803932114680844899 166403671205898172021267349)
          ·
            refine ⟨7800172087776476813496907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166403671205898172021267349 7800172087776476813496907)
            ·
              refine ⟨11700258131664715220245361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7800172087776476813496907 11700258131664715220245361)
              ·
                refine ⟨8775193598748536415184021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11700258131664715220245361 8775193598748536415184021)
                ·
                  refine ⟨411337199941337644461751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8775193598748536415184021 411337199941337644461751)
                  ·
                    rfl

theorem cell23_7209687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 6].length) (baseStart_7209687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209687 prefixEnd_7209687 := by exact prefixLift 7209687
  have htrace : WordTrace (prefixWord ++ tailWord_7209687) baseStart_7209687 baseEnd_7209687 := by
    simpa [prefixWord, tailWord_7209687, baseEnd_7209687] using wordTrace_append hprefix tailTrace_7209687
  have hstable : (prefixWord ++ tailWord_7209687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209687).length < 2 ^ (prefixWord ++ tailWord_7209687).sum := by decide
  have hdescent : baseEnd_7209687 < baseStart_7209687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209704 : List Nat := [2, 1, 4, 1, 4, 1, 3, 1, 6]
def baseStart_7209704 : Nat := 118140960795 + 7209704 * 2 ^ 59
def prefixEnd_7209704 : Nat := 4983230072969 + 3 ^ 40 * 7209704 * 2
def baseEnd_7209704 : Nat := 411338169849240581515909

theorem tailTrace_7209704 : CollatzResearch.WordTrace tailWord_7209704 prefixEnd_7209704 411338169849240581515909 := by
  unfold tailWord_7209704
  simp only [CollatzResearch.WordTrace]
  refine ⟨131479753936240601128982083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175306338581654134838642777 131479753936240601128982083)
  ·
    refine ⟨197219630904360901693473125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131479753936240601128982083 197219630904360901693473125)
    ·
      refine ⟨36978680794567669067526211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197219630904360901693473125 36978680794567669067526211)
      ·
        refine ⟨55468021191851503601289317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36978680794567669067526211 55468021191851503601289317)
        ·
          refine ⟨10400253973472156925241747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55468021191851503601289317 10400253973472156925241747)
          ·
            refine ⟨15600380960208235387862621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10400253973472156925241747 15600380960208235387862621)
            ·
              refine ⟨5850142860078088270448483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15600380960208235387862621 5850142860078088270448483)
              ·
                refine ⟨8775214290117132405672725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5850142860078088270448483 8775214290117132405672725)
                ·
                  refine ⟨411338169849240581515909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8775214290117132405672725 411338169849240581515909)
                  ·
                    rfl

theorem cell23_7209704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 6].length) (baseStart_7209704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209704 prefixEnd_7209704 := by exact prefixLift 7209704
  have htrace : WordTrace (prefixWord ++ tailWord_7209704) baseStart_7209704 baseEnd_7209704 := by
    simpa [prefixWord, tailWord_7209704, baseEnd_7209704] using wordTrace_append hprefix tailTrace_7209704
  have hstable : (prefixWord ++ tailWord_7209704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209704).length < 2 ^ (prefixWord ++ tailWord_7209704).sum := by decide
  have hdescent : baseEnd_7209704 < baseStart_7209704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209714 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_7209714 : Nat := 118140960795 + 7209714 * 2 ^ 59
def prefixEnd_7209714 : Nat := 4983230072969 + 3 ^ 40 * 7209714 * 2
def baseEnd_7209714 : Nat := 3702048663449710194518135

theorem tailTrace_7209714 : CollatzResearch.WordTrace tailWord_7209714 prefixEnd_7209714 3702048663449710194518135 := by
  unfold tailWord_7209714
  simp only [CollatzResearch.WordTrace]
  refine ⟨65739968150611243491457049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175306581734963315977218797 65739968150611243491457049)
  ·
    refine ⟨49304976112958432618592787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65739968150611243491457049 49304976112958432618592787)
    ·
      refine ⟨73957464169437648927889181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49304976112958432618592787 73957464169437648927889181)
      ·
        refine ⟨27734049063539118347958443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73957464169437648927889181 27734049063539118347958443)
        ·
          refine ⟨41601073595308677521937665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27734049063539118347958443 41601073595308677521937665)
          ·
            refine ⟨31200805196481508141453249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41601073595308677521937665 31200805196481508141453249)
            ·
              refine ⟨23400603897361131106089937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31200805196481508141453249 23400603897361131106089937)
              ·
                refine ⟨17550452923020848329567453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23400603897361131106089937 17550452923020848329567453)
                ·
                  refine ⟨6581419846132818123587795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17550452923020848329567453 6581419846132818123587795)
                  ·
                    refine ⟨9872129769199227185381693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6581419846132818123587795 9872129769199227185381693)
                    ·
                      refine ⟨3702048663449710194518135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9872129769199227185381693 3702048663449710194518135)
                      ·
                        rfl

theorem cell23_7209714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_7209714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209714 prefixEnd_7209714 := by exact prefixLift 7209714
  have htrace : WordTrace (prefixWord ++ tailWord_7209714) baseStart_7209714 baseEnd_7209714 := by
    simpa [prefixWord, tailWord_7209714, baseEnd_7209714] using wordTrace_append hprefix tailTrace_7209714
  have hstable : (prefixWord ++ tailWord_7209714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209714).length < 2 ^ (prefixWord ++ tailWord_7209714).sum := by decide
  have hdescent : baseEnd_7209714 < baseStart_7209714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209737 : List Nat := [1, 2, 1, 1, 3, 2, 4, 3, 1, 1, 4]
def baseStart_7209737 : Nat := 118140960795 + 7209737 * 2 ^ 59
def prefixEnd_7209737 : Nat := 4983230072969 + 3 ^ 40 * 7209737 * 2
def baseEnd_7209737 : Nat := 3702060473504763604530529

theorem tailTrace_7209737 : CollatzResearch.WordTrace tailWord_7209737 prefixEnd_7209737 3702060473504763604530529 := by
  unfold tailWord_7209737
  simp only [CollatzResearch.WordTrace]
  refine ⟨262960711481361648893915465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175307140987574432595943643 262960711481361648893915465)
  ·
    refine ⟨197220533611021236670436599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262960711481361648893915465 197220533611021236670436599)
    ·
      refine ⟨295830800416531855005654899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197220533611021236670436599 295830800416531855005654899)
      ·
        refine ⟨443746200624797782508482349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295830800416531855005654899 443746200624797782508482349)
        ·
          refine ⟨166404825234299168440680881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443746200624797782508482349 166404825234299168440680881)
          ·
            refine ⟨124803618925724376330510661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166404825234299168440680881 124803618925724376330510661)
            ·
              refine ⟨23400678548573320561970749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124803618925724376330510661 23400678548573320561970749)
              ·
                refine ⟨8775254455714995210739031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23400678548573320561970749 8775254455714995210739031)
                ·
                  refine ⟨13162881683572492816108547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8775254455714995210739031 13162881683572492816108547)
                  ·
                    refine ⟨19744322525358739224162821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13162881683572492816108547 19744322525358739224162821)
                    ·
                      refine ⟨3702060473504763604530529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19744322525358739224162821 3702060473504763604530529)
                      ·
                        rfl

theorem cell23_7209737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 1, 4].length) (baseStart_7209737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209737 prefixEnd_7209737 := by exact prefixLift 7209737
  have htrace : WordTrace (prefixWord ++ tailWord_7209737) baseStart_7209737 baseEnd_7209737 := by
    simpa [prefixWord, tailWord_7209737, baseEnd_7209737] using wordTrace_append hprefix tailTrace_7209737
  have hstable : (prefixWord ++ tailWord_7209737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209737).length < 2 ^ (prefixWord ++ tailWord_7209737).sum := by decide
  have hdescent : baseEnd_7209737 < baseStart_7209737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209747 : List Nat := [1, 1, 1, 2, 1, 3, 4, 4, 2, 4]
def baseStart_7209747 : Nat := 118140960795 + 7209747 * 2 ^ 59
def prefixEnd_7209747 : Nat := 4983230072969 + 3 ^ 40 * 7209747 * 2
def baseEnd_7209747 : Nat := 1234021869437102855135161

theorem tailTrace_7209747 : CollatzResearch.WordTrace tailWord_7209747 prefixEnd_7209747 1234021869437102855135161 := by
  unfold tailWord_7209747
  simp only [CollatzResearch.WordTrace]
  refine ⟨262961076211325420601779495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175307384140883613734519663 262961076211325420601779495)
  ·
    refine ⟨394441614316988130902669243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262961076211325420601779495 394441614316988130902669243)
    ·
      refine ⟨591662421475482196354003865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394441614316988130902669243 591662421475482196354003865)
      ·
        refine ⟨443746816106611647265502899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591662421475482196354003865 443746816106611647265502899)
        ·
          refine ⟨665620224159917470898254349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443746816106611647265502899 665620224159917470898254349)
          ·
            refine ⟨249607584059969051586845381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 665620224159917470898254349 249607584059969051586845381)
            ·
              refine ⟨46801422011244197172533509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249607584059969051586845381 46801422011244197172533509)
              ·
                refine ⟨8775266627108286969850033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46801422011244197172533509 8775266627108286969850033)
                ·
                  refine ⟨6581449970331215227387525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8775266627108286969850033 6581449970331215227387525)
                  ·
                    refine ⟨1234021869437102855135161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6581449970331215227387525 1234021869437102855135161)
                    ·
                      rfl

theorem cell23_7209747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 4].length) (baseStart_7209747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209747 prefixEnd_7209747 := by exact prefixLift 7209747
  have htrace : WordTrace (prefixWord ++ tailWord_7209747) baseStart_7209747 baseEnd_7209747 := by
    simpa [prefixWord, tailWord_7209747, baseEnd_7209747] using wordTrace_append hprefix tailTrace_7209747
  have hstable : (prefixWord ++ tailWord_7209747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209747).length < 2 ^ (prefixWord ++ tailWord_7209747).sum := by decide
  have hdescent : baseEnd_7209747 < baseStart_7209747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209760 : List Nat := [2, 1, 1, 5, 1, 2, 1, 10]
def baseStart_7209760 : Nat := 118140960795 + 7209760 * 2 ^ 59
def prefixEnd_7209760 : Nat := 4983230072969 + 3 ^ 40 * 7209760 * 2
def baseEnd_7209760 : Nat := 137113788279993222760849

theorem tailTrace_7209760 : CollatzResearch.WordTrace tailWord_7209760 prefixEnd_7209760 137113788279993222760849 := by
  unfold tailWord_7209760
  simp only [CollatzResearch.WordTrace]
  refine ⟨131480775180139161911001367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175307700240185549214668489 131480775180139161911001367)
  ·
    refine ⟨197221162770208742866502051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131480775180139161911001367 197221162770208742866502051)
    ·
      refine ⟨295831744155313114299753077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197221162770208742866502051 295831744155313114299753077)
      ·
        refine ⟨27734226014560604465601851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 295831744155313114299753077 27734226014560604465601851)
        ·
          refine ⟨41601339021840906698402777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27734226014560604465601851 41601339021840906698402777)
          ·
            refine ⟨31201004266380680023802083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41601339021840906698402777 31201004266380680023802083)
            ·
              refine ⟨46801506399571020035703125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31201004266380680023802083 46801506399571020035703125)
              ·
                refine ⟨137113788279993222760849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46801506399571020035703125 137113788279993222760849)
                ·
                  rfl

theorem cell23_7209760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 10].length) (baseStart_7209760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209760 prefixEnd_7209760 := by exact prefixLift 7209760
  have htrace : WordTrace (prefixWord ++ tailWord_7209760) baseStart_7209760 baseEnd_7209760 := by
    simpa [prefixWord, tailWord_7209760, baseEnd_7209760] using wordTrace_append hprefix tailTrace_7209760
  have hstable : (prefixWord ++ tailWord_7209760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209760).length < 2 ^ (prefixWord ++ tailWord_7209760).sum := by decide
  have hdescent : baseEnd_7209760 < baseStart_7209760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209791 : List Nat := [1, 1, 2, 2, 5, 2, 3, 1, 1, 2, 3]
def baseStart_7209791 : Nat := 118140960795 + 7209791 * 2 ^ 59
def prefixEnd_7209791 : Nat := 4983230072969 + 3 ^ 40 * 7209791 * 2
def baseEnd_7209791 : Nat := 3702088201460106393255281

theorem tailTrace_7209791 : CollatzResearch.WordTrace tailWord_7209791 prefixEnd_7209791 3702088201460106393255281 := by
  unfold tailWord_7209791
  simp only [CollatzResearch.WordTrace]
  refine ⟨262962681023166016116381227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175308454015444010744254151 262962681023166016116381227)
  ·
    refine ⟨394444021534749024174571841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262962681023166016116381227 394444021534749024174571841)
    ·
      refine ⟨295833016151061768130928881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394444021534749024174571841 295833016151061768130928881)
      ·
        refine ⟨221874762113296326098196661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295833016151061768130928881 221874762113296326098196661)
        ·
          refine ⟨20800758948121530571705937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221874762113296326098196661 20800758948121530571705937)
          ·
            refine ⟨15600569211091147928779453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20800758948121530571705937 15600569211091147928779453)
            ·
              refine ⟨5850213454159180473292295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15600569211091147928779453 5850213454159180473292295)
              ·
                refine ⟨8775320181238770709938443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5850213454159180473292295 8775320181238770709938443)
                ·
                  refine ⟨13162980271858156064907665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8775320181238770709938443 13162980271858156064907665)
                  ·
                    refine ⟨9872235203893617048680749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13162980271858156064907665 9872235203893617048680749)
                    ·
                      refine ⟨3702088201460106393255281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9872235203893617048680749 3702088201460106393255281)
                      ·
                        rfl

theorem cell23_7209791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 1, 2, 3].length) (baseStart_7209791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209791 prefixEnd_7209791 := by exact prefixLift 7209791
  have htrace : WordTrace (prefixWord ++ tailWord_7209791) baseStart_7209791 baseEnd_7209791 := by
    simpa [prefixWord, tailWord_7209791, baseEnd_7209791] using wordTrace_append hprefix tailTrace_7209791
  have hstable : (prefixWord ++ tailWord_7209791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209791).length < 2 ^ (prefixWord ++ tailWord_7209791).sum := by decide
  have hdescent : baseEnd_7209791 < baseStart_7209791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209850 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 11]
def baseStart_7209850 : Nat := 118140960795 + 7209850 * 2 ^ 59
def prefixEnd_7209850 : Nat := 4983230072969 + 3 ^ 40 * 7209850 * 2
def baseEnd_7209850 : Nat := 411346499646524629157501

theorem tailTrace_7209850 : CollatzResearch.WordTrace tailWord_7209850 prefixEnd_7209850 411346499646524629157501 := by
  unfold tailWord_7209850
  simp only [CollatzResearch.WordTrace]
  refine ⟨65741208232488067298194751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175309888619968179461852669 65741208232488067298194751)
  ·
    refine ⟨98611812348732100947292127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65741208232488067298194751 98611812348732100947292127)
    ·
      refine ⟨147917718523098151420938191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98611812348732100947292127 147917718523098151420938191)
      ·
        refine ⟨221876577784647227131407287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147917718523098151420938191 221876577784647227131407287)
        ·
          refine ⟨332814866676970840697110931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221876577784647227131407287 332814866676970840697110931)
          ·
            refine ⟨499222300015456261045666397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332814866676970840697110931 499222300015456261045666397)
            ·
              refine ⟨187208362505796097892124899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499222300015456261045666397 187208362505796097892124899)
              ·
                refine ⟨280812543758694146838187349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187208362505796097892124899 280812543758694146838187349)
                ·
                  refine ⟨411346499646524629157501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 280812543758694146838187349 411346499646524629157501)
                  ·
                    rfl

theorem cell23_7209850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_7209850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209850 prefixEnd_7209850 := by exact prefixLift 7209850
  have htrace : WordTrace (prefixWord ++ tailWord_7209850) baseStart_7209850 baseEnd_7209850 := by
    simpa [prefixWord, tailWord_7209850, baseEnd_7209850] using wordTrace_append hprefix tailTrace_7209850
  have hstable : (prefixWord ++ tailWord_7209850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209850).length < 2 ^ (prefixWord ++ tailWord_7209850).sum := by decide
  have hdescent : baseEnd_7209850 < baseStart_7209850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209861 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 4, 2, 2]
def baseStart_7209861 : Nat := 118140960795 + 7209861 * 2 ^ 59
def prefixEnd_7209861 : Nat := 4983230072969 + 3 ^ 40 * 7209861 * 2
def baseEnd_7209861 : Nat := 3702124145105921119379959

theorem tailTrace_7209861 : CollatzResearch.WordTrace tailWord_7209861 prefixEnd_7209861 3702124145105921119379959 := by
  unfold tailWord_7209861
  simp only [CollatzResearch.WordTrace]
  refine ⟨262965234132912418071429437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175310156088608278714286291 262965234132912418071429437)
  ·
    refine ⟨98611962799842156776786039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262965234132912418071429437 98611962799842156776786039)
    ·
      refine ⟨147917944199763235165179059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98611962799842156776786039 147917944199763235165179059)
      ·
        refine ⟨221876916299644852747768589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147917944199763235165179059 221876916299644852747768589)
        ·
          refine ⟨83203843612366819780413221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221876916299644852747768589 83203843612366819780413221)
          ·
            refine ⟨15600720677318778708827479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83203843612366819780413221 15600720677318778708827479)
            ·
              refine ⟨23401081015978168063241219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15600720677318778708827479 23401081015978168063241219)
              ·
                refine ⟨35101621523967252094861829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23401081015978168063241219 35101621523967252094861829)
                ·
                  refine ⟨6581554035743859767786593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35101621523967252094861829 6581554035743859767786593)
                  ·
                    refine ⟨4936165526807894825839945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6581554035743859767786593 4936165526807894825839945)
                    ·
                      refine ⟨3702124145105921119379959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936165526807894825839945 3702124145105921119379959)
                      ·
                        rfl

theorem cell23_7209861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 2, 2].length) (baseStart_7209861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209861 prefixEnd_7209861 := by exact prefixLift 7209861
  have htrace : WordTrace (prefixWord ++ tailWord_7209861) baseStart_7209861 baseEnd_7209861 := by
    simpa [prefixWord, tailWord_7209861, baseEnd_7209861] using wordTrace_append hprefix tailTrace_7209861
  have hstable : (prefixWord ++ tailWord_7209861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209861).length < 2 ^ (prefixWord ++ tailWord_7209861).sum := by decide
  have hdescent : baseEnd_7209861 < baseStart_7209861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209897 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 2, 5]
def baseStart_7209897 : Nat := 118140960795 + 7209897 * 2 ^ 59
def prefixEnd_7209897 : Nat := 4983230072969 + 3 ^ 40 * 7209897 * 2
def baseEnd_7209897 : Nat := 1234047543469827659509931

theorem tailTrace_7209897 : CollatzResearch.WordTrace tailWord_7209897 prefixEnd_7209897 1234047543469827659509931 := by
  unfold tailWord_7209897
  simp only [CollatzResearch.WordTrace]
  refine ⟨262966547160781996219739945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175311031440521330813159963 262966547160781996219739945)
  ·
    refine ⟨197224910370586497164804959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262966547160781996219739945 197224910370586497164804959)
    ·
      refine ⟨295837365555879745747207439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197224910370586497164804959 295837365555879745747207439)
      ·
        refine ⟨443756048333819618620811159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295837365555879745747207439 443756048333819618620811159)
        ·
          refine ⟨665634072500729427931216739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443756048333819618620811159 665634072500729427931216739)
          ·
            refine ⟨998451108751094141896825109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665634072500729427931216739 998451108751094141896825109)
            ·
              refine ⟨46802395722707537901413677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 998451108751094141896825109 46802395722707537901413677)
              ·
                refine ⟨17550898396015326713030129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46802395722707537901413677 17550898396015326713030129)
                ·
                  refine ⟨13163173797011495034772597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17550898396015326713030129 13163173797011495034772597)
                  ·
                    refine ⟨1234047543469827659509931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13163173797011495034772597 1234047543469827659509931)
                    ·
                      rfl

theorem cell23_7209897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 5].length) (baseStart_7209897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209897 prefixEnd_7209897 := by exact prefixLift 7209897
  have htrace : WordTrace (prefixWord ++ tailWord_7209897) baseStart_7209897 baseEnd_7209897 := by
    simpa [prefixWord, tailWord_7209897, baseEnd_7209897] using wordTrace_append hprefix tailTrace_7209897
  have hstable : (prefixWord ++ tailWord_7209897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209897).length < 2 ^ (prefixWord ++ tailWord_7209897).sum := by decide
  have hdescent : baseEnd_7209897 < baseStart_7209897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209951 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 4]
def baseStart_7209951 : Nat := 118140960795 + 7209951 * 2 ^ 59
def prefixEnd_7209951 : Nat := 4983230072969 + 3 ^ 40 * 7209951 * 2
def baseEnd_7209951 : Nat := 3702170358364825767254545

theorem tailTrace_7209951 : CollatzResearch.WordTrace tailWord_7209951 prefixEnd_7209951 3702170358364825767254545 := by
  unfold tailWord_7209951
  simp only [CollatzResearch.WordTrace]
  refine ⟨262968516702586363442205707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175312344468390908961470471 262968516702586363442205707)
  ·
    refine ⟨394452775053879545163308561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262968516702586363442205707 394452775053879545163308561)
    ·
      refine ⟨295839581290409658872481421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394452775053879545163308561 295839581290409658872481421)
      ·
        refine ⟨110939842983903622077180533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295839581290409658872481421 110939842983903622077180533)
        ·
          refine ⟨10400610279740964569735675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110939842983903622077180533 10400610279740964569735675)
          ·
            refine ⟨15600915419611446854603513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10400610279740964569735675 15600915419611446854603513)
            ·
              refine ⟨11700686564708585140952635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15600915419611446854603513 11700686564708585140952635)
              ·
                refine ⟨17551029847062877711428953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11700686564708585140952635 17551029847062877711428953)
                ·
                  refine ⟨13163272385297158283571715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17551029847062877711428953 13163272385297158283571715)
                  ·
                    refine ⟨19744908577945737425357573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13163272385297158283571715 19744908577945737425357573)
                    ·
                      refine ⟨3702170358364825767254545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19744908577945737425357573 3702170358364825767254545)
                      ·
                        rfl

theorem cell23_7209951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_7209951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209951 prefixEnd_7209951 := by exact prefixLift 7209951
  have htrace : WordTrace (prefixWord ++ tailWord_7209951) baseStart_7209951 baseEnd_7209951 := by
    simpa [prefixWord, tailWord_7209951, baseEnd_7209951] using wordTrace_append hprefix tailTrace_7209951
  have hstable : (prefixWord ++ tailWord_7209951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209951).length < 2 ^ (prefixWord ++ tailWord_7209951).sum := by decide
  have hdescent : baseEnd_7209951 < baseStart_7209951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7209977 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 6]
def baseStart_7209977 : Nat := 118140960795 + 7209977 * 2 ^ 59
def prefixEnd_7209977 : Nat := 4983230072969 + 3 ^ 40 * 7209977 * 2
def baseEnd_7209977 : Nat := 3702183708861842665529425

theorem tailTrace_7209977 : CollatzResearch.WordTrace tailWord_7209977 prefixEnd_7209977 3702183708861842665529425 := by
  unfold tailWord_7209977
  simp only [CollatzResearch.WordTrace]
  refine ⟨262969465000492169882652185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175312976666994779921768123 262969465000492169882652185)
  ·
    refine ⟨197227098750369127411989139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262969465000492169882652185 197227098750369127411989139)
    ·
      refine ⟨295840648125553691117983709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197227098750369127411989139 295840648125553691117983709)
      ·
        refine ⟨110940243047082634169243891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295840648125553691117983709 110940243047082634169243891)
        ·
          refine ⟨166410364570623951253865837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110940243047082634169243891 166410364570623951253865837)
          ·
            refine ⟨62403886713983981720199689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166410364570623951253865837 62403886713983981720199689)
            ·
              refine ⟨46802915035487986290149767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62403886713983981720199689 46802915035487986290149767)
              ·
                refine ⟨70204372553231979435224651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46802915035487986290149767 70204372553231979435224651)
                ·
                  refine ⟨105306558829847969152836977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70204372553231979435224651 105306558829847969152836977)
                  ·
                    refine ⟨78979919122385976864627733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105306558829847969152836977 78979919122385976864627733)
                    ·
                      refine ⟨3702183708861842665529425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78979919122385976864627733 3702183708861842665529425)
                      ·
                        rfl

theorem cell23_7209977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_7209977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7209977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7209977 prefixEnd_7209977 := by exact prefixLift 7209977
  have htrace : WordTrace (prefixWord ++ tailWord_7209977) baseStart_7209977 baseEnd_7209977 := by
    simpa [prefixWord, tailWord_7209977, baseEnd_7209977] using wordTrace_append hprefix tailTrace_7209977
  have hstable : (prefixWord ++ tailWord_7209977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7209977).length < 2 ^ (prefixWord ++ tailWord_7209977).sum := by decide
  have hdescent : baseEnd_7209977 < baseStart_7209977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7209977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210002 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_7210002 : Nat := 118140960795 + 7210002 * 2 ^ 59
def prefixEnd_7210002 : Nat := 4983230072969 + 3 ^ 40 * 7210002 * 2
def baseEnd_7210002 : Nat := 3702196545878205067716811

theorem tailTrace_7210002 : CollatzResearch.WordTrace tailWord_7210002 prefixEnd_7210002 3702196545878205067716811 := by
  unfold tailWord_7210002
  simp only [CollatzResearch.WordTrace]
  refine ⟨65742594206350399788078065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175313584550267732768208173 65742594206350399788078065)
  ·
    refine ⟨49306945654762799841058549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65742594206350399788078065 49306945654762799841058549)
    ·
      refine ⟨4622526155134012485099239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49306945654762799841058549 4622526155134012485099239)
      ·
        refine ⟨6933789232701018727648859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4622526155134012485099239 6933789232701018727648859)
        ·
          refine ⟨10400683849051528091473289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6933789232701018727648859 10400683849051528091473289)
          ·
            refine ⟨7800512886788646068604967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10400683849051528091473289 7800512886788646068604967)
            ·
              refine ⟨11700769330182969102907451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7800512886788646068604967 11700769330182969102907451)
              ·
                refine ⟨17551153995274453654361177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11700769330182969102907451 17551153995274453654361177)
                ·
                  refine ⟨13163365496455840240770883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17551153995274453654361177 13163365496455840240770883)
                  ·
                    refine ⟨19745048244683760361156325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13163365496455840240770883 19745048244683760361156325)
                    ·
                      refine ⟨3702196545878205067716811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19745048244683760361156325 3702196545878205067716811)
                      ·
                        rfl

theorem cell23_7210002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_7210002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210002 prefixEnd_7210002 := by exact prefixLift 7210002
  have htrace : WordTrace (prefixWord ++ tailWord_7210002) baseStart_7210002 baseEnd_7210002 := by
    simpa [prefixWord, tailWord_7210002, baseEnd_7210002] using wordTrace_append hprefix tailTrace_7210002
  have hstable : (prefixWord ++ tailWord_7210002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210002).length < 2 ^ (prefixWord ++ tailWord_7210002).sum := by decide
  have hdescent : baseEnd_7210002 < baseStart_7210002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210044 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_7210044 : Nat := 118140960795 + 7210044 * 2 ^ 59
def prefixEnd_7210044 : Nat := 4983230072969 + 3 ^ 40 * 7210044 * 2
def baseEnd_7210044 : Nat := 3702218112065693903391617

theorem tailTrace_7210044 : CollatzResearch.WordTrace tailWord_7210044 prefixEnd_7210044 3702218112065693903391617 := by
  unfold tailWord_7210044
  simp only [CollatzResearch.WordTrace]
  refine ⟨131485954345624720162670593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175314605794166293550227457 131485954345624720162670593)
  ·
    refine ⟨98614465759218540122002945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131485954345624720162670593 98614465759218540122002945)
    ·
      refine ⟨73960849319413905091502209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98614465759218540122002945 73960849319413905091502209)
      ·
        refine ⟨55470636989560428818626657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73960849319413905091502209 55470636989560428818626657)
        ·
          refine ⟨41602977742170321613969993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55470636989560428818626657 41602977742170321613969993)
          ·
            refine ⟨31202233306627741210477495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41602977742170321613969993 31202233306627741210477495)
            ·
              refine ⟨46803349959941611815716243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31202233306627741210477495 46803349959941611815716243)
              ·
                refine ⟨70205024939912417723574365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46803349959941611815716243 70205024939912417723574365)
                ·
                  refine ⟨26326884352467156646340387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70205024939912417723574365 26326884352467156646340387)
                  ·
                    refine ⟨39490326528700734969510581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26326884352467156646340387 39490326528700734969510581)
                    ·
                      refine ⟨3702218112065693903391617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39490326528700734969510581 3702218112065693903391617)
                      ·
                        rfl

theorem cell23_7210044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_7210044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210044 prefixEnd_7210044 := by exact prefixLift 7210044
  have htrace : WordTrace (prefixWord ++ tailWord_7210044) baseStart_7210044 baseEnd_7210044 := by
    simpa [prefixWord, tailWord_7210044, baseEnd_7210044] using wordTrace_append hprefix tailTrace_7210044
  have hstable : (prefixWord ++ tailWord_7210044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210044).length < 2 ^ (prefixWord ++ tailWord_7210044).sum := by decide
  have hdescent : baseEnd_7210044 < baseStart_7210044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210047 : List Nat := [1, 1, 2, 2, 3, 1, 1, 12]
def baseStart_7210047 : Nat := 118140960795 + 7210047 * 2 ^ 59
def prefixEnd_7210047 : Nat := 4983230072969 + 3 ^ 40 * 7210047 * 2
def baseEnd_7210047 : Nat := 137119246389172495987189

theorem tailTrace_7210047 : CollatzResearch.WordTrace tailWord_7210047 prefixEnd_7210047 137119246389172495987189 := by
  unfold tailWord_7210047
  simp only [CollatzResearch.WordTrace]
  refine ⟨262972018110238571837700395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175314678740159047891800263 262972018110238571837700395)
  ·
    refine ⟨394458027165357857756550593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262972018110238571837700395 394458027165357857756550593)
    ·
      refine ⟨295843520374018393317412945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394458027165357857756550593 295843520374018393317412945)
      ·
        refine ⟨221882640280513794988059709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295843520374018393317412945 221882640280513794988059709)
        ·
          refine ⟨83205990105192673120522391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221882640280513794988059709 83205990105192673120522391)
          ·
            refine ⟨124808985157789009680783587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83205990105192673120522391 124808985157789009680783587)
            ·
              refine ⟨187213477736683514521175381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124808985157789009680783587 187213477736683514521175381)
              ·
                refine ⟨137119246389172495987189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 187213477736683514521175381 137119246389172495987189)
                ·
                  rfl

theorem cell23_7210047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 12].length) (baseStart_7210047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210047 prefixEnd_7210047 := by exact prefixLift 7210047
  have htrace : WordTrace (prefixWord ++ tailWord_7210047) baseStart_7210047 baseEnd_7210047 := by
    simpa [prefixWord, tailWord_7210047, baseEnd_7210047] using wordTrace_append hprefix tailTrace_7210047
  have hstable : (prefixWord ++ tailWord_7210047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210047).length < 2 ^ (prefixWord ++ tailWord_7210047).sum := by decide
  have hdescent : baseEnd_7210047 < baseStart_7210047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210058 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 3, 2, 2]
def baseStart_7210058 : Nat := 118140960795 + 7210058 * 2 ^ 59
def prefixEnd_7210058 : Nat := 4983230072969 + 3 ^ 40 * 7210058 * 2
def baseEnd_7210058 : Nat := 3702225300794856848616553

theorem tailTrace_7210058 : CollatzResearch.WordTrace tailWord_7210058 prefixEnd_7210058 3702225300794856848616553 := by
  unfold tailWord_7210058
  simp only [CollatzResearch.WordTrace]
  refine ⟨65743104828299680179087707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175314946208799147144233885 65743104828299680179087707)
  ·
    refine ⟨98614657242449520268631561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65743104828299680179087707 98614657242449520268631561)
    ·
      refine ⟨73960992931837140201473671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98614657242449520268631561 73960992931837140201473671)
      ·
        refine ⟨110941489397755710302210507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73960992931837140201473671 110941489397755710302210507)
        ·
          refine ⟨166412234096633565453315761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110941489397755710302210507 166412234096633565453315761)
          ·
            refine ⟨124809175572475174089986821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166412234096633565453315761 124809175572475174089986821)
            ·
              refine ⟨23401720419839095141872529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124809175572475174089986821 23401720419839095141872529)
              ·
                refine ⟨17551290314879321356404397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23401720419839095141872529 17551290314879321356404397)
                ·
                  refine ⟨6581733868079745508651649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17551290314879321356404397 6581733868079745508651649)
                  ·
                    refine ⟨4936300401059809131488737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6581733868079745508651649 4936300401059809131488737)
                    ·
                      refine ⟨3702225300794856848616553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936300401059809131488737 3702225300794856848616553)
                      ·
                        rfl

theorem cell23_7210058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_7210058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210058 prefixEnd_7210058 := by exact prefixLift 7210058
  have htrace : WordTrace (prefixWord ++ tailWord_7210058) baseStart_7210058 baseEnd_7210058 := by
    simpa [prefixWord, tailWord_7210058, baseEnd_7210058] using wordTrace_append hprefix tailTrace_7210058
  have hstable : (prefixWord ++ tailWord_7210058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210058).length < 2 ^ (prefixWord ++ tailWord_7210058).sum := by decide
  have hdescent : baseEnd_7210058 < baseStart_7210058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210092 : List Nat := [2, 2, 1, 1, 3, 2, 5, 2, 1, 2, 2]
def baseStart_7210092 : Nat := 118140960795 + 7210092 * 2 ^ 59
def prefixEnd_7210092 : Nat := 4983230072969 + 3 ^ 40 * 7210092 * 2
def baseEnd_7210092 : Nat := 3702242759137109715591397

theorem tailTrace_7210092 : CollatzResearch.WordTrace tailWord_7210092 prefixEnd_7210092 3702242759137109715591397 := by
  unfold tailWord_7210092
  simp only [CollatzResearch.WordTrace]
  refine ⟨131486829697537772261544265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175315772930050363015392353 131486829697537772261544265)
  ·
    refine ⟨98615122273153329196158199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131486829697537772261544265 98615122273153329196158199)
    ·
      refine ⟨147922683409729993794237299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98615122273153329196158199 147922683409729993794237299)
      ·
        refine ⟨221884025114594990691355949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147922683409729993794237299 221884025114594990691355949)
        ·
          refine ⟨83206509417973121509258481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221884025114594990691355949 83206509417973121509258481)
          ·
            refine ⟨62404882063479841131943861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83206509417973121509258481 62404882063479841131943861)
            ·
              refine ⟨5850457693451235106119737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62404882063479841131943861 5850457693451235106119737)
              ·
                refine ⟨4387843270088426329589803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5850457693451235106119737 4387843270088426329589803)
                ·
                  refine ⟨6581764905132639494384705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4387843270088426329589803 6581764905132639494384705)
                  ·
                    refine ⟨4936323678849479620788529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6581764905132639494384705 4936323678849479620788529)
                    ·
                      refine ⟨3702242759137109715591397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936323678849479620788529 3702242759137109715591397)
                      ·
                        rfl

theorem cell23_7210092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 1, 2, 2].length) (baseStart_7210092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210092 prefixEnd_7210092 := by exact prefixLift 7210092
  have htrace : WordTrace (prefixWord ++ tailWord_7210092) baseStart_7210092 baseEnd_7210092 := by
    simpa [prefixWord, tailWord_7210092, baseEnd_7210092] using wordTrace_append hprefix tailTrace_7210092
  have hstable : (prefixWord ++ tailWord_7210092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210092).length < 2 ^ (prefixWord ++ tailWord_7210092).sum := by decide
  have hdescent : baseEnd_7210092 < baseStart_7210092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210108 : List Nat := [2, 2, 2, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_7210108 : Nat := 118140960795 + 7210108 * 2 ^ 59
def prefixEnd_7210108 : Nat := 4983230072969 + 3 ^ 40 * 7210108 * 2
def baseEnd_7210108 : Nat := 3702250974827581652991323

theorem tailTrace_7210108 : CollatzResearch.WordTrace tailWord_7210108 prefixEnd_7210108 3702250974827581652991323 := by
  unfold tailWord_7210108
  simp only [CollatzResearch.WordTrace]
  refine ⟨131487121481508789627835489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175316161975345052837113985 131487121481508789627835489)
  ·
    refine ⟨98615341111131592220876617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131487121481508789627835489 98615341111131592220876617)
    ·
      refine ⟨73961505833348694165657463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98615341111131592220876617 73961505833348694165657463)
      ·
        refine ⟨110942258750023041248486195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73961505833348694165657463 110942258750023041248486195)
        ·
          refine ⟨166413388125034561872729293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110942258750023041248486195 166413388125034561872729293)
          ·
            refine ⟨62405020546887960702273485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166413388125034561872729293 62405020546887960702273485)
            ·
              refine ⟨23401882705082985263352557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62405020546887960702273485 23401882705082985263352557)
              ·
                refine ⟨8775706014406119473757209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23401882705082985263352557 8775706014406119473757209)
                ·
                  refine ⟨6581779510804589605317907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8775706014406119473757209 6581779510804589605317907)
                  ·
                    refine ⟨9872669266206884407976861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6581779510804589605317907 9872669266206884407976861)
                    ·
                      refine ⟨3702250974827581652991323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9872669266206884407976861 3702250974827581652991323)
                      ·
                        rfl

theorem cell23_7210108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_7210108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210108 prefixEnd_7210108 := by exact prefixLift 7210108
  have htrace : WordTrace (prefixWord ++ tailWord_7210108) baseStart_7210108 baseEnd_7210108 := by
    simpa [prefixWord, tailWord_7210108, baseEnd_7210108] using wordTrace_append hprefix tailTrace_7210108
  have hstable : (prefixWord ++ tailWord_7210108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210108).length < 2 ^ (prefixWord ++ tailWord_7210108).sum := by decide
  have hdescent : baseEnd_7210108 < baseStart_7210108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210131 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 3, 4, 2]
def baseStart_7210131 : Nat := 118140960795 + 7210131 * 2 ^ 59
def prefixEnd_7210131 : Nat := 4983230072969 + 3 ^ 40 * 7210131 * 2
def baseEnd_7210131 : Nat := 3702262784882635063003717

theorem tailTrace_7210131 : CollatzResearch.WordTrace tailWord_7210131 prefixEnd_7210131 3702262784882635063003717 := by
  unfold tailWord_7210131
  simp only [CollatzResearch.WordTrace]
  refine ⟨262975081841934254183758247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175316721227956169455838831 262975081841934254183758247)
  ·
    refine ⟨394462622762901381275637371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262975081841934254183758247 394462622762901381275637371)
    ·
      refine ⟨591693934144352071913456057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394462622762901381275637371 591693934144352071913456057)
      ·
        refine ⟨443770450608264053935092043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591693934144352071913456057 443770450608264053935092043)
        ·
          refine ⟨665655675912396080902638065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443770450608264053935092043 665655675912396080902638065)
          ·
            refine ⟨499241756934297060676978549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665655675912396080902638065 499241756934297060676978549)
            ·
              refine ⟨46803914712590349438466739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 499241756934297060676978549 46803914712590349438466739)
              ·
                refine ⟨70205872068885524157700109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46803914712590349438466739 70205872068885524157700109)
                ·
                  refine ⟨26327202025832071559137541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70205872068885524157700109 26327202025832071559137541)
                  ·
                    refine ⟨4936350379843513417338289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26327202025832071559137541 4936350379843513417338289)
                    ·
                      refine ⟨3702262784882635063003717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936350379843513417338289 3702262784882635063003717)
                      ·
                        rfl

theorem cell23_7210131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 4, 2].length) (baseStart_7210131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210131 prefixEnd_7210131 := by exact prefixLift 7210131
  have htrace : WordTrace (prefixWord ++ tailWord_7210131) baseStart_7210131 baseEnd_7210131 := by
    simpa [prefixWord, tailWord_7210131, baseEnd_7210131] using wordTrace_append hprefix tailTrace_7210131
  have hstable : (prefixWord ++ tailWord_7210131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210131).length < 2 ^ (prefixWord ++ tailWord_7210131).sum := by decide
  have hdescent : baseEnd_7210131 < baseStart_7210131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210142 : List Nat := [4, 3, 1, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_7210142 : Nat := 118140960795 + 7210142 * 2 ^ 59
def prefixEnd_7210142 : Nat := 4983230072969 + 3 ^ 40 * 7210142 * 2
def baseEnd_7210142 : Nat := 3702268433169834519966167

theorem tailTrace_7210142 : CollatzResearch.WordTrace tailWord_7210142 prefixEnd_7210142 3702268433169834519966167 := by
  unfold tailWord_7210142
  simp only [CollatzResearch.WordTrace]
  refine ⟨32871935380611800382801085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175316988696596268708272453 32871935380611800382801085)
  ·
    refine ⟨12326975767729425143550407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32871935380611800382801085 12326975767729425143550407)
    ·
      refine ⟨18490463651594137715325611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12326975767729425143550407 18490463651594137715325611)
      ·
        refine ⟨27735695477391206572988417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18490463651594137715325611 27735695477391206572988417)
        ·
          refine ⟨20801771608043404929741313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27735695477391206572988417 20801771608043404929741313)
          ·
            refine ⟨15601328706032553697305985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20801771608043404929741313 15601328706032553697305985)
            ·
              refine ⟨11700996529524415272979489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15601328706032553697305985 11700996529524415272979489)
              ·
                refine ⟨8775747397143311454734617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11700996529524415272979489 8775747397143311454734617)
                ·
                  refine ⟨6581810547857483591050963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8775747397143311454734617 6581810547857483591050963)
                  ·
                    refine ⟨9872715821786225386576445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6581810547857483591050963 9872715821786225386576445)
                    ·
                      refine ⟨3702268433169834519966167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9872715821786225386576445 3702268433169834519966167)
                      ·
                        rfl

theorem cell23_7210142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_7210142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210142 prefixEnd_7210142 := by exact prefixLift 7210142
  have htrace : WordTrace (prefixWord ++ tailWord_7210142) baseStart_7210142 baseEnd_7210142 := by
    simpa [prefixWord, tailWord_7210142, baseEnd_7210142] using wordTrace_append hprefix tailTrace_7210142
  have hstable : (prefixWord ++ tailWord_7210142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210142).length < 2 ^ (prefixWord ++ tailWord_7210142).sum := by decide
  have hdescent : baseEnd_7210142 < baseStart_7210142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210161 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_7210161 : Nat := 118140960795 + 7210161 * 2 ^ 59
def prefixEnd_7210161 : Nat := 4983230072969 + 3 ^ 40 * 7210161 * 2
def baseEnd_7210161 : Nat := 3702278189302269945628579

theorem tailTrace_7210161 : CollatzResearch.WordTrace tailWord_7210161 prefixEnd_7210161 3702278189302269945628579 := by
  unfold tailWord_7210161
  simp only [CollatzResearch.WordTrace]
  refine ⟨262976176031825569307350337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175317450687883712871566891 262976176031825569307350337)
  ·
    refine ⟨197232132023869176980512753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262976176031825569307350337 197232132023869176980512753)
    ·
      refine ⟨147924099017901882735384565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197232132023869176980512753 147924099017901882735384565)
      ·
        refine ⟨13867884282928301506442303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147924099017901882735384565 13867884282928301506442303)
        ·
          refine ⟨20801826424392452259663455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13867884282928301506442303 20801826424392452259663455)
          ·
            refine ⟨31202739636588678389495183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20801826424392452259663455 31202739636588678389495183)
            ·
              refine ⟨46804109454883017584242775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31202739636588678389495183 46804109454883017584242775)
              ·
                refine ⟨70206164182324526376364163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46804109454883017584242775 70206164182324526376364163)
                ·
                  refine ⟨105309246273486789564546245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70206164182324526376364163 105309246273486789564546245)
                  ·
                    refine ⟨19745483676278773043352421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105309246273486789564546245 19745483676278773043352421)
                    ·
                      refine ⟨3702278189302269945628579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19745483676278773043352421 3702278189302269945628579)
                      ·
                        rfl

theorem cell23_7210161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_7210161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210161 prefixEnd_7210161 := by exact prefixLift 7210161
  have htrace : WordTrace (prefixWord ++ tailWord_7210161) baseStart_7210161 baseEnd_7210161 := by
    simpa [prefixWord, tailWord_7210161, baseEnd_7210161] using wordTrace_append hprefix tailTrace_7210161
  have hstable : (prefixWord ++ tailWord_7210161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210161).length < 2 ^ (prefixWord ++ tailWord_7210161).sum := by decide
  have hdescent : baseEnd_7210161 < baseStart_7210161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210191 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 1, 7, 2]
def baseStart_7210191 : Nat := 118140960795 + 7210191 * 2 ^ 59
def prefixEnd_7210191 : Nat := 4983230072969 + 3 ^ 40 * 7210191 * 2
def baseEnd_7210191 : Nat := 3702293593721904828253441

theorem tailTrace_7210191 : CollatzResearch.WordTrace tailWord_7210191 prefixEnd_7210191 3702293593721904828253441 := by
  unfold tailWord_7210191
  simp only [CollatzResearch.WordTrace]
  refine ⟨262977270221716884430942427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175318180147811256287294951 262977270221716884430942427)
  ·
    refine ⟨394465905332575326646413641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262977270221716884430942427 394465905332575326646413641)
    ·
      refine ⟨295849428999431494984810231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394465905332575326646413641 295849428999431494984810231)
      ·
        refine ⟨443774143499147242477215347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295849428999431494984810231 443774143499147242477215347)
        ·
          refine ⟨665661215248720863715823021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443774143499147242477215347 665661215248720863715823021)
          ·
            refine ⟨249622955718270323893433633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 665661215248720863715823021 249622955718270323893433633)
            ·
              refine ⟨187217216788702742920075225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249622955718270323893433633 187217216788702742920075225)
              ·
                refine ⟨140412912591527057190056419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187217216788702742920075225 140412912591527057190056419)
                ·
                  refine ⟨210619368887290585785084629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140412912591527057190056419 210619368887290585785084629)
                  ·
                    refine ⟨4936391458295873104337921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 210619368887290585785084629 4936391458295873104337921)
                    ·
                      refine ⟨3702293593721904828253441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936391458295873104337921 3702293593721904828253441)
                      ·
                        rfl

theorem cell23_7210191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 7, 2].length) (baseStart_7210191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210191 prefixEnd_7210191 := by exact prefixLift 7210191
  have htrace : WordTrace (prefixWord ++ tailWord_7210191) baseStart_7210191 baseEnd_7210191 := by
    simpa [prefixWord, tailWord_7210191, baseEnd_7210191] using wordTrace_append hprefix tailTrace_7210191
  have hstable : (prefixWord ++ tailWord_7210191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210191).length < 2 ^ (prefixWord ++ tailWord_7210191).sum := by decide
  have hdescent : baseEnd_7210191 < baseStart_7210191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210238 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_7210238 : Nat := 118140960795 + 7210238 * 2 ^ 59
def prefixEnd_7210238 : Nat := 4983230072969 + 3 ^ 40 * 7210238 * 2
def baseEnd_7210238 : Nat := 3702317727312666144365725

theorem tailTrace_7210238 : CollatzResearch.WordTrace tailWord_7210238 prefixEnd_7210238 3702317727312666144365725 := by
  unfold tailWord_7210238
  simp only [CollatzResearch.WordTrace]
  refine ⟨32872373056568326432237921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175319322968364407638602245 32872373056568326432237921)
  ·
    refine ⟨24654279792426244824178441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32872373056568326432237921 24654279792426244824178441)
    ·
      refine ⟨18490709844319683618133831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24654279792426244824178441 18490709844319683618133831)
      ·
        refine ⟨27736064766479525427200747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18490709844319683618133831 27736064766479525427200747)
        ·
          refine ⟨41604097149719288140801121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27736064766479525427200747 41604097149719288140801121)
          ·
            refine ⟨31203072862289466105600841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41604097149719288140801121 31203072862289466105600841)
            ·
              refine ⟨23402304646717099579200631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31203072862289466105600841 23402304646717099579200631)
              ·
                refine ⟨35103456970075649368800947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23402304646717099579200631 35103456970075649368800947)
                ·
                  refine ⟨52655185455113474053201421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35103456970075649368800947 52655185455113474053201421)
                  ·
                    refine ⟨19745694545667552769950533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52655185455113474053201421 19745694545667552769950533)
                    ·
                      refine ⟨3702317727312666144365725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19745694545667552769950533 3702317727312666144365725)
                      ·
                        rfl

theorem cell23_7210238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_7210238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210238 prefixEnd_7210238 := by exact prefixLift 7210238
  have htrace : WordTrace (prefixWord ++ tailWord_7210238) baseStart_7210238 baseEnd_7210238 := by
    simpa [prefixWord, tailWord_7210238, baseEnd_7210238] using wordTrace_append hprefix tailTrace_7210238
  have hstable : (prefixWord ++ tailWord_7210238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210238).length < 2 ^ (prefixWord ++ tailWord_7210238).sum := by decide
  have hdescent : baseEnd_7210238 < baseStart_7210238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210261 : List Nat := [1, 3, 2, 1, 2, 1, 1, 6, 6]
def baseStart_7210261 : Nat := 118140960795 + 7210261 * 2 ^ 59
def prefixEnd_7210261 : Nat := 4983230072969 + 3 ^ 40 * 7210261 * 2
def baseEnd_7210261 : Nat := 411369948596413283819791

theorem tailTrace_7210261 : CollatzResearch.WordTrace tailWord_7210261 prefixEnd_7210261 411369948596413283819791 := by
  unfold tailWord_7210261
  simp only [CollatzResearch.WordTrace]
  refine ⟨262979823331463286385990637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175319882220975524257327091 262979823331463286385990637)
  ·
    refine ⟨98617433749298732394746489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262979823331463286385990637 98617433749298732394746489)
    ·
      refine ⟨73963075311974049296059867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98617433749298732394746489 73963075311974049296059867)
      ·
        refine ⟨110944612967961073944089801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73963075311974049296059867 110944612967961073944089801)
        ·
          refine ⟨83208459725970805458067351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110944612967961073944089801 83208459725970805458067351)
          ·
            refine ⟨124812689588956208187101027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83208459725970805458067351 124812689588956208187101027)
            ·
              refine ⟨187219034383434312280651541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124812689588956208187101027 187219034383434312280651541)
              ·
                refine ⟨8775892236723483388155541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 187219034383434312280651541 8775892236723483388155541)
                ·
                  refine ⟨411369948596413283819791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8775892236723483388155541 411369948596413283819791)
                  ·
                    rfl

theorem cell23_7210261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_7210261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210261 prefixEnd_7210261 := by exact prefixLift 7210261
  have htrace : WordTrace (prefixWord ++ tailWord_7210261) baseStart_7210261 baseEnd_7210261 := by
    simpa [prefixWord, tailWord_7210261, baseEnd_7210261] using wordTrace_append hprefix tailTrace_7210261
  have hstable : (prefixWord ++ tailWord_7210261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210261).length < 2 ^ (prefixWord ++ tailWord_7210261).sum := by decide
  have hdescent : baseEnd_7210261 < baseStart_7210261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210288 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 5, 1, 3]
def baseStart_7210288 : Nat := 118140960795 + 7210288 * 2 ^ 59
def prefixEnd_7210288 : Nat := 4983230072969 + 3 ^ 40 * 7210288 * 2
def baseEnd_7210288 : Nat := 3702343401345390948740495

theorem tailTrace_7210288 : CollatzResearch.WordTrace tailWord_7210288 prefixEnd_7210288 3702343401345390948740495 := by
  unfold tailWord_7210288
  simp only [CollatzResearch.WordTrace]
  refine ⟨131490404051182734998611759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175320538734910313331482345 131490404051182734998611759)
  ·
    refine ⟨197235606076774102497917639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131490404051182734998611759 197235606076774102497917639)
    ·
      refine ⟨295853409115161153746876459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197235606076774102497917639 295853409115161153746876459)
      ·
        refine ⟨443780113672741730620314689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295853409115161153746876459 443780113672741730620314689)
        ·
          refine ⟨332835085254556297965236017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443780113672741730620314689 332835085254556297965236017)
          ·
            refine ⟨249626313940917223473927013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332835085254556297965236017 249626313940917223473927013)
            ·
              refine ⟨46804933863921979401361315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249626313940917223473927013 46804933863921979401361315)
              ·
                refine ⟨70207400795882969102041973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46804933863921979401361315 70207400795882969102041973)
                ·
                  refine ⟨6581943824614028353316435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70207400795882969102041973 6581943824614028353316435)
                  ·
                    refine ⟨9872915736921042529974653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6581943824614028353316435 9872915736921042529974653)
                    ·
                      refine ⟨3702343401345390948740495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9872915736921042529974653 3702343401345390948740495)
                      ·
                        rfl

theorem cell23_7210288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 5, 1, 3].length) (baseStart_7210288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210288 prefixEnd_7210288 := by exact prefixLift 7210288
  have htrace : WordTrace (prefixWord ++ tailWord_7210288) baseStart_7210288 baseEnd_7210288 := by
    simpa [prefixWord, tailWord_7210288, baseEnd_7210288] using wordTrace_append hprefix tailTrace_7210288
  have hstable : (prefixWord ++ tailWord_7210288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210288).length < 2 ^ (prefixWord ++ tailWord_7210288).sum := by decide
  have hdescent : baseEnd_7210288 < baseStart_7210288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210321 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 3, 6]
def baseStart_7210321 : Nat := 118140960795 + 7210321 * 2 ^ 59
def prefixEnd_7210321 : Nat := 4983230072969 + 3 ^ 40 * 7210321 * 2
def baseEnd_7210321 : Nat := 1234120115402329773209281

theorem tailTrace_7210321 : CollatzResearch.WordTrace tailWord_7210321 prefixEnd_7210321 1234120115402329773209281 := by
  unfold tailWord_7210321
  simp only [CollatzResearch.WordTrace]
  refine ⟨262982011711245916633174817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175321341140830611088783211 262982011711245916633174817)
  ·
    refine ⟨197236508783434437474881113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262982011711245916633174817 197236508783434437474881113)
    ·
      refine ⟨147927381587575828106160835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197236508783434437474881113 147927381587575828106160835)
      ·
        refine ⟨221891072381363742159241253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147927381587575828106160835 221891072381363742159241253)
        ·
          refine ⟨41604576071505701654857735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221891072381363742159241253 41604576071505701654857735)
          ·
            refine ⟨62406864107258552482286603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41604576071505701654857735 62406864107258552482286603)
            ·
              refine ⟨93610296160887828723429905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62406864107258552482286603 93610296160887828723429905)
              ·
                refine ⟨70207722120665871542572429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93610296160887828723429905 70207722120665871542572429)
                ·
                  refine ⟨26327895795249701828464661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70207722120665871542572429 26327895795249701828464661)
                  ·
                    refine ⟨1234120115402329773209281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26327895795249701828464661 1234120115402329773209281)
                    ·
                      rfl

theorem cell23_7210321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_7210321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210321 prefixEnd_7210321 := by exact prefixLift 7210321
  have htrace : WordTrace (prefixWord ++ tailWord_7210321) baseStart_7210321 baseEnd_7210321 := by
    simpa [prefixWord, tailWord_7210321, baseEnd_7210321] using wordTrace_append hprefix tailTrace_7210321
  have hstable : (prefixWord ++ tailWord_7210321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210321).length < 2 ^ (prefixWord ++ tailWord_7210321).sum := by decide
  have hdescent : baseEnd_7210321 < baseStart_7210321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210365 : List Nat := [1, 4, 1, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_7210365 : Nat := 118140960795 + 7210365 * 2 ^ 59
def prefixEnd_7210365 : Nat := 4983230072969 + 3 ^ 40 * 7210365 * 2
def baseEnd_7210365 : Nat := 3702382939355787147477641

theorem tailTrace_7210365 : CollatzResearch.WordTrace tailWord_7210365 prefixEnd_7210365 3702382939355787147477641 := by
  unfold tailWord_7210365
  simp only [CollatzResearch.WordTrace]
  refine ⟨262983616523086512147776549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175322411015391008098517699 262983616523086512147776549)
  ·
    refine ⟨49309428098078721027708103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262983616523086512147776549 49309428098078721027708103)
    ·
      refine ⟨73964142147118081541562155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49309428098078721027708103 73964142147118081541562155)
      ·
        refine ⟨110946213220677122312343233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73964142147118081541562155 110946213220677122312343233)
        ·
          refine ⟨83209659915507841734257425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110946213220677122312343233 83209659915507841734257425)
          ·
            refine ⟨62407244936630881300693069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83209659915507841734257425 62407244936630881300693069)
            ·
              refine ⟨23402716851236580487759901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62407244936630881300693069 23402716851236580487759901)
              ·
                refine ⟨8776018819213717682909963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23402716851236580487759901 8776018819213717682909963)
                ·
                  refine ⟨13164028228820576524364945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8776018819213717682909963 13164028228820576524364945)
                  ·
                    refine ⟨9873021171615432393273709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13164028228820576524364945 9873021171615432393273709)
                    ·
                      refine ⟨3702382939355787147477641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9873021171615432393273709 3702382939355787147477641)
                      ·
                        rfl

theorem cell23_7210365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_7210365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210365 prefixEnd_7210365 := by exact prefixLift 7210365
  have htrace : WordTrace (prefixWord ++ tailWord_7210365) baseStart_7210365 baseEnd_7210365 := by
    simpa [prefixWord, tailWord_7210365, baseEnd_7210365] using wordTrace_append hprefix tailTrace_7210365
  have hstable : (prefixWord ++ tailWord_7210365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210365).length < 2 ^ (prefixWord ++ tailWord_7210365).sum := by decide
  have hdescent : baseEnd_7210365 < baseStart_7210365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210372 : List Nat := [2, 3, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_7210372 : Nat := 118140960795 + 7210372 * 2 ^ 59
def prefixEnd_7210372 : Nat := 4983230072969 + 3 ^ 40 * 7210372 * 2
def baseEnd_7210372 : Nat := 1234128844573456206696703

theorem tailTrace_7210372 : CollatzResearch.WordTrace tailWord_7210372 prefixEnd_7210372 1234128844573456206696703 := by
  unfold tailWord_7210372
  simp only [CollatzResearch.WordTrace]
  refine ⟨131491935917030576171640685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175322581222707434895520913 131491935917030576171640685)
  ·
    refine ⟨49309475968886466064365257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131491935917030576171640685 49309475968886466064365257)
    ·
      refine ⟨36982106976664849548273943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49309475968886466064365257 36982106976664849548273943)
      ·
        refine ⟨55473160464997274322410915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36982106976664849548273943 55473160464997274322410915)
        ·
          refine ⟨83209740697495911483616373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55473160464997274322410915 83209740697495911483616373)
          ·
            refine ⟨7800913190390241701589035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83209740697495911483616373 7800913190390241701589035)
            ·
              refine ⟨11701369785585362552383553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7800913190390241701589035 11701369785585362552383553)
              ·
                refine ⟨8776027339189021914287665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11701369785585362552383553 8776027339189021914287665)
                ·
                  refine ⟨6582020504391766435715749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8776027339189021914287665 6582020504391766435715749)
                  ·
                    refine ⟨1234128844573456206696703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6582020504391766435715749 1234128844573456206696703)
                    ·
                      rfl

theorem cell23_7210372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_7210372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210372 prefixEnd_7210372 := by exact prefixLift 7210372
  have htrace : WordTrace (prefixWord ++ tailWord_7210372) baseStart_7210372 baseEnd_7210372 := by
    simpa [prefixWord, tailWord_7210372, baseEnd_7210372] using wordTrace_append hprefix tailTrace_7210372
  have hstable : (prefixWord ++ tailWord_7210372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210372).length < 2 ^ (prefixWord ++ tailWord_7210372).sum := by decide
  have hdescent : baseEnd_7210372 < baseStart_7210372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210392 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 1, 2, 4]
def baseStart_7210392 : Nat := 118140960795 + 7210392 * 2 ^ 59
def prefixEnd_7210392 : Nat := 4983230072969 + 3 ^ 40 * 7210392 * 2
def baseEnd_7210392 : Nat := 3702396803333458541840017

theorem tailTrace_7210392 : CollatzResearch.WordTrace tailWord_7210392 prefixEnd_7210392 3702396803333458541840017 := by
  unfold tailWord_7210392
  simp only [CollatzResearch.WordTrace]
  refine ⟨131492300646994347879504715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175323067529325797172672953 131492300646994347879504715)
  ·
    refine ⟨197238450970491521819257073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131492300646994347879504715 197238450970491521819257073)
    ·
      refine ⟨147928838227868641364442805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197238450970491521819257073 147928838227868641364442805)
      ·
        refine ⟨13868328583862685127916513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147928838227868641364442805 13868328583862685127916513)
        ·
          refine ⟨10401246437897013845937385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13868328583862685127916513 10401246437897013845937385)
          ·
            refine ⟨7800934828422760384453039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10401246437897013845937385 7800934828422760384453039)
            ·
              refine ⟨11701402242634140576679559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7800934828422760384453039 11701402242634140576679559)
              ·
                refine ⟨17552103363951210865019339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11701402242634140576679559 17552103363951210865019339)
                ·
                  refine ⟨26328155045926816297529009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17552103363951210865019339 26328155045926816297529009)
                  ·
                    refine ⟨19746116284445112223146757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26328155045926816297529009 19746116284445112223146757)
                    ·
                      refine ⟨3702396803333458541840017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19746116284445112223146757 3702396803333458541840017)
                      ·
                        rfl

theorem cell23_7210392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_7210392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210392 prefixEnd_7210392 := by exact prefixLift 7210392
  have htrace : WordTrace (prefixWord ++ tailWord_7210392) baseStart_7210392 baseEnd_7210392 := by
    simpa [prefixWord, tailWord_7210392, baseEnd_7210392] using wordTrace_append hprefix tailTrace_7210392
  have hstable : (prefixWord ++ tailWord_7210392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210392).length < 2 ^ (prefixWord ++ tailWord_7210392).sum := by decide
  have hdescent : baseEnd_7210392 < baseStart_7210392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210413 : List Nat := [1, 5, 2, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_7210413 : Nat := 118140960795 + 7210413 * 2 ^ 59
def prefixEnd_7210413 : Nat := 4983230072969 + 3 ^ 40 * 7210413 * 2
def baseEnd_7210413 : Nat := 3702407586427202959677421

theorem tailTrace_7210413 : CollatzResearch.WordTrace tailWord_7210413 prefixEnd_7210413 3702407586427202959677421 := by
  unfold tailWord_7210413
  simp only [CollatzResearch.WordTrace]
  refine ⟨262985367226912616345523893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175323578151275077563682595 262985367226912616345523893)
  ·
    refine ⟨24654878177523057782392865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262985367226912616345523893 24654878177523057782392865)
    ·
      refine ⟨18491158633142293336794649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24654878177523057782392865 18491158633142293336794649)
      ·
        refine ⟨13868368974856720002595987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18491158633142293336794649 13868368974856720002595987)
        ·
          refine ⟨20802553462285080003893981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13868368974856720002595987 20802553462285080003893981)
          ·
            refine ⟨7800957548356905001460243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20802553462285080003893981 7800957548356905001460243)
            ·
              refine ⟨11701436322535357502190365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7800957548356905001460243 11701436322535357502190365)
              ·
                refine ⟨4388038620950759063321387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11701436322535357502190365 4388038620950759063321387)
                ·
                  refine ⟨6582057931426138594982081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388038620950759063321387 6582057931426138594982081)
                  ·
                    refine ⟨4936543448569603946236561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6582057931426138594982081 4936543448569603946236561)
                    ·
                      refine ⟨3702407586427202959677421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936543448569603946236561 3702407586427202959677421)
                      ·
                        rfl

theorem cell23_7210413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_7210413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210413 prefixEnd_7210413 := by exact prefixLift 7210413
  have htrace : WordTrace (prefixWord ++ tailWord_7210413) baseStart_7210413 baseEnd_7210413 := by
    simpa [prefixWord, tailWord_7210413, baseEnd_7210413] using wordTrace_append hprefix tailTrace_7210413
  have hstable : (prefixWord ++ tailWord_7210413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210413).length < 2 ^ (prefixWord ++ tailWord_7210413).sum := by decide
  have hdescent : baseEnd_7210413 < baseStart_7210413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210486 : List Nat := [5, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_7210486 : Nat := 118140960795 + 7210486 * 2 ^ 59
def prefixEnd_7210486 : Nat := 4983230072969 + 3 ^ 40 * 7210486 * 2
def baseEnd_7210486 : Nat := 3702445070514981174064585

theorem tailTrace_7210486 : CollatzResearch.WordTrace tailWord_7210486 prefixEnd_7210486 3702445070514981174064585 := by
  unfold tailWord_7210486
  simp only [CollatzResearch.WordTrace]
  refine ⟨16436751859728009363308207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175325353170432099875287541 16436751859728009363308207)
  ·
    refine ⟨24655127789592014044962311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16436751859728009363308207 24655127789592014044962311)
    ·
      refine ⟨36982691684388021067443467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24655127789592014044962311 36982691684388021067443467)
      ·
        refine ⟨55474037526582031601165201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36982691684388021067443467 55474037526582031601165201)
        ·
          refine ⟨41605528144936523700873901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55474037526582031601165201 41605528144936523700873901)
          ·
            refine ⟨15602073054351196387827713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41605528144936523700873901 15602073054351196387827713)
            ·
              refine ⟨11701554790763397290870785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15602073054351196387827713 11701554790763397290870785)
              ·
                refine ⟨8776166093072547968153089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11701554790763397290870785 8776166093072547968153089)
                ·
                  refine ⟨6582124569804410976114817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8776166093072547968153089 6582124569804410976114817)
                  ·
                    refine ⟨4936593427353308232086113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6582124569804410976114817 4936593427353308232086113)
                    ·
                      refine ⟨3702445070514981174064585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936593427353308232086113 3702445070514981174064585)
                      ·
                        rfl

theorem cell23_7210486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_7210486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210486 prefixEnd_7210486 := by exact prefixLift 7210486
  have htrace : WordTrace (prefixWord ++ tailWord_7210486) baseStart_7210486 baseEnd_7210486 := by
    simpa [prefixWord, tailWord_7210486, baseEnd_7210486] using wordTrace_append hprefix tailTrace_7210486
  have hstable : (prefixWord ++ tailWord_7210486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210486).length < 2 ^ (prefixWord ++ tailWord_7210486).sum := by decide
  have hdescent : baseEnd_7210486 < baseStart_7210486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210492 : List Nat := [2, 2, 2, 1, 2, 1, 6, 2, 5]
def baseStart_7210492 : Nat := 118140960795 + 7210492 * 2 ^ 59
def prefixEnd_7210492 : Nat := 4983230072969 + 3 ^ 40 * 7210492 * 2
def baseEnd_7210492 : Nat := 411383127933212016732173

theorem tailTrace_7210492 : CollatzResearch.WordTrace tailWord_7210492 prefixEnd_7210492 411383127933212016732173 := by
  unfold tailWord_7210492
  simp only [CollatzResearch.WordTrace]
  refine ⟨131494124296813206418824865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175325499062417608558433153 131494124296813206418824865)
  ·
    refine ⟨98620593222609904814118649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131494124296813206418824865 98620593222609904814118649)
    ·
      refine ⟨73965444916957428610588987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98620593222609904814118649 73965444916957428610588987)
      ·
        refine ⟨110948167375436142915883481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73965444916957428610588987 110948167375436142915883481)
        ·
          refine ⟨83211125531577107186912611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110948167375436142915883481 83211125531577107186912611)
          ·
            refine ⟨124816688297365660780368917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83211125531577107186912611 124816688297365660780368917)
            ·
              refine ⟨5850782263939015349079793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124816688297365660780368917 5850782263939015349079793)
              ·
                refine ⟨4388086697954261511809845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5850782263939015349079793 4388086697954261511809845)
                ·
                  refine ⟨411383127933212016732173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4388086697954261511809845 411383127933212016732173)
                  ·
                    rfl

theorem cell23_7210492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 5].length) (baseStart_7210492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210492 prefixEnd_7210492 := by exact prefixLift 7210492
  have htrace : WordTrace (prefixWord ++ tailWord_7210492) baseStart_7210492 baseEnd_7210492 := by
    simpa [prefixWord, tailWord_7210492, baseEnd_7210492] using wordTrace_append hprefix tailTrace_7210492
  have hstable : (prefixWord ++ tailWord_7210492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210492).length < 2 ^ (prefixWord ++ tailWord_7210492).sum := by decide
  have hdescent : baseEnd_7210492 < baseStart_7210492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210509 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 7]
def baseStart_7210509 : Nat := 118140960795 + 7210509 * 2 ^ 59
def prefixEnd_7210509 : Nat := 4983230072969 + 3 ^ 40 * 7210509 * 2
def baseEnd_7210509 : Nat := 411384097841114953786331

theorem tailTrace_7210509 : CollatzResearch.WordTrace tailWord_7210509 prefixEnd_7210509 411384097841114953786331 := by
  unfold tailWord_7210509
  simp only [CollatzResearch.WordTrace]
  refine ⟨262988868634564824741018581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175325912423043216494012387 262988868634564824741018581)
  ·
    refine ⟨6163801608622613079867623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 262988868634564824741018581 6163801608622613079867623)
    ·
      refine ⟨9245702412933919619801435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6163801608622613079867623 9245702412933919619801435)
      ·
        refine ⟨13868553619400879429702153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9245702412933919619801435 13868553619400879429702153)
        ·
          refine ⟨10401415214550659572276615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13868553619400879429702153 10401415214550659572276615)
          ·
            refine ⟨15602122821825989358414923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10401415214550659572276615 15602122821825989358414923)
            ·
              refine ⟨23403184232738984037622385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15602122821825989358414923 23403184232738984037622385)
              ·
                refine ⟨17552388174554238028216789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23403184232738984037622385 17552388174554238028216789)
                ·
                  refine ⟨411384097841114953786331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17552388174554238028216789 411384097841114953786331)
                  ·
                    rfl

theorem cell23_7210509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_7210509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210509 prefixEnd_7210509 := by exact prefixLift 7210509
  have htrace : WordTrace (prefixWord ++ tailWord_7210509) baseStart_7210509 baseEnd_7210509 := by
    simpa [prefixWord, tailWord_7210509, baseEnd_7210509] using wordTrace_append hprefix tailTrace_7210509
  have hstable : (prefixWord ++ tailWord_7210509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210509).length < 2 ^ (prefixWord ++ tailWord_7210509).sum := by decide
  have hdescent : baseEnd_7210509 < baseStart_7210509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210525 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_7210525 : Nat := 118140960795 + 7210525 * 2 ^ 59
def prefixEnd_7210525 : Nat := 4983230072969 + 3 ^ 40 * 7210525 * 2
def baseEnd_7210525 : Nat := 3702465096260506521476905

theorem tailTrace_7210525 : CollatzResearch.WordTrace tailWord_7210525 prefixEnd_7210525 3702465096260506521476905 := by
  unfold tailWord_7210525
  simp only [CollatzResearch.WordTrace]
  refine ⟨262989452202506859473601029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175326301468337906315734019 262989452202506859473601029)
  ·
    refine ⟨49310522287970036151300193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262989452202506859473601029 49310522287970036151300193)
    ·
      refine ⟨36982891715977527113475145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49310522287970036151300193 36982891715977527113475145)
      ·
        refine ⟨27737168786983145335106359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36982891715977527113475145 27737168786983145335106359)
        ·
          refine ⟨41605753180474718002659539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27737168786983145335106359 41605753180474718002659539)
          ·
            refine ⟨62408629770712077003989309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41605753180474718002659539 62408629770712077003989309)
            ·
              refine ⟨23403236164017028876495991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62408629770712077003989309 23403236164017028876495991)
              ·
                refine ⟨35104854246025543314743987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23403236164017028876495991 35104854246025543314743987)
                ·
                  refine ⟨52657281369038314972115981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35104854246025543314743987 52657281369038314972115981)
                  ·
                    refine ⟨19746480513389368114543493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52657281369038314972115981 19746480513389368114543493)
                    ·
                      refine ⟨3702465096260506521476905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19746480513389368114543493 3702465096260506521476905)
                      ·
                        rfl

theorem cell23_7210525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_7210525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210525 prefixEnd_7210525 := by exact prefixLift 7210525
  have htrace : WordTrace (prefixWord ++ tailWord_7210525) baseStart_7210525 baseEnd_7210525 := by
    simpa [prefixWord, tailWord_7210525, baseEnd_7210525] using wordTrace_append hprefix tailTrace_7210525
  have hstable : (prefixWord ++ tailWord_7210525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210525).length < 2 ^ (prefixWord ++ tailWord_7210525).sum := by decide
  have hdescent : baseEnd_7210525 < baseStart_7210525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210545 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 4, 2, 3]
def baseStart_7210545 : Nat := 118140960795 + 7210545 * 2 ^ 59
def prefixEnd_7210545 : Nat := 4983230072969 + 3 ^ 40 * 7210545 * 2
def baseEnd_7210545 : Nat := 3702475365873596443226813

theorem tailTrace_7210545 : CollatzResearch.WordTrace tailWord_7210545 prefixEnd_7210545 3702475365873596443226813 := by
  unfold tailWord_7210545
  simp only [CollatzResearch.WordTrace]
  refine ⟨262990181662434402889329089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175326787774956268592886059 262990181662434402889329089)
  ·
    refine ⟨197242636246825802166996817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262990181662434402889329089 197242636246825802166996817)
    ·
      refine ⟨147931977185119351625247613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197242636246825802166996817 147931977185119351625247613)
      ·
        refine ⟨55474491444419756859467855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147931977185119351625247613 55474491444419756859467855)
        ·
          refine ⟨83211737166629635289201783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55474491444419756859467855 83211737166629635289201783)
          ·
            refine ⟨124817605749944452933802675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83211737166629635289201783 124817605749944452933802675)
            ·
              refine ⟨187226408624916679400704013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124817605749944452933802675 187226408624916679400704013)
              ·
                refine ⟨70209903234343754775264005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187226408624916679400704013 70209903234343754775264005)
                ·
                  refine ⟨13164356856439454020362001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70209903234343754775264005 13164356856439454020362001)
                  ·
                    refine ⟨9873267642329590515271501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13164356856439454020362001 9873267642329590515271501)
                    ·
                      refine ⟨3702475365873596443226813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9873267642329590515271501 3702475365873596443226813)
                      ·
                        rfl

theorem cell23_7210545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_7210545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210545 prefixEnd_7210545 := by exact prefixLift 7210545
  have htrace : WordTrace (prefixWord ++ tailWord_7210545) baseStart_7210545 baseEnd_7210545 := by
    simpa [prefixWord, tailWord_7210545, baseEnd_7210545] using wordTrace_append hprefix tailTrace_7210545
  have hstable : (prefixWord ++ tailWord_7210545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210545).length < 2 ^ (prefixWord ++ tailWord_7210545).sum := by decide
  have hdescent : baseEnd_7210545 < baseStart_7210545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210552 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 3, 4]
def baseStart_7210552 : Nat := 118140960795 + 7210552 * 2 ^ 59
def prefixEnd_7210552 : Nat := 4983230072969 + 3 ^ 40 * 7210552 * 2
def baseEnd_7210552 : Nat := 1234159653412725971946427

theorem tailTrace_7210552 : CollatzResearch.WordTrace tailWord_7210552 prefixEnd_7210552 1234159653412725971946427 := by
  unfold tailWord_7210552
  simp only [CollatzResearch.WordTrace]
  refine ⟨131495218486704521542416955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175326957982272695389889273 131495218486704521542416955)
  ·
    refine ⟨197242827730056782313625433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131495218486704521542416955 197242827730056782313625433)
    ·
      refine ⟨147932120797542586735219075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197242827730056782313625433 147932120797542586735219075)
      ·
        refine ⟨221898181196313880102828613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147932120797542586735219075 221898181196313880102828613)
        ·
          refine ⟨41605908974308852519280365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221898181196313880102828613 41605908974308852519280365)
          ·
            refine ⟨15602215865365819694730137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41605908974308852519280365 15602215865365819694730137)
            ·
              refine ⟨11701661899024364771047603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15602215865365819694730137 11701661899024364771047603)
              ·
                refine ⟨17552492848536547156571405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11701661899024364771047603 17552492848536547156571405)
                ·
                  refine ⟨6582184818201205183714277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17552492848536547156571405 6582184818201205183714277)
                  ·
                    refine ⟨1234159653412725971946427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6582184818201205183714277 1234159653412725971946427)
                    ·
                      rfl

theorem cell23_7210552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_7210552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210552 prefixEnd_7210552 := by exact prefixLift 7210552
  have htrace : WordTrace (prefixWord ++ tailWord_7210552) baseStart_7210552 baseEnd_7210552 := by
    simpa [prefixWord, tailWord_7210552, baseEnd_7210552] using wordTrace_append hprefix tailTrace_7210552
  have hstable : (prefixWord ++ tailWord_7210552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210552).length < 2 ^ (prefixWord ++ tailWord_7210552).sum := by decide
  have hdescent : baseEnd_7210552 < baseStart_7210552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210609 : List Nat := [1, 2, 2, 2, 1, 1, 1, 8, 1, 1, 3]
def baseStart_7210609 : Nat := 118140960795 + 7210609 * 2 ^ 59
def prefixEnd_7210609 : Nat := 4983230072969 + 3 ^ 40 * 7210609 * 2
def baseEnd_7210609 : Nat := 3702508228635484192826519

theorem tailTrace_7210609 : CollatzResearch.WordTrace tailWord_7210609 prefixEnd_7210609 3702508228635484192826519 := by
  unfold tailWord_7210609
  simp only [CollatzResearch.WordTrace]
  refine ⟨262992515934202541819658881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175328343956135027879772587 262992515934202541819658881)
  ·
    refine ⟨197244386950651906364744161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262992515934202541819658881 197244386950651906364744161)
    ·
      refine ⟨147933290212988929773558121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197244386950651906364744161 147933290212988929773558121)
      ·
        refine ⟨110949967659741697330168591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147933290212988929773558121 110949967659741697330168591)
        ·
          refine ⟨166424951489612545995252887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110949967659741697330168591 166424951489612545995252887)
          ·
            refine ⟨249637427234418818992879331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166424951489612545995252887 249637427234418818992879331)
            ·
              refine ⟨374456140851628228489318997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249637427234418818992879331 374456140851628228489318997)
              ·
                refine ⟨4388157900605018302609207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 374456140851628228489318997 4388157900605018302609207)
                ·
                  refine ⟨6582236850907527453913811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388157900605018302609207 6582236850907527453913811)
                  ·
                    refine ⟨9873355276361291180870717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6582236850907527453913811 9873355276361291180870717)
                    ·
                      refine ⟨3702508228635484192826519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9873355276361291180870717 3702508228635484192826519)
                      ·
                        rfl

theorem cell23_7210609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_7210609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210609 prefixEnd_7210609 := by exact prefixLift 7210609
  have htrace : WordTrace (prefixWord ++ tailWord_7210609) baseStart_7210609 baseEnd_7210609 := by
    simpa [prefixWord, tailWord_7210609, baseEnd_7210609] using wordTrace_append hprefix tailTrace_7210609
  have hstable : (prefixWord ++ tailWord_7210609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210609).length < 2 ^ (prefixWord ++ tailWord_7210609).sum := by decide
  have hdescent : baseEnd_7210609 < baseStart_7210609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210615 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_7210615 : Nat := 118140960795 + 7210615 * 2 ^ 59
def prefixEnd_7210615 : Nat := 4983230072969 + 3 ^ 40 * 7210615 * 2
def baseEnd_7210615 : Nat := 3702511309519411169351491

theorem tailTrace_7210615 : CollatzResearch.WordTrace tailWord_7210615 prefixEnd_7210615 3702511309519411169351491 := by
  unfold tailWord_7210615
  simp only [CollatzResearch.WordTrace]
  refine ⟨262992734772180804844377299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175328489848120536562918199 262992734772180804844377299)
  ·
    refine ⟨394489102158271207266565949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262992734772180804844377299 394489102158271207266565949)
    ·
      refine ⟨147933413309351702724962231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394489102158271207266565949 147933413309351702724962231)
      ·
        refine ⟨221900119964027554087443347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147933413309351702724962231 221900119964027554087443347)
        ·
          refine ⟨332850179946041331131165021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221900119964027554087443347 332850179946041331131165021)
          ·
            refine ⟨124818817479765499174186883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332850179946041331131165021 124818817479765499174186883)
            ·
              refine ⟨187228226219648248761280325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124818817479765499174186883 187228226219648248761280325)
              ·
                refine ⟨35105292416184046642740061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187228226219648248761280325 35105292416184046642740061)
                ·
                  refine ⟨13164484656069017491027523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35105292416184046642740061 13164484656069017491027523)
                  ·
                    refine ⟨19746726984103526236541285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13164484656069017491027523 19746726984103526236541285)
                    ·
                      refine ⟨3702511309519411169351491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19746726984103526236541285 3702511309519411169351491)
                      ·
                        rfl

theorem cell23_7210615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_7210615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210615 prefixEnd_7210615 := by exact prefixLift 7210615
  have htrace : WordTrace (prefixWord ++ tailWord_7210615) baseStart_7210615 baseEnd_7210615 := by
    simpa [prefixWord, tailWord_7210615, baseEnd_7210615] using wordTrace_append hprefix tailTrace_7210615
  have hstable : (prefixWord ++ tailWord_7210615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210615).length < 2 ^ (prefixWord ++ tailWord_7210615).sum := by decide
  have hdescent : baseEnd_7210615 < baseStart_7210615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210655 : List Nat := [1, 1, 2, 7, 12]
def baseStart_7210655 : Nat := 118140960795 + 7210655 * 2 ^ 59
def prefixEnd_7210655 : Nat := 4983230072969 + 3 ^ 40 * 7210655 * 2
def baseEnd_7210655 : Nat := 5078918859733321005283

theorem tailTrace_7210655 : CollatzResearch.WordTrace tailWord_7210655 prefixEnd_7210655 5078918859733321005283 := by
  unfold tailWord_7210655
  simp only [CollatzResearch.WordTrace]
  refine ⟨262994193692035891675833419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175329462461357261117222279 262994193692035891675833419)
  ·
    refine ⟨394491290538053837513750129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262994193692035891675833419 394491290538053837513750129)
    ·
      refine ⟨295868467903540378135312597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394491290538053837513750129 295868467903540378135312597)
      ·
        refine ⟨6934417216489227612546389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 295868467903540378135312597 6934417216489227612546389)
        ·
          refine ⟨5078918859733321005283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6934417216489227612546389 5078918859733321005283)
          ·
            rfl

theorem cell23_7210655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 12].length) (baseStart_7210655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210655 prefixEnd_7210655 := by exact prefixLift 7210655
  have htrace : WordTrace (prefixWord ++ tailWord_7210655) baseStart_7210655 baseEnd_7210655 := by
    simpa [prefixWord, tailWord_7210655, baseEnd_7210655] using wordTrace_append hprefix tailTrace_7210655
  have hstable : (prefixWord ++ tailWord_7210655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210655).length < 2 ^ (prefixWord ++ tailWord_7210655).sum := by decide
  have hdescent : baseEnd_7210655 < baseStart_7210655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210682 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3]
def baseStart_7210682 : Nat := 118140960795 + 7210682 * 2 ^ 59
def prefixEnd_7210682 : Nat := 4983230072969 + 3 ^ 40 * 7210682 * 2
def baseEnd_7210682 : Nat := 3702545712723262407213683

theorem tailTrace_7210682 : CollatzResearch.WordTrace tailWord_7210682 prefixEnd_7210682 3702545712723262407213683 := by
  unfold tailWord_7210682
  simp only [CollatzResearch.WordTrace]
  refine ⟨65748794615734518821766575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175330118975292050191377533 65748794615734518821766575)
  ·
    refine ⟨98623191923601778232649863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65748794615734518821766575 98623191923601778232649863)
    ·
      refine ⟨147934787885402667348974795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98623191923601778232649863 147934787885402667348974795)
      ·
        refine ⟨221902181828104001023462193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147934787885402667348974795 221902181828104001023462193)
        ·
          refine ⟨166426636371078000767596645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221902181828104001023462193 166426636371078000767596645)
          ·
            refine ⟨31204994319577125143924371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166426636371078000767596645 31204994319577125143924371)
            ·
              refine ⟨46807491479365687715886557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31204994319577125143924371 46807491479365687715886557)
              ·
                refine ⟨17552809304762132893457459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46807491479365687715886557 17552809304762132893457459)
                ·
                  refine ⟨26329213957143199340186189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17552809304762132893457459 26329213957143199340186189)
                  ·
                    refine ⟨9873455233928699752569821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26329213957143199340186189 9873455233928699752569821)
                    ·
                      refine ⟨3702545712723262407213683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9873455233928699752569821 3702545712723262407213683)
                      ·
                        rfl

theorem cell23_7210682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_7210682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210682 prefixEnd_7210682 := by exact prefixLift 7210682
  have htrace : WordTrace (prefixWord ++ tailWord_7210682) baseStart_7210682 baseEnd_7210682 := by
    simpa [prefixWord, tailWord_7210682, baseEnd_7210682] using wordTrace_append hprefix tailTrace_7210682
  have hstable : (prefixWord ++ tailWord_7210682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210682).length < 2 ^ (prefixWord ++ tailWord_7210682).sum := by decide
  have hdescent : baseEnd_7210682 < baseStart_7210682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210685 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_7210685 : Nat := 118140960795 + 7210685 * 2 ^ 59
def prefixEnd_7210685 : Nat := 4983230072969 + 3 ^ 40 * 7210685 * 2
def baseEnd_7210685 : Nat := 1234182417721741965158723

theorem tailTrace_7210685 : CollatzResearch.WordTrace tailWord_7210685 prefixEnd_7210685 1234182417721741965158723 := by
  unfold tailWord_7210685
  simp only [CollatzResearch.WordTrace]
  refine ⟨262995287881927206799425509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175330191921284804532950339 262995287881927206799425509)
  ·
    refine ⟨49311616477861351274892283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262995287881927206799425509 49311616477861351274892283)
    ·
      refine ⟨73967424716792026912338425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49311616477861351274892283 73967424716792026912338425)
      ·
        refine ⟨55475568537594020184253819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73967424716792026912338425 55475568537594020184253819)
        ·
          refine ⟨83213352806391030276380729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55475568537594020184253819 83213352806391030276380729)
          ·
            refine ⟨62410014604793272707285547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83213352806391030276380729 62410014604793272707285547)
            ·
              refine ⟨93615021907189909060928321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62410014604793272707285547 93615021907189909060928321)
              ·
                refine ⟨70211266430392431795696241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93615021907189909060928321 70211266430392431795696241)
                ·
                  refine ⟨52658449822794323846772181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70211266430392431795696241 52658449822794323846772181)
                  ·
                    refine ⟨1234182417721741965158723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52658449822794323846772181 1234182417721741965158723)
                    ·
                      rfl

theorem cell23_7210685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_7210685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210685 prefixEnd_7210685 := by exact prefixLift 7210685
  have htrace : WordTrace (prefixWord ++ tailWord_7210685) baseStart_7210685 baseEnd_7210685 := by
    simpa [prefixWord, tailWord_7210685, baseEnd_7210685] using wordTrace_append hprefix tailTrace_7210685
  have hstable : (prefixWord ++ tailWord_7210685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210685).length < 2 ^ (prefixWord ++ tailWord_7210685).sum := by decide
  have hdescent : baseEnd_7210685 < baseStart_7210685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210695 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_7210695 : Nat := 118140960795 + 7210695 * 2 ^ 59
def prefixEnd_7210695 : Nat := 4983230072969 + 3 ^ 40 * 7210695 * 2
def baseEnd_7210695 : Nat := 3702552387971770856351123

theorem tailTrace_7210695 : CollatzResearch.WordTrace tailWord_7210695 prefixEnd_7210695 3702552387971770856351123 := by
  unfold tailWord_7210695
  simp only [CollatzResearch.WordTrace]
  refine ⟨262995652611890978507289539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175330435074593985671526359 262995652611890978507289539)
  ·
    refine ⟨394493478917836467760934309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262995652611890978507289539 394493478917836467760934309)
    ·
      refine ⟨73967527297094337705175183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394493478917836467760934309 73967527297094337705175183)
      ·
        refine ⟨110951290945641506557762775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73967527297094337705175183 110951290945641506557762775)
        ·
          refine ⟨166426936418462259836644163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110951290945641506557762775 166426936418462259836644163)
          ·
            refine ⟨249640404627693389754966245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166426936418462259836644163 249640404627693389754966245)
            ·
              refine ⟨46807575867692510579056171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249640404627693389754966245 46807575867692510579056171)
              ·
                refine ⟨70211363801538765868584257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46807575867692510579056171 70211363801538765868584257)
                ·
                  refine ⟨52658522851154074401438193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70211363801538765868584257 52658522851154074401438193)
                  ·
                    refine ⟨39493892138365555801078645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52658522851154074401438193 39493892138365555801078645)
                    ·
                      refine ⟨3702552387971770856351123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39493892138365555801078645 3702552387971770856351123)
                      ·
                        rfl

theorem cell23_7210695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_7210695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210695 prefixEnd_7210695 := by exact prefixLift 7210695
  have htrace : WordTrace (prefixWord ++ tailWord_7210695) baseStart_7210695 baseEnd_7210695 := by
    simpa [prefixWord, tailWord_7210695, baseEnd_7210695] using wordTrace_append hprefix tailTrace_7210695
  have hstable : (prefixWord ++ tailWord_7210695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210695).length < 2 ^ (prefixWord ++ tailWord_7210695).sum := by decide
  have hdescent : baseEnd_7210695 < baseStart_7210695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210700 : List Nat := [2, 2, 1, 5, 2, 1, 2, 3, 1, 2, 2]
def baseStart_7210700 : Nat := 118140960795 + 7210700 * 2 ^ 59
def prefixEnd_7210700 : Nat := 4983230072969 + 3 ^ 40 * 7210700 * 2
def baseEnd_7210700 : Nat := 3702554955375043336788601

theorem tailTrace_7210700 : CollatzResearch.WordTrace tailWord_7210700 prefixEnd_7210700 3702554955375043336788601 := by
  unfold tailWord_7210700
  simp only [CollatzResearch.WordTrace]
  refine ⟨131497917488436432180610777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175330556651248576240814369 131497917488436432180610777)
  ·
    refine ⟨98623438116327324135458083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131497917488436432180610777 98623438116327324135458083)
    ·
      refine ⟨147935157174490986203187125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98623438116327324135458083 147935157174490986203187125)
      ·
        refine ⟨13868920985108529956548793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147935157174490986203187125 13868920985108529956548793)
        ·
          refine ⟨10401690738831397467411595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13868920985108529956548793 10401690738831397467411595)
          ·
            refine ⟨15602536108247096201117393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10401690738831397467411595 15602536108247096201117393)
            ·
              refine ⟨11701902081185322150838045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15602536108247096201117393 11701902081185322150838045)
              ·
                refine ⟨4388213280444495806564267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11701902081185322150838045 4388213280444495806564267)
                ·
                  refine ⟨6582319920666743709846401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388213280444495806564267 6582319920666743709846401)
                  ·
                    refine ⟨4936739940500057782384801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6582319920666743709846401 4936739940500057782384801)
                    ·
                      refine ⟨3702554955375043336788601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936739940500057782384801 3702554955375043336788601)
                      ·
                        rfl

theorem cell23_7210700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_7210700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210700 prefixEnd_7210700 := by exact prefixLift 7210700
  have htrace : WordTrace (prefixWord ++ tailWord_7210700) baseStart_7210700 baseEnd_7210700 := by
    simpa [prefixWord, tailWord_7210700, baseEnd_7210700] using wordTrace_append hprefix tailTrace_7210700
  have hstable : (prefixWord ++ tailWord_7210700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210700).length < 2 ^ (prefixWord ++ tailWord_7210700).sum := by decide
  have hdescent : baseEnd_7210700 < baseStart_7210700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210710 : List Nat := [5, 2, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_7210710 : Nat := 118140960795 + 7210710 * 2 ^ 59
def prefixEnd_7210710 : Nat := 4983230072969 + 3 ^ 40 * 7210710 * 2
def baseEnd_7210710 : Nat := 1234186696727196099221185

theorem tailTrace_7210710 : CollatzResearch.WordTrace tailWord_7210710 prefixEnd_7210710 1234186696727196099221185 := by
  unfold tailWord_7210710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16437262481677289754317849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175330799804557757379390389 16437262481677289754317849)
  ·
    refine ⟨12327946861257967315738387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16437262481677289754317849 12327946861257967315738387)
    ·
      refine ⟨18491920291886950973607581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12327946861257967315738387 18491920291886950973607581)
      ·
        refine ⟨6934470109457606615102843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18491920291886950973607581 6934470109457606615102843)
        ·
          refine ⟨10401705164186409922654265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6934470109457606615102843 10401705164186409922654265)
          ·
            refine ⟨7801278873139807441990699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10401705164186409922654265 7801278873139807441990699)
            ·
              refine ⟨11701918309709711162986049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7801278873139807441990699 11701918309709711162986049)
              ·
                refine ⟨8776438732282283372239537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11701918309709711162986049 8776438732282283372239537)
                ·
                  refine ⟨6582329049211712529179653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8776438732282283372239537 6582329049211712529179653)
                  ·
                    refine ⟨1234186696727196099221185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6582329049211712529179653 1234186696727196099221185)
                    ·
                      rfl

theorem cell23_7210710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_7210710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210710 prefixEnd_7210710 := by exact prefixLift 7210710
  have htrace : WordTrace (prefixWord ++ tailWord_7210710) baseStart_7210710 baseEnd_7210710 := by
    simpa [prefixWord, tailWord_7210710, baseEnd_7210710] using wordTrace_append hprefix tailTrace_7210710
  have hstable : (prefixWord ++ tailWord_7210710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210710).length < 2 ^ (prefixWord ++ tailWord_7210710).sum := by decide
  have hdescent : baseEnd_7210710 < baseStart_7210710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210733 : List Nat := [1, 5, 1, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_7210733 : Nat := 118140960795 + 7210733 * 2 ^ 59
def prefixEnd_7210733 : Nat := 4983230072969 + 3 ^ 40 * 7210733 * 2
def baseEnd_7210733 : Nat := 3702571900236641707675949

theorem tailTrace_7210733 : CollatzResearch.WordTrace tailWord_7210733 prefixEnd_7210733 3702571900236641707675949 := by
  unfold tailWord_7210733
  simp only [CollatzResearch.WordTrace]
  refine ⟨262997038585753310997172853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175331359057168873998115235 262997038585753310997172853)
  ·
    refine ⟨24655972367414372905984955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262997038585753310997172853 24655972367414372905984955)
    ·
      refine ⟨36983958551121559358977433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24655972367414372905984955 36983958551121559358977433)
      ·
        refine ⟨27737968913341169519233075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36983958551121559358977433 27737968913341169519233075)
        ·
          refine ⟨41606953370011754278849613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27737968913341169519233075 41606953370011754278849613)
          ·
            refine ⟨15602607513754407854568605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41606953370011754278849613 15602607513754407854568605)
            ·
              refine ⟨5850977817657902945463227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15602607513754407854568605 5850977817657902945463227)
              ·
                refine ⟨8776466726486854418194841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5850977817657902945463227 8776466726486854418194841)
                ·
                  refine ⟨6582350044865140813646131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8776466726486854418194841 6582350044865140813646131)
                  ·
                    refine ⟨9873525067297711220469197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6582350044865140813646131 9873525067297711220469197)
                    ·
                      refine ⟨3702571900236641707675949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9873525067297711220469197 3702571900236641707675949)
                      ·
                        rfl

theorem cell23_7210733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_7210733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210733 prefixEnd_7210733 := by exact prefixLift 7210733
  have htrace : WordTrace (prefixWord ++ tailWord_7210733) baseStart_7210733 baseEnd_7210733 := by
    simpa [prefixWord, tailWord_7210733, baseEnd_7210733] using wordTrace_append hprefix tailTrace_7210733
  have hstable : (prefixWord ++ tailWord_7210733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210733).length < 2 ^ (prefixWord ++ tailWord_7210733).sum := by decide
  have hdescent : baseEnd_7210733 < baseStart_7210733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210739 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 1, 4, 2]
def baseStart_7210739 : Nat := 118140960795 + 7210739 * 2 ^ 59
def prefixEnd_7210739 : Nat := 4983230072969 + 3 ^ 40 * 7210739 * 2
def baseEnd_7210739 : Nat := 3702574981120568684200921

theorem tailTrace_7210739 : CollatzResearch.WordTrace tailWord_7210739 prefixEnd_7210739 3702574981120568684200921 := by
  unfold tailWord_7210739
  simp only [CollatzResearch.WordTrace]
  refine ⟨262997257423731574021891271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175331504949154382681260847 262997257423731574021891271)
  ·
    refine ⟨394495886135597361032836907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262997257423731574021891271 394495886135597361032836907)
    ·
      refine ⟨591743829203396041549255361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394495886135597361032836907 591743829203396041549255361)
      ·
        refine ⟨443807871902547031161941521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591743829203396041549255361 443807871902547031161941521)
        ·
          refine ⟨332855903926910273371456141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443807871902547031161941521 332855903926910273371456141)
          ·
            refine ⟨124820963972591352514296053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332855903926910273371456141 124820963972591352514296053)
            ·
              refine ⟨11701965372430439298215255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124820963972591352514296053 11701965372430439298215255)
              ·
                refine ⟨17552948058645658947322883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11701965372430439298215255 17552948058645658947322883)
                ·
                  refine ⟨26329422087968488420984325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17552948058645658947322883 26329422087968488420984325)
                  ·
                    refine ⟨4936766641494091578934561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26329422087968488420984325 4936766641494091578934561)
                    ·
                      refine ⟨3702574981120568684200921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936766641494091578934561 3702574981120568684200921)
                      ·
                        rfl

theorem cell23_7210739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 4, 2].length) (baseStart_7210739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210739 prefixEnd_7210739 := by exact prefixLift 7210739
  have htrace : WordTrace (prefixWord ++ tailWord_7210739) baseStart_7210739 baseEnd_7210739 := by
    simpa [prefixWord, tailWord_7210739, baseEnd_7210739] using wordTrace_append hprefix tailTrace_7210739
  have hstable : (prefixWord ++ tailWord_7210739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210739).length < 2 ^ (prefixWord ++ tailWord_7210739).sum := by decide
  have hdescent : baseEnd_7210739 < baseStart_7210739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210756 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_7210756 : Nat := 118140960795 + 7210756 * 2 ^ 59
def prefixEnd_7210756 : Nat := 4983230072969 + 3 ^ 40 * 7210756 * 2
def baseEnd_7210756 : Nat := 3702583710291695117688343

theorem tailTrace_7210756 : CollatzResearch.WordTrace tailWord_7210756 prefixEnd_7210756 3702583710291695117688343 := by
  unfold tailWord_7210756
  simp only [CollatzResearch.WordTrace]
  refine ⟨131498938732334992962630061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175331918309779990616840081 131498938732334992962630061)
  ·
    refine ⟨49312102024625622360986273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131498938732334992962630061 49312102024625622360986273)
    ·
      refine ⟨36984076518469216770739705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49312102024625622360986273 36984076518469216770739705)
      ·
        refine ⟨27738057388851912578054779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36984076518469216770739705 27738057388851912578054779)
        ·
          refine ⟨41607086083277868867082169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27738057388851912578054779 41607086083277868867082169)
          ·
            refine ⟨31205314562458401650311627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41607086083277868867082169 31205314562458401650311627)
            ·
              refine ⟨46807971843687602475467441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31205314562458401650311627 46807971843687602475467441)
              ·
                refine ⟨35105978882765701856600581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46807971843687602475467441 35105978882765701856600581)
                ·
                  refine ⟨6582371040518569098112609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35105978882765701856600581 6582371040518569098112609)
                  ·
                    refine ⟨4936778280388926823584457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6582371040518569098112609 4936778280388926823584457)
                    ·
                      refine ⟨3702583710291695117688343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936778280388926823584457 3702583710291695117688343)
                      ·
                        rfl

theorem cell23_7210756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_7210756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210756 prefixEnd_7210756 := by exact prefixLift 7210756
  have htrace : WordTrace (prefixWord ++ tailWord_7210756) baseStart_7210756 baseEnd_7210756 := by
    simpa [prefixWord, tailWord_7210756, baseEnd_7210756] using wordTrace_append hprefix tailTrace_7210756
  have hstable : (prefixWord ++ tailWord_7210756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210756).length < 2 ^ (prefixWord ++ tailWord_7210756).sum := by decide
  have hdescent : baseEnd_7210756 < baseStart_7210756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210759 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_7210759 : Nat := 118140960795 + 7210759 * 2 ^ 59
def prefixEnd_7210759 : Nat := 4983230072969 + 3 ^ 40 * 7210759 * 2
def baseEnd_7210759 : Nat := 3702585250733658605950829

theorem tailTrace_7210759 : CollatzResearch.WordTrace tailWord_7210759 prefixEnd_7210759 3702585250733658605950829 := by
  unfold tailWord_7210759
  simp only [CollatzResearch.WordTrace]
  refine ⟨262997986883659117437619331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175331991255772744958412887 262997986883659117437619331)
  ·
    refine ⟨394496980325488676156428997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262997986883659117437619331 394496980325488676156428997)
    ·
      refine ⟨73968183811029126779330437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394496980325488676156428997 73968183811029126779330437)
      ·
        refine ⟨13869034464567961271124457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73968183811029126779330437 13869034464567961271124457)
        ·
          refine ⟨10401775848425970953343343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13869034464567961271124457 10401775848425970953343343)
          ·
            refine ⟨15602663772638956430015015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10401775848425970953343343 15602663772638956430015015)
            ·
              refine ⟨23403995658958434645022523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15602663772638956430015015 23403995658958434645022523)
              ·
                refine ⟨35105993488437651967533785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23403995658958434645022523 35105993488437651967533785)
                ·
                  refine ⟨26329495116328238975650339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35105993488437651967533785 26329495116328238975650339)
                  ·
                    refine ⟨39494242674492358463475509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26329495116328238975650339 39494242674492358463475509)
                    ·
                      refine ⟨3702585250733658605950829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39494242674492358463475509 3702585250733658605950829)
                      ·
                        rfl

theorem cell23_7210759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_7210759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210759 prefixEnd_7210759 := by exact prefixLift 7210759
  have htrace : WordTrace (prefixWord ++ tailWord_7210759) baseStart_7210759 baseEnd_7210759 := by
    simpa [prefixWord, tailWord_7210759, baseEnd_7210759] using wordTrace_append hprefix tailTrace_7210759
  have hstable : (prefixWord ++ tailWord_7210759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210759).length < 2 ^ (prefixWord ++ tailWord_7210759).sum := by decide
  have hdescent : baseEnd_7210759 < baseStart_7210759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210812 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_7210812 : Nat := 118140960795 + 7210812 * 2 ^ 59
def prefixEnd_7210812 : Nat := 4983230072969 + 3 ^ 40 * 7210812 * 2
def baseEnd_7210812 : Nat := 3702612465208346898588085

theorem tailTrace_7210812 : CollatzResearch.WordTrace tailWord_7210812 prefixEnd_7210812 3702612465208346898588085 := by
  unfold tailWord_7210812
  simp only [CollatzResearch.WordTrace]
  refine ⟨131499959976233553744649345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175333279968311404992865793 131499959976233553744649345)
  ·
    refine ⟨98624969982175165308487009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131499959976233553744649345 98624969982175165308487009)
    ·
      refine ⟨73968727486631373981365257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98624969982175165308487009 73968727486631373981365257)
      ·
        refine ⟨55476545614973530486023943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73968727486631373981365257 55476545614973530486023943)
        ·
          refine ⟨83214818422460295729035915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55476545614973530486023943 83214818422460295729035915)
          ·
            refine ⟨124822227633690443593553873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83214818422460295729035915 124822227633690443593553873)
            ·
              refine ⟨93616670725267832695165405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124822227633690443593553873 93616670725267832695165405)
              ·
                refine ⟨35106251521975437260687027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93616670725267832695165405 35106251521975437260687027)
                ·
                  refine ⟨52659377282963155891030541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35106251521975437260687027 52659377282963155891030541)
                  ·
                    refine ⟨19747266481111183459136453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52659377282963155891030541 19747266481111183459136453)
                    ·
                      refine ⟨3702612465208346898588085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19747266481111183459136453 3702612465208346898588085)
                      ·
                        rfl

theorem cell23_7210812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_7210812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210812 prefixEnd_7210812 := by exact prefixLift 7210812
  have htrace : WordTrace (prefixWord ++ tailWord_7210812) baseStart_7210812 baseEnd_7210812 := by
    simpa [prefixWord, tailWord_7210812, baseEnd_7210812] using wordTrace_append hprefix tailTrace_7210812
  have hstable : (prefixWord ++ tailWord_7210812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210812).length < 2 ^ (prefixWord ++ tailWord_7210812).sum := by decide
  have hdescent : baseEnd_7210812 < baseStart_7210812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210832 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 3]
def baseStart_7210832 : Nat := 118140960795 + 7210832 * 2 ^ 59
def prefixEnd_7210832 : Nat := 4983230072969 + 3 ^ 40 * 7210832 * 2
def baseEnd_7210832 : Nat := 3702622734821436820337993

theorem tailTrace_7210832 : CollatzResearch.WordTrace tailWord_7210832 prefixEnd_7210832 3702622734821436820337993 := by
  unfold tailWord_7210832
  simp only [CollatzResearch.WordTrace]
  refine ⟨131500324706197325452513375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175333766274929767270017833 131500324706197325452513375)
  ·
    refine ⟨197250487059295988178770063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131500324706197325452513375 197250487059295988178770063)
    ·
      refine ⟨295875730588943982268155095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197250487059295988178770063 295875730588943982268155095)
      ·
        refine ⟨443813595883415973402232643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295875730588943982268155095 443813595883415973402232643)
        ·
          refine ⟨665720393825123960103348965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443813595883415973402232643 665720393825123960103348965)
          ·
            refine ⟨124822573842210742519377931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 665720393825123960103348965 124822573842210742519377931)
            ·
              refine ⟨187233860763316113779066897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124822573842210742519377931 187233860763316113779066897)
              ·
                refine ⟨140425395572487085334300173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187233860763316113779066897 140425395572487085334300173)
                ·
                  refine ⟨52659523339682657000362565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140425395572487085334300173 52659523339682657000362565)
                  ·
                    refine ⟨9873660626190498187567981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52659523339682657000362565 9873660626190498187567981)
                    ·
                      refine ⟨3702622734821436820337993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9873660626190498187567981 3702622734821436820337993)
                      ·
                        rfl

theorem cell23_7210832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 3].length) (baseStart_7210832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210832 prefixEnd_7210832 := by exact prefixLift 7210832
  have htrace : WordTrace (prefixWord ++ tailWord_7210832) baseStart_7210832 baseEnd_7210832 := by
    simpa [prefixWord, tailWord_7210832, baseEnd_7210832] using wordTrace_append hprefix tailTrace_7210832
  have hstable : (prefixWord ++ tailWord_7210832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210832).length < 2 ^ (prefixWord ++ tailWord_7210832).sum := by decide
  have hdescent : baseEnd_7210832 < baseStart_7210832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210879 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 7, 1, 3]
def baseStart_7210879 : Nat := 118140960795 + 7210879 * 2 ^ 59
def prefixEnd_7210879 : Nat := 4983230072969 + 3 ^ 40 * 7210879 * 2
def baseEnd_7210879 : Nat := 3702646868412198136450277

theorem tailTrace_7210879 : CollatzResearch.WordTrace tailWord_7210879 prefixEnd_7210879 3702646868412198136450277 := by
  unfold tailWord_7210879
  simp only [CollatzResearch.WordTrace]
  refine ⟨263002363643224377931987691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175334909095482918621325127 263002363643224377931987691)
  ·
    refine ⟨394503545464836566897981537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263002363643224377931987691 394503545464836566897981537)
    ·
      refine ⟨295877659098627425173486153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394503545464836566897981537 295877659098627425173486153)
      ·
        refine ⟨221908244323970568880114615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295877659098627425173486153 221908244323970568880114615)
        ·
          refine ⟨332862366485955853320171923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221908244323970568880114615 332862366485955853320171923)
          ·
            refine ⟨499293549728933779980257885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332862366485955853320171923 499293549728933779980257885)
            ·
              refine ⟨187235081148350167492596707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499293549728933779980257885 187235081148350167492596707)
              ·
                refine ⟨280852621722525251238895061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187235081148350167492596707 280852621722525251238895061)
                ·
                  refine ⟨6582483321621685575911603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 280852621722525251238895061 6582483321621685575911603)
                  ·
                    refine ⟨9873724982432528363867405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6582483321621685575911603 9873724982432528363867405)
                    ·
                      refine ⟨3702646868412198136450277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9873724982432528363867405 3702646868412198136450277)
                      ·
                        rfl

theorem cell23_7210879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_7210879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210879 prefixEnd_7210879 := by exact prefixLift 7210879
  have htrace : WordTrace (prefixWord ++ tailWord_7210879) baseStart_7210879 baseEnd_7210879 := by
    simpa [prefixWord, tailWord_7210879, baseEnd_7210879] using wordTrace_append hprefix tailTrace_7210879
  have hstable : (prefixWord ++ tailWord_7210879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210879).length < 2 ^ (prefixWord ++ tailWord_7210879).sum := by decide
  have hdescent : baseEnd_7210879 < baseStart_7210879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210906 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2]
def baseStart_7210906 : Nat := 118140960795 + 7210906 * 2 ^ 59
def prefixEnd_7210906 : Nat := 4983230072969 + 3 ^ 40 * 7210906 * 2
def baseEnd_7210906 : Nat := 3702660732389869530812653

theorem tailTrace_7210906 : CollatzResearch.WordTrace tailWord_7210906 prefixEnd_7210906 3702660732389869530812653 := by
  unfold tailWord_7210906
  simp only [CollatzResearch.WordTrace]
  refine ⟨65750837103531640385805143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175335565609417707695480381 65750837103531640385805143)
  ·
    refine ⟨98626255655297460578707715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65750837103531640385805143 98626255655297460578707715)
    ·
      refine ⟨147939383482946190868061573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98626255655297460578707715 147939383482946190868061573)
      ·
        refine ⟨27738634403052410787761545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147939383482946190868061573 27738634403052410787761545)
        ·
          refine ⟨20803975802289308090821159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27738634403052410787761545 20803975802289308090821159)
          ·
            refine ⟨31205963703433962136231739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20803975802289308090821159 31205963703433962136231739)
            ·
              refine ⟨46808945555150943204347609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31205963703433962136231739 46808945555150943204347609)
              ·
                refine ⟨35106709166363207403260707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46808945555150943204347609 35106709166363207403260707)
                ·
                  refine ⟨52660063749544811104891061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35106709166363207403260707 52660063749544811104891061)
                  ·
                    refine ⟨4936880976519826041083537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52660063749544811104891061 4936880976519826041083537)
                    ·
                      refine ⟨3702660732389869530812653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936880976519826041083537 3702660732389869530812653)
                      ·
                        rfl

theorem cell23_7210906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_7210906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210906 prefixEnd_7210906 := by exact prefixLift 7210906
  have htrace : WordTrace (prefixWord ++ tailWord_7210906) baseStart_7210906 baseEnd_7210906 := by
    simpa [prefixWord, tailWord_7210906, baseEnd_7210906] using wordTrace_append hprefix tailTrace_7210906
  have hstable : (prefixWord ++ tailWord_7210906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210906).length < 2 ^ (prefixWord ++ tailWord_7210906).sum := by decide
  have hdescent : baseEnd_7210906 < baseStart_7210906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210916 : List Nat := [2, 3, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_7210916 : Nat := 118140960795 + 7210916 * 2 ^ 59
def prefixEnd_7210916 : Nat := 4983230072969 + 3 ^ 40 * 7210916 * 2
def baseEnd_7210916 : Nat := 1234221955732138163895869

theorem tailTrace_7210916 : CollatzResearch.WordTrace tailWord_7210916 prefixEnd_7210916 1234221955732138163895869 := by
  unfold tailWord_7210916
  simp only [CollatzResearch.WordTrace]
  refine ⟨131501856572045166625542301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175335808762726888834056401 131501856572045166625542301)
  ·
    refine ⟨49313196214516937484578363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131501856572045166625542301 49313196214516937484578363)
    ·
      refine ⟨73969794321775406226867545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49313196214516937484578363 73969794321775406226867545)
      ·
        refine ⟨55477345741331554670150659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73969794321775406226867545 55477345741331554670150659)
        ·
          refine ⟨83216018611997332005225989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55477345741331554670150659 83216018611997332005225989)
          ·
            refine ⟨15603003489749499750979873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83216018611997332005225989 15603003489749499750979873)
            ·
              refine ⟨11702252617312124813234905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15603003489749499750979873 11702252617312124813234905)
              ·
                refine ⟨8776689462984093609926179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11702252617312124813234905 8776689462984093609926179)
                ·
                  refine ⟨13165034194476140414889269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8776689462984093609926179 13165034194476140414889269)
                  ·
                    refine ⟨1234221955732138163895869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13165034194476140414889269 1234221955732138163895869)
                    ·
                      rfl

theorem cell23_7210916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_7210916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210916 prefixEnd_7210916 := by exact prefixLift 7210916
  have htrace : WordTrace (prefixWord ++ tailWord_7210916) baseStart_7210916 baseEnd_7210916 := by
    simpa [prefixWord, tailWord_7210916, baseEnd_7210916] using wordTrace_append hprefix tailTrace_7210916
  have hstable : (prefixWord ++ tailWord_7210916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210916).length < 2 ^ (prefixWord ++ tailWord_7210916).sum := by decide
  have hdescent : baseEnd_7210916 < baseStart_7210916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210940 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 2, 3, 2]
def baseStart_7210940 : Nat := 118140960795 + 7210940 * 2 ^ 59
def prefixEnd_7210940 : Nat := 4983230072969 + 3 ^ 40 * 7210940 * 2
def baseEnd_7210940 : Nat := 3702678190732122397787497

theorem tailTrace_7210940 : CollatzResearch.WordTrace tailWord_7210940 prefixEnd_7210940 3702678190732122397787497 := by
  unfold tailWord_7210940
  simp only [CollatzResearch.WordTrace]
  refine ⟨131502294248001692674979137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175336392330668923566638849 131502294248001692674979137)
  ·
    refine ⟨98626720686001269506234353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131502294248001692674979137 98626720686001269506234353)
    ·
      refine ⟨73970040514500952129675765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98626720686001269506234353 73970040514500952129675765)
      ·
        refine ⟨6934691298234464262157103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73970040514500952129675765 6934691298234464262157103)
        ·
          refine ⟨10402036947351696393235655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6934691298234464262157103 10402036947351696393235655)
          ·
            refine ⟨15603055421027544589853483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10402036947351696393235655 15603055421027544589853483)
            ·
              refine ⟨23404583131541316884780225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15603055421027544589853483 23404583131541316884780225)
              ·
                refine ⟨17553437348655987663585169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23404583131541316884780225 17553437348655987663585169)
                ·
                  refine ⟨13165078011491990747688877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17553437348655987663585169 13165078011491990747688877)
                  ·
                    refine ⟨4936904254309496530383329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13165078011491990747688877 4936904254309496530383329)
                    ·
                      refine ⟨3702678190732122397787497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936904254309496530383329 3702678190732122397787497)
                      ·
                        rfl

theorem cell23_7210940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_7210940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210940 prefixEnd_7210940 := by exact prefixLift 7210940
  have htrace : WordTrace (prefixWord ++ tailWord_7210940) baseStart_7210940 baseEnd_7210940 := by
    simpa [prefixWord, tailWord_7210940, baseEnd_7210940] using wordTrace_append hprefix tailTrace_7210940
  have hstable : (prefixWord ++ tailWord_7210940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210940).length < 2 ^ (prefixWord ++ tailWord_7210940).sum := by decide
  have hdescent : baseEnd_7210940 < baseStart_7210940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210970 : List Nat := [3, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4]
def baseStart_7210970 : Nat := 118140960795 + 7210970 * 2 ^ 59
def prefixEnd_7210970 : Nat := 4983230072969 + 3 ^ 40 * 7210970 * 2
def baseEnd_7210970 : Nat := 3702693595151757280412359

theorem tailTrace_7210970 : CollatzResearch.WordTrace tailWord_7210970 prefixEnd_7210970 3702693595151757280412359 := by
  unfold tailWord_7210970
  simp only [CollatzResearch.WordTrace]
  refine ⟨65751420671473675118387591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175337121790596466982366909 65751420671473675118387591)
  ·
    refine ⟨98627131007210512677581387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65751420671473675118387591 98627131007210512677581387)
    ·
      refine ⟨147940696510815769016372081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98627131007210512677581387 147940696510815769016372081)
      ·
        refine ⟨110955522383111826762279061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147940696510815769016372081 110955522383111826762279061)
        ·
          refine ⟨5201040111708366879481831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110955522383111826762279061 5201040111708366879481831)
          ·
            refine ⟨7801560167562550319222747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5201040111708366879481831 7801560167562550319222747)
            ·
              refine ⟨11702340251343825478834121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7801560167562550319222747 11702340251343825478834121)
              ·
                refine ⟨8776755188507869109125591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11702340251343825478834121 8776755188507869109125591)
                ·
                  refine ⟨13165132782761803663688387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8776755188507869109125591 13165132782761803663688387)
                  ·
                    refine ⟨19747699174142705495532581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13165132782761803663688387 19747699174142705495532581)
                    ·
                      refine ⟨3702693595151757280412359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19747699174142705495532581 3702693595151757280412359)
                      ·
                        rfl

theorem cell23_7210970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_7210970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210970 prefixEnd_7210970 := by exact prefixLift 7210970
  have htrace : WordTrace (prefixWord ++ tailWord_7210970) baseStart_7210970 baseEnd_7210970 := by
    simpa [prefixWord, tailWord_7210970, baseEnd_7210970] using wordTrace_append hprefix tailTrace_7210970
  have hstable : (prefixWord ++ tailWord_7210970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210970).length < 2 ^ (prefixWord ++ tailWord_7210970).sum := by decide
  have hdescent : baseEnd_7210970 < baseStart_7210970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210973 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_7210973 : Nat := 118140960795 + 7210973 * 2 ^ 59
def prefixEnd_7210973 : Nat := 4983230072969 + 3 ^ 40 * 7210973 * 2
def baseEnd_7210973 : Nat := 3702695135593720768674845

theorem tailTrace_7210973 : CollatzResearch.WordTrace tailWord_7210973 prefixEnd_7210973 3702695135593720768674845 := by
  unfold tailWord_7210973
  simp only [CollatzResearch.WordTrace]
  refine ⟨263005792104883831985909573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175337194736589221323939715 263005792104883831985909573)
  ·
    refine ⟨49313586019665718497358045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263005792104883831985909573 49313586019665718497358045)
    ·
      refine ⟨18492594757374644436509267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49313586019665718497358045 18492594757374644436509267)
      ·
        refine ⟨27738892136061966654763901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18492594757374644436509267 27738892136061966654763901)
        ·
          refine ⟨10402084551023237495536463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27738892136061966654763901 10402084551023237495536463)
          ·
            refine ⟨15603126826534856243304695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10402084551023237495536463 15603126826534856243304695)
            ·
              refine ⟨23404690239802284364957043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15603126826534856243304695 23404690239802284364957043)
              ·
                refine ⟨35107035359703426547435565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23404690239802284364957043 35107035359703426547435565)
                ·
                  refine ⟨13165138259888784955288337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35107035359703426547435565 13165138259888784955288337)
                  ·
                    refine ⟨9873853694916588716466253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13165138259888784955288337 9873853694916588716466253)
                    ·
                      refine ⟨3702695135593720768674845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9873853694916588716466253 3702695135593720768674845)
                      ·
                        rfl

theorem cell23_7210973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_7210973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210973 prefixEnd_7210973 := by exact prefixLift 7210973
  have htrace : WordTrace (prefixWord ++ tailWord_7210973) baseStart_7210973 baseEnd_7210973 := by
    simpa [prefixWord, tailWord_7210973, baseEnd_7210973] using wordTrace_append hprefix tailTrace_7210973
  have hstable : (prefixWord ++ tailWord_7210973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210973).length < 2 ^ (prefixWord ++ tailWord_7210973).sum := by decide
  have hdescent : baseEnd_7210973 < baseStart_7210973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210986 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_7210986 : Nat := 118140960795 + 7210986 * 2 ^ 59
def prefixEnd_7210986 : Nat := 4983230072969 + 3 ^ 40 * 7210986 * 2
def baseEnd_7210986 : Nat := 3702701810842229217812285

theorem tailTrace_7210986 : CollatzResearch.WordTrace tailWord_7210986 prefixEnd_7210986 3702701810842229217812285 := by
  unfold tailWord_7210986
  simp only [CollatzResearch.WordTrace]
  refine ⟨65751566563459183801533203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175337510835891156804088541 65751566563459183801533203)
  ·
    refine ⟨98627349845188775702299805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65751566563459183801533203 98627349845188775702299805)
    ·
      refine ⟨36985256191945790888362427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98627349845188775702299805 36985256191945790888362427)
      ·
        refine ⟨55477884287918686332543641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36985256191945790888362427 55477884287918686332543641)
        ·
          refine ⟨41608413215939014749407731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55477884287918686332543641 41608413215939014749407731)
          ·
            refine ⟨62412619823908522124111597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41608413215939014749407731 62412619823908522124111597)
            ·
              refine ⟨23404732433965695796541849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62412619823908522124111597 23404732433965695796541849)
              ·
                refine ⟨17553549325474271847406387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23404732433965695796541849 17553549325474271847406387)
                ·
                  refine ⟨26330323988211407771109581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17553549325474271847406387 26330323988211407771109581)
                  ·
                    refine ⟨9873871495579277914166093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26330323988211407771109581 9873871495579277914166093)
                    ·
                      refine ⟨3702701810842229217812285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9873871495579277914166093 3702701810842229217812285)
                      ·
                        rfl

theorem cell23_7210986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_7210986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210986 prefixEnd_7210986 := by exact prefixLift 7210986
  have htrace : WordTrace (prefixWord ++ tailWord_7210986) baseStart_7210986 baseEnd_7210986 := by
    simpa [prefixWord, tailWord_7210986, baseEnd_7210986] using wordTrace_append hprefix tailTrace_7210986
  have hstable : (prefixWord ++ tailWord_7210986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210986).length < 2 ^ (prefixWord ++ tailWord_7210986).sum := by decide
  have hdescent : baseEnd_7210986 < baseStart_7210986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7210990 : List Nat := [4, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_7210990 : Nat := 118140960795 + 7210990 * 2 ^ 59
def prefixEnd_7210990 : Nat := 4983230072969 + 3 ^ 40 * 7210990 * 2
def baseEnd_7210990 : Nat := 3702703864764847202162267

theorem tailTrace_7210990 : CollatzResearch.WordTrace tailWord_7210990 prefixEnd_7210990 3702703864764847202162267 := by
  unfold tailWord_7210990
  simp only [CollatzResearch.WordTrace]
  refine ⟨32875801518227780486159803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175337608097214829259518949 32875801518227780486159803)
  ·
    refine ⟨49313702277341670729239705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32875801518227780486159803 49313702277341670729239705)
    ·
      refine ⟨36985276708006253046929779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49313702277341670729239705 36985276708006253046929779)
      ·
        refine ⟨55477915062009379570394669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36985276708006253046929779 55477915062009379570394669)
        ·
          refine ⟨20804218148253517338898001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55477915062009379570394669 20804218148253517338898001)
          ·
            refine ⟨15603163611190138004173501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20804218148253517338898001 15603163611190138004173501)
            ·
              refine ⟨5851186354196301751565063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15603163611190138004173501 5851186354196301751565063)
              ·
                refine ⟨8776779531294452627347595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5851186354196301751565063 8776779531294452627347595)
                ·
                  refine ⟨13165169296941678941021393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8776779531294452627347595 13165169296941678941021393)
                  ·
                    refine ⟨9873876972706259205766045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13165169296941678941021393 9873876972706259205766045)
                    ·
                      refine ⟨3702703864764847202162267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9873876972706259205766045 3702703864764847202162267)
                      ·
                        rfl

theorem cell23_7210990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_7210990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7210990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7210990 prefixEnd_7210990 := by exact prefixLift 7210990
  have htrace : WordTrace (prefixWord ++ tailWord_7210990) baseStart_7210990 baseEnd_7210990 := by
    simpa [prefixWord, tailWord_7210990, baseEnd_7210990] using wordTrace_append hprefix tailTrace_7210990
  have hstable : (prefixWord ++ tailWord_7210990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7210990).length < 2 ^ (prefixWord ++ tailWord_7210990).sum := by decide
  have hdescent : baseEnd_7210990 < baseStart_7210990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7210990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211006 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_7211006 : Nat := 118140960795 + 7211006 * 2 ^ 59
def prefixEnd_7211006 : Nat := 4983230072969 + 3 ^ 40 * 7211006 * 2
def baseEnd_7211006 : Nat := 1234237360151773046520731

theorem tailTrace_7211006 : CollatzResearch.WordTrace tailWord_7211006 prefixEnd_7211006 1234237360151773046520731 := by
  unfold tailWord_7211006
  simp only [CollatzResearch.WordTrace]
  refine ⟨32875874464220534827732609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175337997142509519081240581 32875874464220534827732609)
  ·
    refine ⟨24656905848165401120799457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32875874464220534827732609 24656905848165401120799457)
    ·
      refine ⟨18492679386124050840599593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24656905848165401120799457 18492679386124050840599593)
      ·
        refine ⟨13869509539593038130449695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18492679386124050840599593 13869509539593038130449695)
        ·
          refine ⟨20804264309389557195674543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13869509539593038130449695 20804264309389557195674543)
          ·
            refine ⟨31206396464084335793511815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20804264309389557195674543 31206396464084335793511815)
            ·
              refine ⟨46809594696126503690267723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31206396464084335793511815 46809594696126503690267723)
              ·
                refine ⟨70214392044189755535401585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46809594696126503690267723 70214392044189755535401585)
                ·
                  refine ⟨52660794033142316651551189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70214392044189755535401585 52660794033142316651551189)
                  ·
                    refine ⟨1234237360151773046520731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52660794033142316651551189 1234237360151773046520731)
                    ·
                      rfl

theorem cell23_7211006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_7211006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211006 prefixEnd_7211006 := by exact prefixLift 7211006
  have htrace : WordTrace (prefixWord ++ tailWord_7211006) baseStart_7211006 baseEnd_7211006 := by
    simpa [prefixWord, tailWord_7211006, baseEnd_7211006] using wordTrace_append hprefix tailTrace_7211006
  have hstable : (prefixWord ++ tailWord_7211006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211006).length < 2 ^ (prefixWord ++ tailWord_7211006).sum := by decide
  have hdescent : baseEnd_7211006 < baseStart_7211006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211009 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_7211009 : Nat := 118140960795 + 7211009 * 2 ^ 59
def prefixEnd_7211009 : Nat := 4983230072969 + 3 ^ 40 * 7211009 * 2
def baseEnd_7211009 : Nat := 3702713620897282627824679

theorem tailTrace_7211009 : CollatzResearch.WordTrace tailWord_7211009 prefixEnd_7211009 3702713620897282627824679 := by
  unfold tailWord_7211009
  simp only [CollatzResearch.WordTrace]
  refine ⟨263007105132753410134220081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175338070088502273422813387 263007105132753410134220081)
  ·
    refine ⟨197255328849565057600665061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263007105132753410134220081 197255328849565057600665061)
    ·
      refine ⟨36985374159293448300124699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197255328849565057600665061 36985374159293448300124699)
      ·
        refine ⟨55478061238940172450187049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36985374159293448300124699 55478061238940172450187049)
        ·
          refine ⟨41608545929205129337640287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55478061238940172450187049 41608545929205129337640287)
          ·
            refine ⟨62412818893807694006460431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41608545929205129337640287 62412818893807694006460431)
            ·
              refine ⟨93619228340711541009690647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62412818893807694006460431 93619228340711541009690647)
              ·
                refine ⟨140428842511067311514535971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93619228340711541009690647 140428842511067311514535971)
                ·
                  refine ⟨210643263766600967271803957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140428842511067311514535971 210643263766600967271803957)
                  ·
                    refine ⟨19747805978118840681731621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 210643263766600967271803957 19747805978118840681731621)
                    ·
                      refine ⟨3702713620897282627824679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19747805978118840681731621 3702713620897282627824679)
                      ·
                        rfl

theorem cell23_7211009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_7211009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211009 prefixEnd_7211009 := by exact prefixLift 7211009
  have htrace : WordTrace (prefixWord ++ tailWord_7211009) baseStart_7211009 baseEnd_7211009 := by
    simpa [prefixWord, tailWord_7211009, baseEnd_7211009] using wordTrace_append hprefix tailTrace_7211009
  have hstable : (prefixWord ++ tailWord_7211009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211009).length < 2 ^ (prefixWord ++ tailWord_7211009).sum := by decide
  have hdescent : baseEnd_7211009 < baseStart_7211009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211019 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 2, 6]
def baseStart_7211019 : Nat := 118140960795 + 7211019 * 2 ^ 59
def prefixEnd_7211019 : Nat := 4983230072969 + 3 ^ 40 * 7211019 * 2
def baseEnd_7211019 : Nat := 1234239585234609196233211

theorem tailTrace_7211019 : CollatzResearch.WordTrace tailWord_7211019 prefixEnd_7211019 1234239585234609196233211 := by
  unfold tailWord_7211019
  simp only [CollatzResearch.WordTrace]
  refine ⟨263007469862717181842084111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175338313241811454561389407 263007469862717181842084111)
  ·
    refine ⟨394511204794075772763126167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263007469862717181842084111 394511204794075772763126167)
    ·
      refine ⟨591766807191113659144689251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394511204794075772763126167 591766807191113659144689251)
      ·
        refine ⟨887650210786670488717033877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591766807191113659144689251 887650210786670488717033877)
        ·
          refine ⟨41608603630625179158610963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 887650210786670488717033877 41608603630625179158610963)
          ·
            refine ⟨62412905445937768737916445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41608603630625179158610963 62412905445937768737916445)
            ·
              refine ⟨23404839542226663276718667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62412905445937768737916445 23404839542226663276718667)
              ·
                refine ⟨35107259313339994915078001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23404839542226663276718667 35107259313339994915078001)
                ·
                  refine ⟨26330444485004996186308501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35107259313339994915078001 26330444485004996186308501)
                  ·
                    refine ⟨1234239585234609196233211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26330444485004996186308501 1234239585234609196233211)
                    ·
                      rfl

theorem cell23_7211019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 6].length) (baseStart_7211019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211019 prefixEnd_7211019 := by exact prefixLift 7211019
  have htrace : WordTrace (prefixWord ++ tailWord_7211019) baseStart_7211019 baseEnd_7211019 := by
    simpa [prefixWord, tailWord_7211019, baseEnd_7211019] using wordTrace_append hprefix tailTrace_7211019
  have hstable : (prefixWord ++ tailWord_7211019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211019).length < 2 ^ (prefixWord ++ tailWord_7211019).sum := by decide
  have hdescent : baseEnd_7211019 < baseStart_7211019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211039 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 4]
def baseStart_7211039 : Nat := 118140960795 + 7211039 * 2 ^ 59
def prefixEnd_7211039 : Nat := 4983230072969 + 3 ^ 40 * 7211039 * 2
def baseEnd_7211039 : Nat := 3702729025316917510449541

theorem tailTrace_7211039 : CollatzResearch.WordTrace tailWord_7211039 prefixEnd_7211039 3702729025316917510449541 := by
  unfold tailWord_7211039
  simp only [CollatzResearch.WordTrace]
  refine ⟨263008199322644725257812171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175338799548429816838541447 263008199322644725257812171)
  ·
    refine ⟨394512298983967087886718257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263008199322644725257812171 394512298983967087886718257)
    ·
      refine ⟨295884224237975315915038693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394512298983967087886718257 295884224237975315915038693)
      ·
        refine ⟨55478292044620371734069755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295884224237975315915038693 55478292044620371734069755)
        ·
          refine ⟨83217438066930557601104633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55478292044620371734069755 83217438066930557601104633)
          ·
            refine ⟨62413078550197918200828475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83217438066930557601104633 62413078550197918200828475)
            ·
              refine ⟨93619617825296877301242713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62413078550197918200828475 93619617825296877301242713)
              ·
                refine ⟨70214713368972657975932035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93619617825296877301242713 70214713368972657975932035)
                ·
                  refine ⟨105322070053458986963898053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70214713368972657975932035 105322070053458986963898053)
                  ·
                    refine ⟨19747888135023560055730885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105322070053458986963898053 19747888135023560055730885)
                    ·
                      refine ⟨3702729025316917510449541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19747888135023560055730885 3702729025316917510449541)
                      ·
                        rfl

theorem cell23_7211039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_7211039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211039 prefixEnd_7211039 := by exact prefixLift 7211039
  have htrace : WordTrace (prefixWord ++ tailWord_7211039) baseStart_7211039 baseEnd_7211039 := by
    simpa [prefixWord, tailWord_7211039, baseEnd_7211039] using wordTrace_append hprefix tailTrace_7211039
  have hstable : (prefixWord ++ tailWord_7211039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211039).length < 2 ^ (prefixWord ++ tailWord_7211039).sum := by decide
  have hdescent : baseEnd_7211039 < baseStart_7211039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211043 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 4, 2, 2]
def baseStart_7211043 : Nat := 118140960795 + 7211043 * 2 ^ 59
def prefixEnd_7211043 : Nat := 4983230072969 + 3 ^ 40 * 7211043 * 2
def baseEnd_7211043 : Nat := 3702731079239535494799523

theorem tailTrace_7211043 : CollatzResearch.WordTrace tailWord_7211043 prefixEnd_7211043 3702731079239535494799523 := by
  unfold tailWord_7211043
  simp only [CollatzResearch.WordTrace]
  refine ⟨263008345214630233940957783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175338896809753489293971855 263008345214630233940957783)
  ·
    refine ⟨394512517821945350911436675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263008345214630233940957783 394512517821945350911436675)
    ·
      refine ⟨591768776732918026367155013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394512517821945350911436675 591768776732918026367155013)
      ·
        refine ⟨110956645637422129943841565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 591768776732918026367155013 110956645637422129943841565)
        ·
          refine ⟨41608742114033298728940587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110956645637422129943841565 41608742114033298728940587)
          ·
            refine ⟨62413113171049948093410881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41608742114033298728940587 62413113171049948093410881)
            ·
              refine ⟨46809834878287461070058161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62413113171049948093410881 46809834878287461070058161)
              ·
                refine ⟨35107376158715595802543621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46809834878287461070058161 35107376158715595802543621)
                ·
                  refine ⟨6582633029759174212976929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35107376158715595802543621 6582633029759174212976929)
                  ·
                    refine ⟨4936974772319380659732697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6582633029759174212976929 4936974772319380659732697)
                    ·
                      refine ⟨3702731079239535494799523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936974772319380659732697 3702731079239535494799523)
                      ·
                        rfl

theorem cell23_7211043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_7211043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211043 prefixEnd_7211043 := by exact prefixLift 7211043
  have htrace : WordTrace (prefixWord ++ tailWord_7211043) baseStart_7211043 baseEnd_7211043 := by
    simpa [prefixWord, tailWord_7211043, baseEnd_7211043] using wordTrace_append hprefix tailTrace_7211043
  have hstable : (prefixWord ++ tailWord_7211043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211043).length < 2 ^ (prefixWord ++ tailWord_7211043).sum := by decide
  have hdescent : baseEnd_7211043 < baseStart_7211043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211047 : List Nat := [1, 1, 7, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_7211047 : Nat := 118140960795 + 7211047 * 2 ^ 59
def prefixEnd_7211047 : Nat := 4983230072969 + 3 ^ 40 * 7211047 * 2
def baseEnd_7211047 : Nat := 3702733133162153479149505

theorem tailTrace_7211047 : CollatzResearch.WordTrace tailWord_7211047 prefixEnd_7211047 3702733133162153479149505 := by
  unfold tailWord_7211047
  simp only [CollatzResearch.WordTrace]
  refine ⟨263008491106615742624103395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175338994071077161749402263 263008491106615742624103395)
  ·
    refine ⟨394512736659923613936155093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263008491106615742624103395 394512736659923613936155093)
    ·
      refine ⟨9246392265466959701628635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 394512736659923613936155093 9246392265466959701628635)
      ·
        refine ⟨13869588398200439552442953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9246392265466959701628635 13869588398200439552442953)
        ·
          refine ⟨10402191298650329664332215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13869588398200439552442953 10402191298650329664332215)
          ·
            refine ⟨15603286947975494496498323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10402191298650329664332215 15603286947975494496498323)
            ·
              refine ⟨23404930421963241744747485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15603286947975494496498323 23404930421963241744747485)
              ·
                refine ⟨8776848908236215654280307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23404930421963241744747485 8776848908236215654280307)
                ·
                  refine ⟨13165273362354323481420461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8776848908236215654280307 13165273362354323481420461)
                  ·
                    refine ⟨4936977510882871305532673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13165273362354323481420461 4936977510882871305532673)
                    ·
                      refine ⟨3702733133162153479149505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4936977510882871305532673 3702733133162153479149505)
                      ·
                        rfl

theorem cell23_7211047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_7211047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211047 prefixEnd_7211047 := by exact prefixLift 7211047
  have htrace : WordTrace (prefixWord ++ tailWord_7211047) baseStart_7211047 baseEnd_7211047 := by
    simpa [prefixWord, tailWord_7211047, baseEnd_7211047] using wordTrace_append hprefix tailTrace_7211047
  have hstable : (prefixWord ++ tailWord_7211047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211047).length < 2 ^ (prefixWord ++ tailWord_7211047).sum := by decide
  have hdescent : baseEnd_7211047 < baseStart_7211047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211079 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 3, 7]
def baseStart_7211079 : Nat := 118140960795 + 7211079 * 2 ^ 59
def prefixEnd_7211079 : Nat := 4983230072969 + 3 ^ 40 * 7211079 * 2
def baseEnd_7211079 : Nat := 1234249854847699117983119

theorem tailTrace_7211079 : CollatzResearch.WordTrace tailWord_7211079 prefixEnd_7211079 1234249854847699117983119 := by
  unfold tailWord_7211079
  simp only [CollatzResearch.WordTrace]
  refine ⟨263009658242499812089268291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175339772161666541392845527 263009658242499812089268291)
  ·
    refine ⟨394514487363749718133902437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263009658242499812089268291 394514487363749718133902437)
    ·
      refine ⟨73971466380703072150106707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 394514487363749718133902437 73971466380703072150106707)
      ·
        refine ⟨110957199571054608225160061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73971466380703072150106707 110957199571054608225160061)
        ·
          refine ⟨41608949839145478084435023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110957199571054608225160061 41608949839145478084435023)
          ·
            refine ⟨62413424758718217126652535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41608949839145478084435023 62413424758718217126652535)
            ·
              refine ⟨93620137138077325689978803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62413424758718217126652535 93620137138077325689978803)
              ·
                refine ⟨140430205707115988534968205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93620137138077325689978803 140430205707115988534968205)
                ·
                  refine ⟨52661327140168495700613077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140430205707115988534968205 52661327140168495700613077)
                  ·
                    refine ⟨1234249854847699117983119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52661327140168495700613077 1234249854847699117983119)
                    ·
                      rfl

theorem cell23_7211079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_7211079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211079 prefixEnd_7211079 := by exact prefixLift 7211079
  have htrace : WordTrace (prefixWord ++ tailWord_7211079) baseStart_7211079 baseEnd_7211079 := by
    simpa [prefixWord, tailWord_7211079, baseEnd_7211079] using wordTrace_append hprefix tailTrace_7211079
  have hstable : (prefixWord ++ tailWord_7211079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211079).length < 2 ^ (prefixWord ++ tailWord_7211079).sum := by decide
  have hdescent : baseEnd_7211079 < baseStart_7211079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211089 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_7211089 : Nat := 118140960795 + 7211089 * 2 ^ 59
def prefixEnd_7211089 : Nat := 4983230072969 + 3 ^ 40 * 7211089 * 2
def baseEnd_7211089 : Nat := 3702754699349642314824311

theorem tailTrace_7211089 : CollatzResearch.WordTrace tailWord_7211089 prefixEnd_7211089 3702754699349642314824311 := by
  unfold tailWord_7211089
  simp only [CollatzResearch.WordTrace]
  refine ⟨263010022972463583797132321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175340015314975722531421547 263010022972463583797132321)
  ·
    refine ⟨197257517229347687847849241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263010022972463583797132321 197257517229347687847849241)
    ·
      refine ⟨147943137922010765885886931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197257517229347687847849241 147943137922010765885886931)
      ·
        refine ⟨221914706883016148828830397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147943137922010765885886931 221914706883016148828830397)
        ·
          refine ⟨83218015081131055810811399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221914706883016148828830397 83218015081131055810811399)
          ·
            refine ⟨124827022621696583716217099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83218015081131055810811399 124827022621696583716217099)
            ·
              refine ⟨187240533932544875574325649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124827022621696583716217099 187240533932544875574325649)
              ·
                refine ⟨140430400449408656680744237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187240533932544875574325649 140430400449408656680744237)
                ·
                  refine ⟨52661400168528246255279089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140430400449408656680744237 52661400168528246255279089)
                  ·
                    refine ⟨39496050126396184691459317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52661400168528246255279089 39496050126396184691459317)
                    ·
                      refine ⟨3702754699349642314824311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39496050126396184691459317 3702754699349642314824311)
                      ·
                        rfl

theorem cell23_7211089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_7211089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211089 prefixEnd_7211089 := by exact prefixLift 7211089
  have htrace : WordTrace (prefixWord ++ tailWord_7211089) baseStart_7211089 baseEnd_7211089 := by
    simpa [prefixWord, tailWord_7211089, baseEnd_7211089] using wordTrace_append hprefix tailTrace_7211089
  have hstable : (prefixWord ++ tailWord_7211089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211089).length < 2 ^ (prefixWord ++ tailWord_7211089).sum := by decide
  have hdescent : baseEnd_7211089 < baseStart_7211089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211100 : List Nat := [2, 2, 4, 1, 1, 4, 1, 3, 5]
def baseStart_7211100 : Nat := 118140960795 + 7211100 * 2 ^ 59
def prefixEnd_7211100 : Nat := 4983230072969 + 3 ^ 40 * 7211100 * 2
def baseEnd_7211100 : Nat := 411417816404093530198529

theorem tailTrace_7211100 : CollatzResearch.WordTrace tailWord_7211100 prefixEnd_7211100 411417816404093530198529 := by
  unfold tailWord_7211100
  simp only [CollatzResearch.WordTrace]
  refine ⟨131505212087711866337891377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175340282783615821783855169 131505212087711866337891377)
  ·
    refine ⟨98628909065783899753418533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131505212087711866337891377 98628909065783899753418533)
    ·
      refine ⟨18492920449834481203765975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98628909065783899753418533 18492920449834481203765975)
      ·
        refine ⟨27739380674751721805648963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18492920449834481203765975 27739380674751721805648963)
        ·
          refine ⟨41609071012127582708473445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27739380674751721805648963 41609071012127582708473445)
          ·
            refine ⟨7801700814773921757838771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41609071012127582708473445 7801700814773921757838771)
            ·
              refine ⟨11702551222160882636758157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7801700814773921757838771 11702551222160882636758157)
              ·
                refine ⟨4388456708310330988784309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11702551222160882636758157 4388456708310330988784309)
                ·
                  refine ⟨411417816404093530198529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4388456708310330988784309 411417816404093530198529)
                  ·
                    rfl

theorem cell23_7211100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 5].length) (baseStart_7211100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211100 prefixEnd_7211100 := by exact prefixLift 7211100
  have htrace : WordTrace (prefixWord ++ tailWord_7211100) baseStart_7211100 baseEnd_7211100 := by
    simpa [prefixWord, tailWord_7211100, baseEnd_7211100] using wordTrace_append hprefix tailTrace_7211100
  have hstable : (prefixWord ++ tailWord_7211100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211100).length < 2 ^ (prefixWord ++ tailWord_7211100).sum := by decide
  have hdescent : baseEnd_7211100 < baseStart_7211100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211116 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_7211116 : Nat := 118140960795 + 7211116 * 2 ^ 59
def prefixEnd_7211116 : Nat := 4983230072969 + 3 ^ 40 * 7211116 * 2
def baseEnd_7211116 : Nat := 3702768563327313709186687

theorem tailTrace_7211116 : CollatzResearch.WordTrace tailWord_7211116 prefixEnd_7211116 3702768563327313709186687 := by
  unfold tailWord_7211116
  simp only [CollatzResearch.WordTrace]
  refine ⟨131505503871682883704182601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175340671828910511605576801 131505503871682883704182601)
  ·
    refine ⟨98629127903762162778136951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131505503871682883704182601 98629127903762162778136951)
    ·
      refine ⟨147943691855643244167205427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98629127903762162778136951 147943691855643244167205427)
      ·
        refine ⟨221915537783464866250808141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147943691855643244167205427 221915537783464866250808141)
        ·
          refine ⟨83218326668799324844053053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221915537783464866250808141 83218326668799324844053053)
          ·
            refine ⟨31206872500799746816519895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83218326668799324844053053 31206872500799746816519895)
            ·
              refine ⟨46810308751199620224779843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31206872500799746816519895 46810308751199620224779843)
              ·
                refine ⟨70215463126799430337169765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46810308751199620224779843 70215463126799430337169765)
                ·
                  refine ⟨13165399336274893188219331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70215463126799430337169765 13165399336274893188219331)
                  ·
                    refine ⟨19748099004412339782328997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13165399336274893188219331 19748099004412339782328997)
                    ·
                      refine ⟨3702768563327313709186687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19748099004412339782328997 3702768563327313709186687)
                      ·
                        rfl

theorem cell23_7211116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_7211116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211116 prefixEnd_7211116 := by exact prefixLift 7211116
  have htrace : WordTrace (prefixWord ++ tailWord_7211116) baseStart_7211116 baseEnd_7211116 := by
    simpa [prefixWord, tailWord_7211116, baseEnd_7211116] using wordTrace_append hprefix tailTrace_7211116
  have hstable : (prefixWord ++ tailWord_7211116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211116).length < 2 ^ (prefixWord ++ tailWord_7211116).sum := by decide
  have hdescent : baseEnd_7211116 < baseStart_7211116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211136 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 3]
def baseStart_7211136 : Nat := 118140960795 + 7211136 * 2 ^ 59
def prefixEnd_7211136 : Nat := 4983230072969 + 3 ^ 40 * 7211136 * 2
def baseEnd_7211136 : Nat := 3702778832940403630936595

theorem tailTrace_7211136 : CollatzResearch.WordTrace tailWord_7211136 prefixEnd_7211136 3702778832940403630936595 := by
  unfold tailWord_7211136
  simp only [CollatzResearch.WordTrace]
  refine ⟨131505868601646655412046631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175341158135528873882728841 131505868601646655412046631)
  ·
    refine ⟨197258802902469983118069947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131505868601646655412046631 197258802902469983118069947)
    ·
      refine ⟨295888204353704974677104921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197258802902469983118069947 295888204353704974677104921)
      ·
        refine ⟨221916153265278731007828691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295888204353704974677104921 221916153265278731007828691)
        ·
          refine ⟨332874229897918096511743037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221916153265278731007828691 332874229897918096511743037)
          ·
            refine ⟨124827836211719286191903639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332874229897918096511743037 124827836211719286191903639)
            ·
              refine ⟨187241754317578929287855459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124827836211719286191903639 187241754317578929287855459)
              ·
                refine ⟨280862631476368393931783189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187241754317578929287855459 280862631476368393931783189)
                ·
                  refine ⟨13165435850454768465552337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 280862631476368393931783189 13165435850454768465552337)
                  ·
                    refine ⟨9874076887841076349164253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13165435850454768465552337 9874076887841076349164253)
                    ·
                      refine ⟨3702778832940403630936595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9874076887841076349164253 3702778832940403630936595)
                      ·
                        rfl

theorem cell23_7211136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_7211136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211136 prefixEnd_7211136 := by exact prefixLift 7211136
  have htrace : WordTrace (prefixWord ++ tailWord_7211136) baseStart_7211136 baseEnd_7211136 := by
    simpa [prefixWord, tailWord_7211136, baseEnd_7211136] using wordTrace_append hprefix tailTrace_7211136
  have hstable : (prefixWord ++ tailWord_7211136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211136).length < 2 ^ (prefixWord ++ tailWord_7211136).sum := by decide
  have hdescent : baseEnd_7211136 < baseStart_7211136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211150 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_7211150 : Nat := 118140960795 + 7211150 * 2 ^ 59
def prefixEnd_7211150 : Nat := 4983230072969 + 3 ^ 40 * 7211150 * 2
def baseEnd_7211150 : Nat := 3702786021669566576161531

theorem tailTrace_7211150 : CollatzResearch.WordTrace tailWord_7211150 prefixEnd_7211150 3702786021669566576161531 := by
  unfold tailWord_7211150
  simp only [CollatzResearch.WordTrace]
  refine ⟨32876530978155323901887863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175341498550161727476735269 32876530978155323901887863)
  ·
    refine ⟨49314796467232985852831795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32876530978155323901887863 49314796467232985852831795)
    ·
      refine ⟨73972194700849478779247693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49314796467232985852831795 73972194700849478779247693)
      ·
        refine ⟨27739573012818554542217885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73972194700849478779247693 27739573012818554542217885)
        ·
          refine ⟨10402339879806957953331707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27739573012818554542217885 10402339879806957953331707)
          ·
            refine ⟨15603509819710436929997561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10402339879806957953331707 15603509819710436929997561)
            ·
              refine ⟨11702632364782827697498171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15603509819710436929997561 11702632364782827697498171)
              ·
                refine ⟨17553948547174241546247257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11702632364782827697498171 17553948547174241546247257)
                ·
                  refine ⟨13165461410380681159685443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17553948547174241546247257 13165461410380681159685443)
                  ·
                    refine ⟨19748192115571021739528165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13165461410380681159685443 19748192115571021739528165)
                    ·
                      refine ⟨3702786021669566576161531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19748192115571021739528165 3702786021669566576161531)
                      ·
                        rfl

theorem cell23_7211150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_7211150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211150 prefixEnd_7211150 := by exact prefixLift 7211150
  have htrace : WordTrace (prefixWord ++ tailWord_7211150) baseStart_7211150 baseEnd_7211150 := by
    simpa [prefixWord, tailWord_7211150, baseEnd_7211150] using wordTrace_append hprefix tailTrace_7211150
  have hstable : (prefixWord ++ tailWord_7211150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211150).length < 2 ^ (prefixWord ++ tailWord_7211150).sum := by decide
  have hdescent : baseEnd_7211150 < baseStart_7211150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211170 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_7211170 : Nat := 118140960795 + 7211170 * 2 ^ 59
def prefixEnd_7211170 : Nat := 4983230072969 + 3 ^ 40 * 7211170 * 2
def baseEnd_7211170 : Nat := 3702796291282656497911439

theorem tailTrace_7211170 : CollatzResearch.WordTrace tailWord_7211170 prefixEnd_7211170 3702796291282656497911439 := by
  unfold tailWord_7211170
  simp only [CollatzResearch.WordTrace]
  refine ⟨65753244321292533657707741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175341984856780089753887309 65753244321292533657707741)
  ·
    refine ⟨24657466620484700121640403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65753244321292533657707741 24657466620484700121640403)
    ·
      refine ⟨36986199930727050182460605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24657466620484700121640403 36986199930727050182460605)
      ·
        refine ⟨13869824974022643818422727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36986199930727050182460605 13869824974022643818422727)
        ·
          refine ⟨20804737461033965727634091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13869824974022643818422727 20804737461033965727634091)
          ·
            refine ⟨31207106191550948591451137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20804737461033965727634091 31207106191550948591451137)
            ·
              refine ⟨23405329643663211443588353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31207106191550948591451137 23405329643663211443588353)
              ·
                refine ⟨17553997232747408582691265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23405329643663211443588353 17553997232747408582691265)
                ·
                  refine ⟨13165497924560556437018449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17553997232747408582691265 13165497924560556437018449)
                  ·
                    refine ⟨9874123443420417327763837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13165497924560556437018449 9874123443420417327763837)
                    ·
                      refine ⟨3702796291282656497911439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9874123443420417327763837 3702796291282656497911439)
                      ·
                        rfl

theorem cell23_7211170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_7211170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211170 prefixEnd_7211170 := by exact prefixLift 7211170
  have htrace : WordTrace (prefixWord ++ tailWord_7211170) baseStart_7211170 baseEnd_7211170 := by
    simpa [prefixWord, tailWord_7211170, baseEnd_7211170] using wordTrace_append hprefix tailTrace_7211170
  have hstable : (prefixWord ++ tailWord_7211170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211170).length < 2 ^ (prefixWord ++ tailWord_7211170).sum := by decide
  have hdescent : baseEnd_7211170 < baseStart_7211170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211183 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 3, 1, 3]
def baseStart_7211183 : Nat := 118140960795 + 7211183 * 2 ^ 59
def prefixEnd_7211183 : Nat := 4983230072969 + 3 ^ 40 * 7211183 * 2
def baseEnd_7211183 : Nat := 3702802966531164947048879

theorem tailTrace_7211183 : CollatzResearch.WordTrace tailWord_7211183 prefixEnd_7211183 3702802966531164947048879 := by
  unfold tailWord_7211183
  simp only [CollatzResearch.WordTrace]
  refine ⟨263013451434123037851054203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175342300956082025234036135 263013451434123037851054203)
  ·
    refine ⟨394520177151184556776581305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263013451434123037851054203 394520177151184556776581305)
    ·
      refine ⟨295890132863388417582435979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394520177151184556776581305 295890132863388417582435979)
      ·
        refine ⟨443835199295082626373653969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295890132863388417582435979 443835199295082626373653969)
        ·
          refine ⟨332876399471311969780240477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443835199295082626373653969 332876399471311969780240477)
          ·
            refine ⟨124828649801741988667590179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332876399471311969780240477 124828649801741988667590179)
            ·
              refine ⟨187242974702612983001385269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124828649801741988667590179 187242974702612983001385269)
              ·
                refine ⟨17554028878369967156379869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187242974702612983001385269 17554028878369967156379869)
                ·
                  refine ⟨6582760829388737683642451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17554028878369967156379869 6582760829388737683642451)
                  ·
                    refine ⟨9874141244083106525463677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6582760829388737683642451 9874141244083106525463677)
                    ·
                      refine ⟨3702802966531164947048879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9874141244083106525463677 3702802966531164947048879)
                      ·
                        rfl

theorem cell23_7211183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 1, 3].length) (baseStart_7211183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211183 prefixEnd_7211183 := by exact prefixLift 7211183
  have htrace : WordTrace (prefixWord ++ tailWord_7211183) baseStart_7211183 baseEnd_7211183 := by
    simpa [prefixWord, tailWord_7211183, baseEnd_7211183] using wordTrace_append hprefix tailTrace_7211183
  have hstable : (prefixWord ++ tailWord_7211183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211183).length < 2 ^ (prefixWord ++ tailWord_7211183).sum := by decide
  have hdescent : baseEnd_7211183 < baseStart_7211183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211186 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_7211186 : Nat := 118140960795 + 7211186 * 2 ^ 59
def prefixEnd_7211186 : Nat := 4983230072969 + 3 ^ 40 * 7211186 * 2
def baseEnd_7211186 : Nat := 1234268168991042811770455

theorem tailTrace_7211186 : CollatzResearch.WordTrace tailWord_7211186 prefixEnd_7211186 1234268168991042811770455 := by
  unfold tailWord_7211186
  simp only [CollatzResearch.WordTrace]
  refine ⟨65753390213278042340853353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175342373902074779575608941 65753390213278042340853353)
  ·
    refine ⟨49315042659958531755640015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65753390213278042340853353 49315042659958531755640015)
    ·
      refine ⟨73972563989937797633460023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49315042659958531755640015 73972563989937797633460023)
      ·
        refine ⟨110958845984906696450190035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73972563989937797633460023 110958845984906696450190035)
        ·
          refine ⟨166438268977360044675285053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110958845984906696450190035 166438268977360044675285053)
          ·
            refine ⟨62414350866510016753231895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166438268977360044675285053 62414350866510016753231895)
            ·
              refine ⟨93621526299765025129847843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62414350866510016753231895 93621526299765025129847843)
              ·
                refine ⟨140432289449647537694771765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93621526299765025129847843 140432289449647537694771765)
                ·
                  refine ⟨13165527135904456658884853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140432289449647537694771765 13165527135904456658884853)
                  ·
                    refine ⟨1234268168991042811770455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13165527135904456658884853 1234268168991042811770455)
                    ·
                      rfl

theorem cell23_7211186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_7211186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211186 prefixEnd_7211186 := by exact prefixLift 7211186
  have htrace : WordTrace (prefixWord ++ tailWord_7211186) baseStart_7211186 baseEnd_7211186 := by
    simpa [prefixWord, tailWord_7211186, baseEnd_7211186] using wordTrace_append hprefix tailTrace_7211186
  have hstable : (prefixWord ++ tailWord_7211186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211186).length < 2 ^ (prefixWord ++ tailWord_7211186).sum := by decide
  have hdescent : baseEnd_7211186 < baseStart_7211186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211193 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 1, 5, 2]
def baseStart_7211193 : Nat := 118140960795 + 7211193 * 2 ^ 59
def prefixEnd_7211193 : Nat := 4983230072969 + 3 ^ 40 * 7211193 * 2
def baseEnd_7211193 : Nat := 3702808101337709907923833

theorem tailTrace_7211193 : CollatzResearch.WordTrace tailWord_7211193 prefixEnd_7211193 3702808101337709907923833 := by
  unfold tailWord_7211193
  simp only [CollatzResearch.WordTrace]
  refine ⟨263013816164086809558918233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175342544109391206372612155 263013816164086809558918233)
  ·
    refine ⟨197260362123065107169188675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263013816164086809558918233 197260362123065107169188675)
    ·
      refine ⟨295890543184597660753783013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197260362123065107169188675 295890543184597660753783013)
      ·
        refine ⟨55479476847112061391334315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 295890543184597660753783013 55479476847112061391334315)
        ·
          refine ⟨83219215270668092087001473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55479476847112061391334315 83219215270668092087001473)
          ·
            refine ⟨62414411453001069065251105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83219215270668092087001473 62414411453001069065251105)
            ·
              refine ⟨46810808589750801798938329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62414411453001069065251105 46810808589750801798938329)
              ·
                refine ⟨35108106442313101349203747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46810808589750801798938329 35108106442313101349203747)
                ·
                  refine ⟨52662159663469652023805621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35108106442313101349203747 52662159663469652023805621)
                  ·
                    refine ⟨4937077468450279877231777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52662159663469652023805621 4937077468450279877231777)
                    ·
                      refine ⟨3702808101337709907923833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937077468450279877231777 3702808101337709907923833)
                      ·
                        rfl

theorem cell23_7211193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_7211193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211193 prefixEnd_7211193 := by exact prefixLift 7211193
  have htrace : WordTrace (prefixWord ++ tailWord_7211193) baseStart_7211193 baseEnd_7211193 := by
    simpa [prefixWord, tailWord_7211193, baseEnd_7211193] using wordTrace_append hprefix tailTrace_7211193
  have hstable : (prefixWord ++ tailWord_7211193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211193).length < 2 ^ (prefixWord ++ tailWord_7211193).sum := by decide
  have hdescent : baseEnd_7211193 < baseStart_7211193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211200 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 3, 1, 3]
def baseStart_7211200 : Nat := 118140960795 + 7211200 * 2 ^ 59
def prefixEnd_7211200 : Nat := 4983230072969 + 3 ^ 40 * 7211200 * 2
def baseEnd_7211200 : Nat := 3702811695702291380536301

theorem tailTrace_7211200 : CollatzResearch.WordTrace tailWord_7211200 prefixEnd_7211200 3702811695702291380536301 := by
  unfold tailWord_7211200
  simp only [CollatzResearch.WordTrace]
  refine ⟨131507035737530724877211527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175342714316707633169615369 131507035737530724877211527)
  ·
    refine ⟨197260553606296087315817291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131507035737530724877211527 197260553606296087315817291)
    ·
      refine ⟨295890830409444130973725937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197260553606296087315817291 295890830409444130973725937)
      ·
        refine ⟨221918122807083098230294453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295890830409444130973725937 221918122807083098230294453)
        ·
          refine ⟨20804824013164040459090105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221918122807083098230294453 20804824013164040459090105)
          ·
            refine ⟨15603618009873030344317579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20804824013164040459090105 15603618009873030344317579)
            ·
              refine ⟨23405427014809545516476369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15603618009873030344317579 23405427014809545516476369)
              ·
                refine ⟨17554070261107159137357277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23405427014809545516476369 17554070261107159137357277)
                ·
                  refine ⟨6582776347915184676508979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17554070261107159137357277 6582776347915184676508979)
                  ·
                    refine ⟨9874164521872777014763469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6582776347915184676508979 9874164521872777014763469)
                    ·
                      refine ⟨3702811695702291380536301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9874164521872777014763469 3702811695702291380536301)
                      ·
                        rfl

theorem cell23_7211200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_7211200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211200 prefixEnd_7211200 := by exact prefixLift 7211200
  have htrace : WordTrace (prefixWord ++ tailWord_7211200) baseStart_7211200 baseEnd_7211200 := by
    simpa [prefixWord, tailWord_7211200, baseEnd_7211200] using wordTrace_append hprefix tailTrace_7211200
  have hstable : (prefixWord ++ tailWord_7211200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211200).length < 2 ^ (prefixWord ++ tailWord_7211200).sum := by decide
  have hdescent : baseEnd_7211200 < baseStart_7211200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211233 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 4, 4]
def baseStart_7211233 : Nat := 118140960795 + 7211233 * 2 ^ 59
def prefixEnd_7211233 : Nat := 4983230072969 + 3 ^ 40 * 7211233 * 2
def baseEnd_7211233 : Nat := 1234276213521296583807883

theorem tailTrace_7211233 : CollatzResearch.WordTrace tailWord_7211233 prefixEnd_7211233 1234276213521296583807883 := by
  unfold tailWord_7211233
  simp only [CollatzResearch.WordTrace]
  refine ⟨263015275083941896390374353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175343516722627930926916235 263015275083941896390374353)
  ·
    refine ⟨197261456312956422292780765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263015275083941896390374353 197261456312956422292780765)
    ·
      refine ⟨73973046117358658359792787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197261456312956422292780765 73973046117358658359792787)
      ·
        refine ⟨110959569176037987539689181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73973046117358658359792787 110959569176037987539689181)
        ·
          refine ⟨41609838441014245327383443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110959569176037987539689181 41609838441014245327383443)
          ·
            refine ⟨62414757661521367991075165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41609838441014245327383443 62414757661521367991075165)
            ·
              refine ⟨23405534123070512996653187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62414757661521367991075165 23405534123070512996653187)
              ·
                refine ⟨35108301184605769494979781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23405534123070512996653187 35108301184605769494979781)
                ·
                  refine ⟨6582806472113581780308709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35108301184605769494979781 6582806472113581780308709)
                  ·
                    refine ⟨1234276213521296583807883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6582806472113581780308709 1234276213521296583807883)
                    ·
                      rfl

theorem cell23_7211233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_7211233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211233 prefixEnd_7211233 := by exact prefixLift 7211233
  have htrace : WordTrace (prefixWord ++ tailWord_7211233) baseStart_7211233 baseEnd_7211233 := by
    simpa [prefixWord, tailWord_7211233, baseEnd_7211233] using wordTrace_append hprefix tailTrace_7211233
  have hstable : (prefixWord ++ tailWord_7211233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211233).length < 2 ^ (prefixWord ++ tailWord_7211233).sum := by decide
  have hdescent : baseEnd_7211233 < baseStart_7211233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211236 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_7211236 : Nat := 118140960795 + 7211236 * 2 ^ 59
def prefixEnd_7211236 : Nat := 4983230072969 + 3 ^ 40 * 7211236 * 2
def baseEnd_7211236 : Nat := 3702830181005853239686135

theorem tailTrace_7211236 : CollatzResearch.WordTrace tailWord_7211236 prefixEnd_7211236 3702830181005853239686135 := by
  unfold tailWord_7211236
  simp only [CollatzResearch.WordTrace]
  refine ⟨131507692251465513951366781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175343589668620685268489041 131507692251465513951366781)
  ·
    refine ⟨49315384594299567731762543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131507692251465513951366781 49315384594299567731762543)
    ·
      refine ⟨73973076891449351597643815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49315384594299567731762543 73973076891449351597643815)
      ·
        refine ⟨110959615337174027396465723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73973076891449351597643815 110959615337174027396465723)
        ·
          refine ⟨166439423005761041094698585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110959615337174027396465723 166439423005761041094698585)
          ·
            refine ⟨124829567254320780821023939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166439423005761041094698585 124829567254320780821023939)
            ·
              refine ⟨187244350881481171231535909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124829567254320780821023939 187244350881481171231535909)
              ·
                refine ⟨35108315790277719605912983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187244350881481171231535909 35108315790277719605912983)
                ·
                  refine ⟨52662473685416579408869475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35108315790277719605912983 52662473685416579408869475)
                  ·
                    refine ⟨78993710528124869113304213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52662473685416579408869475 78993710528124869113304213)
                    ·
                      refine ⟨3702830181005853239686135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78993710528124869113304213 3702830181005853239686135)
                      ·
                        rfl

theorem cell23_7211236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_7211236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211236 prefixEnd_7211236 := by exact prefixLift 7211236
  have htrace : WordTrace (prefixWord ++ tailWord_7211236) baseStart_7211236 baseEnd_7211236 := by
    simpa [prefixWord, tailWord_7211236, baseEnd_7211236] using wordTrace_append hprefix tailTrace_7211236
  have hstable : (prefixWord ++ tailWord_7211236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211236).length < 2 ^ (prefixWord ++ tailWord_7211236).sum := by decide
  have hdescent : baseEnd_7211236 < baseStart_7211236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211246 : List Nat := [4, 1, 2, 1, 1, 1, 1, 12]
def baseStart_7211246 : Nat := 118140960795 + 7211246 * 2 ^ 59
def prefixEnd_7211246 : Nat := 4983230072969 + 3 ^ 40 * 7211246 * 2
def baseEnd_7211246 : Nat := 137142048733792525946707

theorem tailTrace_7211246 : CollatzResearch.WordTrace tailWord_7211246 prefixEnd_7211246 137142048733792525946707 := by
  unfold tailWord_7211246
  simp only [CollatzResearch.WordTrace]
  refine ⟨32876968654111849951324699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175343832821929866407065061 32876968654111849951324699)
  ·
    refine ⟨49315452981167774926987049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32876968654111849951324699 49315452981167774926987049)
    ·
      refine ⟨36986589735875831195240287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49315452981167774926987049 36986589735875831195240287)
      ·
        refine ⟨55479884603813746792860431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36986589735875831195240287 55479884603813746792860431)
        ·
          refine ⟨83219826905720620189290647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55479884603813746792860431 83219826905720620189290647)
          ·
            refine ⟨124829740358580930283935971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83219826905720620189290647 124829740358580930283935971)
            ·
              refine ⟨187244610537871395425903957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124829740358580930283935971 187244610537871395425903957)
              ·
                refine ⟨137142048733792525946707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 187244610537871395425903957 137142048733792525946707)
                ·
                  rfl

theorem cell23_7211246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_7211246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211246 prefixEnd_7211246 := by exact prefixLift 7211246
  have htrace : WordTrace (prefixWord ++ tailWord_7211246) baseStart_7211246 baseEnd_7211246 := by
    simpa [prefixWord, tailWord_7211246, baseEnd_7211246] using wordTrace_append hprefix tailTrace_7211246
  have hstable : (prefixWord ++ tailWord_7211246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211246).length < 2 ^ (prefixWord ++ tailWord_7211246).sum := by decide
  have hdescent : baseEnd_7211246 < baseStart_7211246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211250 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_7211250 : Nat := 118140960795 + 7211250 * 2 ^ 59
def prefixEnd_7211250 : Nat := 4983230072969 + 3 ^ 40 * 7211250 * 2
def baseEnd_7211250 : Nat := 1234279123245005394970357

theorem tailTrace_7211250 : CollatzResearch.WordTrace tailWord_7211250 prefixEnd_7211250 1234279123245005394970357 := by
  unfold tailWord_7211250
  simp only [CollatzResearch.WordTrace]
  refine ⟨65753973781220077073435801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175343930083253538862495469 65753973781220077073435801)
  ·
    refine ⟨49315480335915057805076851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65753973781220077073435801 49315480335915057805076851)
    ·
      refine ⟨73973220503872586707615277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49315480335915057805076851 73973220503872586707615277)
      ·
        refine ⟨27739957688952220015355729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73973220503872586707615277 27739957688952220015355729)
        ·
          refine ⟨20804968266714165011516797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27739957688952220015355729 20804968266714165011516797)
          ·
            refine ⟨7801863100017811879318799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20804968266714165011516797 7801863100017811879318799)
            ·
              refine ⟨11702794650026717818978199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7801863100017811879318799 11702794650026717818978199)
              ·
                refine ⟨17554191975040076728467299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11702794650026717818978199 17554191975040076728467299)
                ·
                  refine ⟨26331287962560115092700949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17554191975040076728467299 26331287962560115092700949)
                  ·
                    refine ⟨1234279123245005394970357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26331287962560115092700949 1234279123245005394970357)
                    ·
                      rfl

theorem cell23_7211250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_7211250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211250 prefixEnd_7211250 := by exact prefixLift 7211250
  have htrace : WordTrace (prefixWord ++ tailWord_7211250) baseStart_7211250 baseEnd_7211250 := by
    simpa [prefixWord, tailWord_7211250, baseEnd_7211250] using wordTrace_append hprefix tailTrace_7211250
  have hstable : (prefixWord ++ tailWord_7211250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211250).length < 2 ^ (prefixWord ++ tailWord_7211250).sum := by decide
  have hdescent : baseEnd_7211250 < baseStart_7211250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211260 : List Nat := [2, 2, 2, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_7211260 : Nat := 118140960795 + 7211260 * 2 ^ 59
def prefixEnd_7211260 : Nat := 4983230072969 + 3 ^ 40 * 7211260 * 2
def baseEnd_7211260 : Nat := 3702842504541561145786025

theorem tailTrace_7211260 : CollatzResearch.WordTrace tailWord_7211260 prefixEnd_7211260 3702842504541561145786025 := by
  unfold tailWord_7211260
  simp only [CollatzResearch.WordTrace]
  refine ⟨131508129927422040000803617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175344173236562720001071489 131508129927422040000803617)
  ·
    refine ⟨98631097445566530000602713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131508129927422040000803617 98631097445566530000602713)
    ·
      refine ⟨73973323084174897500452035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98631097445566530000602713 73973323084174897500452035)
      ·
        refine ⟨110959984626262346250678053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73973323084174897500452035 110959984626262346250678053)
        ·
          refine ⟨20804997117424189922002135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110959984626262346250678053 20804997117424189922002135)
          ·
            refine ⟨31207495676136284883003203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20804997117424189922002135 31207495676136284883003203)
            ·
              refine ⟨46811243514204427324504805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31207495676136284883003203 46811243514204427324504805)
              ·
                refine ⟨8777108158913330123344651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46811243514204427324504805 8777108158913330123344651)
                ·
                  refine ⟨13165662238369995185016977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8777108158913330123344651 13165662238369995185016977)
                  ·
                    refine ⟨9874246678777496388762733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13165662238369995185016977 9874246678777496388762733)
                    ·
                      refine ⟨3702842504541561145786025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9874246678777496388762733 3702842504541561145786025)
                      ·
                        rfl

theorem cell23_7211260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_7211260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211260 prefixEnd_7211260 := by exact prefixLift 7211260
  have htrace : WordTrace (prefixWord ++ tailWord_7211260) baseStart_7211260 baseEnd_7211260 := by
    simpa [prefixWord, tailWord_7211260, baseEnd_7211260] using wordTrace_append hprefix tailTrace_7211260
  have hstable : (prefixWord ++ tailWord_7211260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211260).length < 2 ^ (prefixWord ++ tailWord_7211260).sum := by decide
  have hdescent : baseEnd_7211260 < baseStart_7211260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211274 : List Nat := [3, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2]
def baseStart_7211274 : Nat := 118140960795 + 7211274 * 2 ^ 59
def prefixEnd_7211274 : Nat := 4983230072969 + 3 ^ 40 * 7211274 * 2
def baseEnd_7211274 : Nat := 3702849693270724091010961

theorem tailTrace_7211274 : CollatzResearch.WordTrace tailWord_7211274 prefixEnd_7211274 3702849693270724091010961 := by
  unfold tailWord_7211274
  simp only [CollatzResearch.WordTrace]
  refine ⟨65754192619198340098154219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175344513651195573595077917 65754192619198340098154219)
  ·
    refine ⟨98631288928797510147231329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65754192619198340098154219 98631288928797510147231329)
    ·
      refine ⟨73973466696598132610423497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98631288928797510147231329 73973466696598132610423497)
      ·
        refine ⟨55480100022448599457817623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73973466696598132610423497 55480100022448599457817623)
        ·
          refine ⟨83220150033672899186726435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55480100022448599457817623 83220150033672899186726435)
          ·
            refine ⟨124830225050509348780089653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83220150033672899186726435 124830225050509348780089653)
            ·
              refine ⟨11702833598485251448133405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124830225050509348780089653 11702833598485251448133405)
              ·
                refine ⟨4388562599431969293050027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11702833598485251448133405 4388562599431969293050027)
                ·
                  refine ⟨6582843899147953939575041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388562599431969293050027 6582843899147953939575041)
                  ·
                    refine ⟨4937132924360965454681281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6582843899147953939575041 4937132924360965454681281)
                    ·
                      refine ⟨3702849693270724091010961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4937132924360965454681281 3702849693270724091010961)
                      ·
                        rfl

theorem cell23_7211274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_7211274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211274 prefixEnd_7211274 := by exact prefixLift 7211274
  have htrace : WordTrace (prefixWord ++ tailWord_7211274) baseStart_7211274 baseEnd_7211274 := by
    simpa [prefixWord, tailWord_7211274, baseEnd_7211274] using wordTrace_append hprefix tailTrace_7211274
  have hstable : (prefixWord ++ tailWord_7211274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211274).length < 2 ^ (prefixWord ++ tailWord_7211274).sum := by decide
  have hdescent : baseEnd_7211274 < baseStart_7211274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211358 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_7211358 : Nat := 118140960795 + 7211358 * 2 ^ 59
def prefixEnd_7211358 : Nat := 4983230072969 + 3 ^ 40 * 7211358 * 2
def baseEnd_7211358 : Nat := 3702892825645701762360575

theorem tailTrace_7211358 : CollatzResearch.WordTrace tailWord_7211358 prefixEnd_7211358 3702892825645701762360575 := by
  unfold tailWord_7211358
  simp only [CollatzResearch.WordTrace]
  refine ⟨32877479276061130342334341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175346556138992695159116485 32877479276061130342334341)
  ·
    refine ⟨6164527364261461939187689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32877479276061130342334341 6164527364261461939187689)
    ·
      refine ⟨4623395523196096454390767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6164527364261461939187689 4623395523196096454390767)
      ·
        refine ⟨6935093284794144681586151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623395523196096454390767 6935093284794144681586151)
        ·
          refine ⟨10402639927191217022379227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6935093284794144681586151 10402639927191217022379227)
          ·
            refine ⟨15603959890786825533568841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10402639927191217022379227 15603959890786825533568841)
            ·
              refine ⟨11702969918090119150176631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15603959890786825533568841 11702969918090119150176631)
              ·
                refine ⟨17554454877135178725264947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11702969918090119150176631 17554454877135178725264947)
                ·
                  refine ⟨26331682315702768087897421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17554454877135178725264947 26331682315702768087897421)
                  ·
                    refine ⟨9874380868388538032961533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26331682315702768087897421 9874380868388538032961533)
                    ·
                      refine ⟨3702892825645701762360575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9874380868388538032961533 3702892825645701762360575)
                      ·
                        rfl

theorem cell23_7211358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_7211358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211358 prefixEnd_7211358 := by exact prefixLift 7211358
  have htrace : WordTrace (prefixWord ++ tailWord_7211358) baseStart_7211358 baseEnd_7211358 := by
    simpa [prefixWord, tailWord_7211358, baseEnd_7211358] using wordTrace_append hprefix tailTrace_7211358
  have hstable : (prefixWord ++ tailWord_7211358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211358).length < 2 ^ (prefixWord ++ tailWord_7211358).sum := by decide
  have hdescent : baseEnd_7211358 < baseStart_7211358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211360 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 4]
def baseStart_7211360 : Nat := 118140960795 + 7211360 * 2 ^ 59
def prefixEnd_7211360 : Nat := 4983230072969 + 3 ^ 40 * 7211360 * 2
def baseEnd_7211360 : Nat := 3702893852607010754535565

theorem tailTrace_7211360 : CollatzResearch.WordTrace tailWord_7211360 prefixEnd_7211360 3702893852607010754535565 := by
  unfold tailWord_7211360
  simp only [CollatzResearch.WordTrace]
  refine ⟨131509953577240898540123767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175346604769654531386831689 131509953577240898540123767)
  ·
    refine ⟨197264930365861347810185651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131509953577240898540123767 197264930365861347810185651)
    ·
      refine ⟨295897395548792021715278477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197264930365861347810185651 295897395548792021715278477)
      ·
        refine ⟨110961523330797008143229429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295897395548792021715278477 110961523330797008143229429)
        ·
          refine ⟨10402642812262219513427759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110961523330797008143229429 10402642812262219513427759)
          ·
            refine ⟨15603964218393329270141639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10402642812262219513427759 15603964218393329270141639)
            ·
              refine ⟨23405946327589993905212459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15603964218393329270141639 23405946327589993905212459)
              ·
                refine ⟨35108919491384990857818689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23405946327589993905212459 35108919491384990857818689)
                ·
                  refine ⟨26331689618538743143364017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35108919491384990857818689 26331689618538743143364017)
                  ·
                    refine ⟨19748767213904057357523013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26331689618538743143364017 19748767213904057357523013)
                    ·
                      refine ⟨3702893852607010754535565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19748767213904057357523013 3702893852607010754535565)
                      ·
                        rfl

theorem cell23_7211360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_7211360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211360 prefixEnd_7211360 := by exact prefixLift 7211360
  have htrace : WordTrace (prefixWord ++ tailWord_7211360) baseStart_7211360 baseEnd_7211360 := by
    simpa [prefixWord, tailWord_7211360, baseEnd_7211360] using wordTrace_append hprefix tailTrace_7211360
  have hstable : (prefixWord ++ tailWord_7211360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211360).length < 2 ^ (prefixWord ++ tailWord_7211360).sum := by decide
  have hdescent : baseEnd_7211360 < baseStart_7211360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7211370 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 7]
def baseStart_7211370 : Nat := 118140960795 + 7211370 * 2 ^ 59
def prefixEnd_7211370 : Nat := 4983230072969 + 3 ^ 40 * 7211370 * 2
def baseEnd_7211370 : Nat := 411433220823728412823391

theorem tailTrace_7211370 : CollatzResearch.WordTrace tailWord_7211370 prefixEnd_7211370 411433220823728412823391 := by
  unfold tailWord_7211370
  simp only [CollatzResearch.WordTrace]
  refine ⟨65755067971111392197027891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175346847922963712525407709 65755067971111392197027891)
  ·
    refine ⟨98632601956667088295541837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65755067971111392197027891 98632601956667088295541837)
    ·
      refine ⟨36987225733750158110828189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98632601956667088295541837 36987225733750158110828189)
      ·
        refine ⟨13870209650156309291560571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36987225733750158110828189 13870209650156309291560571)
        ·
          refine ⟨20805314475234463937340857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13870209650156309291560571 20805314475234463937340857)
          ·
            refine ⟨15603985856425847953005643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20805314475234463937340857 15603985856425847953005643)
            ·
              refine ⟨23405978784638771929508465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15603985856425847953005643 23405978784638771929508465)
              ·
                refine ⟨17554484088479078947131349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23405978784638771929508465 17554484088479078947131349)
                ·
                  refine ⟨411433220823728412823391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17554484088479078947131349 411433220823728412823391)
                  ·
                    rfl

theorem cell23_7211370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_7211370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7211370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7211370 prefixEnd_7211370 := by exact prefixLift 7211370
  have htrace : WordTrace (prefixWord ++ tailWord_7211370) baseStart_7211370 baseEnd_7211370 := by
    simpa [prefixWord, tailWord_7211370, baseEnd_7211370] using wordTrace_append hprefix tailTrace_7211370
  have hstable : (prefixWord ++ tailWord_7211370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7211370).length < 2 ^ (prefixWord ++ tailWord_7211370).sum := by decide
  have hdescent : baseEnd_7211370 < baseStart_7211370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7211370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
