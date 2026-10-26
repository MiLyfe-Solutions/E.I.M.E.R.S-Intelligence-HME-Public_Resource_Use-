import V185TrunkScan23Chunk1300

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7705022 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_7705022 : Nat := 118140960795 + 7705022 * 2 ^ 59
def prefixEnd_7705022 : Nat := 4983230072969 + 3 ^ 40 * 7705022 * 2
def baseEnd_7705022 : Nat := 3956379739466858299690255

theorem tailTrace_7705022 : CollatzResearch.WordTrace tailWord_7705022 prefixEnd_7705022 3956379739466858299690255 := by
  unfold tailWord_7705022
  simp only [CollatzResearch.WordTrace]
  refine ⟨35128154936503585229690665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187350159661352454558350213 35128154936503585229690665)
  ·
    refine ⟨26346116202377688922267999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35128154936503585229690665 26346116202377688922267999)
    ·
      refine ⟨39519174303566533383401999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26346116202377688922267999 39519174303566533383401999)
      ·
        refine ⟨59278761455349800075102999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39519174303566533383401999 59278761455349800075102999)
        ·
          refine ⟨88918142183024700112654499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59278761455349800075102999 88918142183024700112654499)
          ·
            refine ⟨133377213274537050168981749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88918142183024700112654499 133377213274537050168981749)
            ·
              refine ⟨12504113744487848453342039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133377213274537050168981749 12504113744487848453342039)
              ·
                refine ⟨18756170616731772680013059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12504113744487848453342039 18756170616731772680013059)
                ·
                  refine ⟨28134255925097659020019589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18756170616731772680013059 28134255925097659020019589)
                  ·
                    refine ⟨5275172985955811066253673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28134255925097659020019589 5275172985955811066253673)
                    ·
                      refine ⟨3956379739466858299690255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5275172985955811066253673 3956379739466858299690255)
                      ·
                        rfl

theorem cell23_7705022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_7705022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705022 prefixEnd_7705022 := by exact prefixLift 7705022
  have htrace : WordTrace (prefixWord ++ tailWord_7705022) baseStart_7705022 baseEnd_7705022 := by
    simpa [prefixWord, tailWord_7705022, baseEnd_7705022] using wordTrace_append hprefix tailTrace_7705022
  have hstable : (prefixWord ++ tailWord_7705022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705022).length < 2 ^ (prefixWord ++ tailWord_7705022).sum := by decide
  have hdescent : baseEnd_7705022 < baseStart_7705022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705042 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_7705042 : Nat := 118140960795 + 7705042 * 2 ^ 59
def prefixEnd_7705042 : Nat := 4983230072969 + 3 ^ 40 * 7705042 * 2
def baseEnd_7705042 : Nat := 3956390009079948221440163

theorem tailTrace_7705042 : CollatzResearch.WordTrace tailWord_7705042 prefixEnd_7705042 3956390009079948221440163 := by
  unfold tailWord_7705042
  simp only [CollatzResearch.WordTrace]
  refine ⟨70256492237989056313313345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187350645967970816835502253 70256492237989056313313345)
  ·
    refine ⟨52692369178491792234985009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70256492237989056313313345 52692369178491792234985009)
    ·
      refine ⟨39519276883868844176238757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52692369178491792234985009 39519276883868844176238757)
      ·
        refine ⟨7409864415725408283044767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39519276883868844176238757 7409864415725408283044767)
        ·
          refine ⟨11114796623588112424567151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7409864415725408283044767 11114796623588112424567151)
          ·
            refine ⟨16672194935382168636850727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11114796623588112424567151 16672194935382168636850727)
            ·
              refine ⟨25008292403073252955276091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16672194935382168636850727 25008292403073252955276091)
              ·
                refine ⟨37512438604609879432914137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25008292403073252955276091 37512438604609879432914137)
                ·
                  refine ⟨28134328953457409574685603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37512438604609879432914137 28134328953457409574685603)
                  ·
                    refine ⟨42201493430186114362028405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28134328953457409574685603 42201493430186114362028405)
                    ·
                      refine ⟨3956390009079948221440163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42201493430186114362028405 3956390009079948221440163)
                      ·
                        rfl

theorem cell23_7705042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_7705042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705042 prefixEnd_7705042 := by exact prefixLift 7705042
  have htrace : WordTrace (prefixWord ++ tailWord_7705042) baseStart_7705042 baseEnd_7705042 := by
    simpa [prefixWord, tailWord_7705042, baseEnd_7705042] using wordTrace_append hprefix tailTrace_7705042
  have hstable : (prefixWord ++ tailWord_7705042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705042).length < 2 ^ (prefixWord ++ tailWord_7705042).sum := by decide
  have hdescent : baseEnd_7705042 < baseStart_7705042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705068 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_7705068 : Nat := 118140960795 + 7705068 * 2 ^ 59
def prefixEnd_7705068 : Nat := 4983230072969 + 3 ^ 40 * 7705068 * 2
def baseEnd_7705068 : Nat := 3956403359576965119715043

theorem tailTrace_7705068 : CollatzResearch.WordTrace tailWord_7705068 prefixEnd_7705068 3956403359576965119715043 := by
  unfold tailWord_7705068
  simp only [CollatzResearch.WordTrace]
  refine ⟨140513458624931015846849929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187351278166574687795799905 140513458624931015846849929)
  ·
    refine ⟨105385093968698261885137447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140513458624931015846849929 105385093968698261885137447)
    ·
      refine ⟨158077640953047392827706171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105385093968698261885137447 158077640953047392827706171)
      ·
        refine ⟨237116461429571089241559257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158077640953047392827706171 237116461429571089241559257)
        ·
          refine ⟨177837346072178316931169443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237116461429571089241559257 177837346072178316931169443)
          ·
            refine ⟨266756019108267475396754165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177837346072178316931169443 266756019108267475396754165)
            ·
              refine ⟨25008376791400075818445703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 266756019108267475396754165 25008376791400075818445703)
              ·
                refine ⟨37512565187100113727668555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25008376791400075818445703 37512565187100113727668555)
                ·
                  refine ⟨56268847780650170591502833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37512565187100113727668555 56268847780650170591502833)
                  ·
                    refine ⟨42201635835487627943627125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56268847780650170591502833 42201635835487627943627125)
                    ·
                      refine ⟨3956403359576965119715043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42201635835487627943627125 3956403359576965119715043)
                      ·
                        rfl

theorem cell23_7705068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_7705068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705068 prefixEnd_7705068 := by exact prefixLift 7705068
  have htrace : WordTrace (prefixWord ++ tailWord_7705068) baseStart_7705068 baseEnd_7705068 := by
    simpa [prefixWord, tailWord_7705068, baseEnd_7705068] using wordTrace_append hprefix tailTrace_7705068
  have hstable : (prefixWord ++ tailWord_7705068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705068).length < 2 ^ (prefixWord ++ tailWord_7705068).sum := by decide
  have hdescent : baseEnd_7705068 < baseStart_7705068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705092 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_7705092 : Nat := 118140960795 + 7705092 * 2 ^ 59
def prefixEnd_7705092 : Nat := 4983230072969 + 3 ^ 40 * 7705092 * 2
def baseEnd_7705092 : Nat := 1318805227704224341938311

theorem tailTrace_7705092 : CollatzResearch.WordTrace tailWord_7705092 prefixEnd_7705092 1318805227704224341938311 := by
  unfold tailWord_7705092
  simp only [CollatzResearch.WordTrace]
  refine ⟨140513896300887541896286765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187351861734516722528382353 140513896300887541896286765)
  ·
    refine ⟨52692711112832828211107537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140513896300887541896286765 52692711112832828211107537)
    ·
      refine ⟨39519533334624621158330653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52692711112832828211107537 39519533334624621158330653)
      ·
        refine ⟨14819825000484232934373995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39519533334624621158330653 14819825000484232934373995)
        ·
          refine ⟨22229737500726349401560993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14819825000484232934373995 22229737500726349401560993)
          ·
            refine ⟨16672303125544762051170745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22229737500726349401560993 16672303125544762051170745)
            ·
              refine ⟨12504227344158571538378059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16672303125544762051170745 12504227344158571538378059)
              ·
                refine ⟨18756341016237857307567089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12504227344158571538378059 18756341016237857307567089)
                ·
                  refine ⟨14067255762178392980675317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18756341016237857307567089 14067255762178392980675317)
                  ·
                    refine ⟨1318805227704224341938311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14067255762178392980675317 1318805227704224341938311)
                    ·
                      rfl

theorem cell23_7705092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_7705092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705092 prefixEnd_7705092 := by exact prefixLift 7705092
  have htrace : WordTrace (prefixWord ++ tailWord_7705092) baseStart_7705092 baseEnd_7705092 := by
    simpa [prefixWord, tailWord_7705092, baseEnd_7705092] using wordTrace_append hprefix tailTrace_7705092
  have hstable : (prefixWord ++ tailWord_7705092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705092).length < 2 ^ (prefixWord ++ tailWord_7705092).sum := by decide
  have hdescent : baseEnd_7705092 < baseStart_7705092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705149 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_7705149 : Nat := 118140960795 + 7705149 * 2 ^ 59
def prefixEnd_7705149 : Nat := 4983230072969 + 3 ^ 40 * 7705149 * 2
def baseEnd_7705149 : Nat := 3956444951509979302802171

theorem tailTrace_7705149 : CollatzResearch.WordTrace tailWord_7705149 prefixEnd_7705149 3956444951509979302802171 := by
  unfold tailWord_7705149
  simp only [CollatzResearch.WordTrace]
  refine ⟨281029871562568582527398501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187353247708379055018265667 281029871562568582527398501)
  ·
    refine ⟨52693100917981609223887219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281029871562568582527398501 52693100917981609223887219)
    ·
      refine ⟨79039651376972413835830829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52693100917981609223887219 79039651376972413835830829)
      ·
        refine ⟨29639869266364655188436561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79039651376972413835830829 29639869266364655188436561)
        ·
          refine ⟨22229901949773491391327421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29639869266364655188436561 22229901949773491391327421)
          ·
            refine ⟨8336213231165059271747783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22229901949773491391327421 8336213231165059271747783)
            ·
              refine ⟨12504319846747588907621675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336213231165059271747783 12504319846747588907621675)
              ·
                refine ⟨18756479770121383361432513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12504319846747588907621675 18756479770121383361432513)
                ·
                  refine ⟨14067359827591037521074385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18756479770121383361432513 14067359827591037521074385)
                  ·
                    refine ⟨10550519870693278140805789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14067359827591037521074385 10550519870693278140805789)
                    ·
                      refine ⟨3956444951509979302802171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10550519870693278140805789 3956444951509979302802171)
                      ·
                        rfl

theorem cell23_7705149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_7705149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705149 prefixEnd_7705149 := by exact prefixLift 7705149
  have htrace : WordTrace (prefixWord ++ tailWord_7705149) baseStart_7705149 baseEnd_7705149 := by
    simpa [prefixWord, tailWord_7705149, baseEnd_7705149] using wordTrace_append hprefix tailTrace_7705149
  have hstable : (prefixWord ++ tailWord_7705149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705149).length < 2 ^ (prefixWord ++ tailWord_7705149).sum := by decide
  have hdescent : baseEnd_7705149 < baseStart_7705149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705178 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 2, 10]
def baseStart_7705178 : Nat := 118140960795 + 7705178 * 2 ^ 59
def prefixEnd_7705178 : Nat := 4983230072969 + 3 ^ 40 * 7705178 * 2
def baseEnd_7705178 : Nat := 1318819947482986563113179

theorem tailTrace_7705178 : CollatzResearch.WordTrace tailWord_7705178 prefixEnd_7705178 1318819947482986563113179 := by
  unfold tailWord_7705178
  simp only [CollatzResearch.WordTrace]
  refine ⟨70257732319865880120051047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187353952852975680320136125 70257732319865880120051047)
  ·
    refine ⟨105386598479798820180076571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70257732319865880120051047 105386598479798820180076571)
    ·
      refine ⟨158079897719698230270114857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105386598479798820180076571 158079897719698230270114857)
      ·
        refine ⟨118559923289773672702586143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158079897719698230270114857 118559923289773672702586143)
        ·
          refine ⟨177839884934660509053879215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118559923289773672702586143 177839884934660509053879215)
          ·
            refine ⟨266759827401990763580818823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177839884934660509053879215 266759827401990763580818823)
            ·
              refine ⟨400139741102986145371228235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266759827401990763580818823 400139741102986145371228235)
              ·
                refine ⟨600209611654479218056842353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400139741102986145371228235 600209611654479218056842353)
                ·
                  refine ⟨450157208740859413542631765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600209611654479218056842353 450157208740859413542631765)
                  ·
                    refine ⟨1318819947482986563113179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 450157208740859413542631765 1318819947482986563113179)
                    ·
                      rfl

theorem cell23_7705178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_7705178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705178 prefixEnd_7705178 := by exact prefixLift 7705178
  have htrace : WordTrace (prefixWord ++ tailWord_7705178) baseStart_7705178 baseEnd_7705178 := by
    simpa [prefixWord, tailWord_7705178, baseEnd_7705178] using wordTrace_append hprefix tailTrace_7705178
  have hstable : (prefixWord ++ tailWord_7705178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705178).length < 2 ^ (prefixWord ++ tailWord_7705178).sum := by decide
  have hdescent : baseEnd_7705178 < baseStart_7705178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705186 : List Nat := [3, 3, 2, 3, 1, 1, 3, 1, 6]
def baseStart_7705186 : Nat := 118140960795 + 7705186 * 2 ^ 59
def prefixEnd_7705186 : Nat := 4983230072969 + 3 ^ 40 * 7705186 * 2
def baseEnd_7705186 : Nat := 439607105588243962004389

theorem tailTrace_7705186 : CollatzResearch.WordTrace tailWord_7705186 prefixEnd_7705186 439607105588243962004389 := by
  unfold tailWord_7705186
  simp only [CollatzResearch.WordTrace]
  refine ⟨70257805265858634461623853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187354147375623025230996941 70257805265858634461623853)
  ·
    refine ⟨26346676974696987923108945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70257805265858634461623853 26346676974696987923108945)
    ·
      refine ⟨19760007731022740942331709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26346676974696987923108945 19760007731022740942331709)
      ·
        refine ⟨7410002899133527853374391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19760007731022740942331709 7410002899133527853374391)
        ·
          refine ⟨11115004348700291780061587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7410002899133527853374391 11115004348700291780061587)
          ·
            refine ⟨16672506523050437670092381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11115004348700291780061587 16672506523050437670092381)
            ·
              refine ⟨6252189946143914126284643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16672506523050437670092381 6252189946143914126284643)
              ·
                refine ⟨9378284919215871189426965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6252189946143914126284643 9378284919215871189426965)
                ·
                  refine ⟨439607105588243962004389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9378284919215871189426965 439607105588243962004389)
                  ·
                    rfl

theorem cell23_7705186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_7705186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705186 prefixEnd_7705186 := by exact prefixLift 7705186
  have htrace : WordTrace (prefixWord ++ tailWord_7705186) baseStart_7705186 baseEnd_7705186 := by
    simpa [prefixWord, tailWord_7705186, baseEnd_7705186] using wordTrace_append hprefix tailTrace_7705186
  have hstable : (prefixWord ++ tailWord_7705186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705186).length < 2 ^ (prefixWord ++ tailWord_7705186).sum := by decide
  have hdescent : baseEnd_7705186 < baseStart_7705186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705208 : List Nat := [2, 1, 2, 1, 1, 1, 2, 13]
def baseStart_7705208 : Nat := 118140960795 + 7705208 * 2 ^ 59
def prefixEnd_7705208 : Nat := 4983230072969 + 3 ^ 40 * 7705208 * 2
def baseEnd_7705208 : Nat := 146536120254392391554237

theorem tailTrace_7705208 : CollatzResearch.WordTrace tailWord_7705208 prefixEnd_7705208 146536120254392391554237 := by
  unfold tailWord_7705208
  simp only [CollatzResearch.WordTrace]
  refine ⟨140516011734677417801898139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187354682312903223735864185 140516011734677417801898139)
  ·
    refine ⟨210774017602016126702847209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140516011734677417801898139 210774017602016126702847209)
    ·
      refine ⟨158080513201512095027135407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210774017602016126702847209 158080513201512095027135407)
      ·
        refine ⟨237120769802268142540703111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158080513201512095027135407 237120769802268142540703111)
        ·
          refine ⟨355681154703402213811054667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237120769802268142540703111 355681154703402213811054667)
          ·
            refine ⟨533521732055103320716582001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355681154703402213811054667 533521732055103320716582001)
            ·
              refine ⟨400141299041327490537436501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533521732055103320716582001 400141299041327490537436501)
              ·
                refine ⟨146536120254392391554237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 400141299041327490537436501 146536120254392391554237)
                ·
                  rfl

theorem cell23_7705208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 13].length) (baseStart_7705208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705208 prefixEnd_7705208 := by exact prefixLift 7705208
  have htrace : WordTrace (prefixWord ++ tailWord_7705208) baseStart_7705208 baseEnd_7705208 := by
    simpa [prefixWord, tailWord_7705208, baseEnd_7705208] using wordTrace_append hprefix tailTrace_7705208
  have hstable : (prefixWord ++ tailWord_7705208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705208).length < 2 ^ (prefixWord ++ tailWord_7705208).sum := by decide
  have hdescent : baseEnd_7705208 < baseStart_7705208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705213 : List Nat := [1, 4, 1, 1, 5, 2, 1, 3, 1, 1, 3]
def baseStart_7705213 : Nat := 118140960795 + 7705213 * 2 ^ 59
def prefixEnd_7705213 : Nat := 4983230072969 + 3 ^ 40 * 7705213 * 2
def baseEnd_7705213 : Nat := 3956477814271867052401877

theorem tailTrace_7705213 : CollatzResearch.WordTrace tailWord_7705213 prefixEnd_7705213 3956477814271867052401877 := by
  unfold tailWord_7705213
  simp only [CollatzResearch.WordTrace]
  refine ⟨281032205834336721457728293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187354803889557814305152195 281032205834336721457728293)
  ·
    refine ⟨52693538593938135273324055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281032205834336721457728293 52693538593938135273324055)
    ·
      refine ⟨79040307890907202909986083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52693538593938135273324055 79040307890907202909986083)
      ·
        refine ⟨118560461836360804364979125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79040307890907202909986083 118560461836360804364979125)
        ·
          refine ⟨11115043297158825409216793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118560461836360804364979125 11115043297158825409216793)
          ·
            refine ⟨8336282472869119056912595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11115043297158825409216793 8336282472869119056912595)
            ·
              refine ⟨12504423709303678585368893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336282472869119056912595 12504423709303678585368893)
              ·
                refine ⟨4689158890988879469513335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12504423709303678585368893 4689158890988879469513335)
                ·
                  refine ⟨7033738336483319204270003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689158890988879469513335 7033738336483319204270003)
                  ·
                    refine ⟨10550607504724978806405005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7033738336483319204270003 10550607504724978806405005)
                    ·
                      refine ⟨3956477814271867052401877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10550607504724978806405005 3956477814271867052401877)
                      ·
                        rfl

theorem cell23_7705213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_7705213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705213 prefixEnd_7705213 := by exact prefixLift 7705213
  have htrace : WordTrace (prefixWord ++ tailWord_7705213) baseStart_7705213 baseEnd_7705213 := by
    simpa [prefixWord, tailWord_7705213, baseEnd_7705213] using wordTrace_append hprefix tailTrace_7705213
  have hstable : (prefixWord ++ tailWord_7705213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705213).length < 2 ^ (prefixWord ++ tailWord_7705213).sum := by decide
  have hdescent : baseEnd_7705213 < baseStart_7705213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705235 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 3]
def baseStart_7705235 : Nat := 118140960795 + 7705235 * 2 ^ 59
def prefixEnd_7705235 : Nat := 4983230072969 + 3 ^ 40 * 7705235 * 2
def baseEnd_7705235 : Nat := 3956489110846265966326775

theorem tailTrace_7705235 : CollatzResearch.WordTrace tailWord_7705235 prefixEnd_7705235 3956489110846265966326775 := by
  unfold tailWord_7705235
  simp only [CollatzResearch.WordTrace]
  refine ⟨281033008240257019215029159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187355338826838012810019439 281033008240257019215029159)
  ·
    refine ⟨421549512360385528822543739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281033008240257019215029159 421549512360385528822543739)
    ·
      refine ⟨632324268540578293233815609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421549512360385528822543739 632324268540578293233815609)
      ·
        refine ⟨474243201405433719925361707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632324268540578293233815609 474243201405433719925361707)
        ·
          refine ⟨711364802108150579888042561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474243201405433719925361707 711364802108150579888042561)
          ·
            refine ⟨533523601581112934916031921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711364802108150579888042561 533523601581112934916031921)
            ·
              refine ⟨400142701185834701187023941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533523601581112934916031921 400142701185834701187023941)
              ·
                refine ⟨75026756472344006472566989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400142701185834701187023941 75026756472344006472566989)
                ·
                  refine ⟨28135033677129002427212621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75026756472344006472566989 28135033677129002427212621)
                  ·
                    refine ⟨10550637628923375910204733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28135033677129002427212621 10550637628923375910204733)
                    ·
                      refine ⟨3956489110846265966326775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10550637628923375910204733 3956489110846265966326775)
                      ·
                        rfl

theorem cell23_7705235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 3].length) (baseStart_7705235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705235 prefixEnd_7705235 := by exact prefixLift 7705235
  have htrace : WordTrace (prefixWord ++ tailWord_7705235) baseStart_7705235 baseEnd_7705235 := by
    simpa [prefixWord, tailWord_7705235, baseEnd_7705235] using wordTrace_append hprefix tailTrace_7705235
  have hstable : (prefixWord ++ tailWord_7705235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705235).length < 2 ^ (prefixWord ++ tailWord_7705235).sum := by decide
  have hdescent : baseEnd_7705235 < baseStart_7705235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705252 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_7705252 : Nat := 118140960795 + 7705252 * 2 ^ 59
def prefixEnd_7705252 : Nat := 4983230072969 + 3 ^ 40 * 7705252 * 2
def baseEnd_7705252 : Nat := 3956497840017392399814197

theorem tailTrace_7705252 : CollatzResearch.WordTrace tailWord_7705252 prefixEnd_7705252 3956497840017392399814197 := by
  unfold tailWord_7705252
  simp only [CollatzResearch.WordTrace]
  refine ⟨140516814140597715559199005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187355752187463620745598673 140516814140597715559199005)
  ·
    refine ⟨52693805302724143334699627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140516814140597715559199005 52693805302724143334699627)
    ·
      refine ⟨79040707954086215002049441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52693805302724143334699627 79040707954086215002049441)
      ·
        refine ⟨59280530965564661251537081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79040707954086215002049441 59280530965564661251537081)
        ·
          refine ⟨44460398224173495938652811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59280530965564661251537081 44460398224173495938652811)
          ·
            refine ⟨66690597336260243907979217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44460398224173495938652811 66690597336260243907979217)
            ·
              refine ⟨50017948002195182930984413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66690597336260243907979217 50017948002195182930984413)
              ·
                refine ⟨18756730500823193599119155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50017948002195182930984413 18756730500823193599119155)
                ·
                  refine ⟨28135095751234790398678733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18756730500823193599119155 28135095751234790398678733)
                  ·
                    refine ⟨10550660906713046399504525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28135095751234790398678733 10550660906713046399504525)
                    ·
                      refine ⟨3956497840017392399814197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10550660906713046399504525 3956497840017392399814197)
                      ·
                        rfl

theorem cell23_7705252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_7705252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705252 prefixEnd_7705252 := by exact prefixLift 7705252
  have htrace : WordTrace (prefixWord ++ tailWord_7705252) baseStart_7705252 baseEnd_7705252 := by
    simpa [prefixWord, tailWord_7705252, baseEnd_7705252] using wordTrace_append hprefix tailTrace_7705252
  have hstable : (prefixWord ++ tailWord_7705252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705252).length < 2 ^ (prefixWord ++ tailWord_7705252).sum := by decide
  have hdescent : baseEnd_7705252 < baseStart_7705252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705269 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_7705269 : Nat := 118140960795 + 7705269 * 2 ^ 59
def prefixEnd_7705269 : Nat := 4983230072969 + 3 ^ 40 * 7705269 * 2
def baseEnd_7705269 : Nat := 3956506569188518833301619

theorem tailTrace_7705269 : CollatzResearch.WordTrace tailWord_7705269 prefixEnd_7705269 3956506569188518833301619 := by
  unfold tailWord_7705269
  simp only [CollatzResearch.WordTrace]
  refine ⟨281034248322133843021766861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187356165548089228681177907 281034248322133843021766861)
  ·
    refine ⟨105387843120800191133162573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281034248322133843021766861 105387843120800191133162573)
    ·
      refine ⟨39520441170300071674935965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105387843120800191133162573 39520441170300071674935965)
      ·
        refine ⟨14820165438862526878100987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39520441170300071674935965 14820165438862526878100987)
        ·
          refine ⟨22230248158293790317151481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14820165438862526878100987 22230248158293790317151481)
          ·
            refine ⟨16672686118720342737863611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22230248158293790317151481 16672686118720342737863611)
            ·
              refine ⟨25009029178080514106795417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16672686118720342737863611 25009029178080514106795417)
              ·
                refine ⟨18756771883560385580096563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25009029178080514106795417 18756771883560385580096563)
                ·
                  refine ⟨28135157825340578370144845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18756771883560385580096563 28135157825340578370144845)
                  ·
                    refine ⟨10550684184502716888804317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28135157825340578370144845 10550684184502716888804317)
                    ·
                      refine ⟨3956506569188518833301619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10550684184502716888804317 3956506569188518833301619)
                      ·
                        rfl

theorem cell23_7705269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_7705269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705269 prefixEnd_7705269 := by exact prefixLift 7705269
  have htrace : WordTrace (prefixWord ++ tailWord_7705269) baseStart_7705269 baseEnd_7705269 := by
    simpa [prefixWord, tailWord_7705269, baseEnd_7705269] using wordTrace_append hprefix tailTrace_7705269
  have hstable : (prefixWord ++ tailWord_7705269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705269).length < 2 ^ (prefixWord ++ tailWord_7705269).sum := by decide
  have hdescent : baseEnd_7705269 < baseStart_7705269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705292 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_7705292 : Nat := 118140960795 + 7705292 * 2 ^ 59
def prefixEnd_7705292 : Nat := 4983230072969 + 3 ^ 40 * 7705292 * 2
def baseEnd_7705292 : Nat := 3956518379243572243314013

theorem tailTrace_7705292 : CollatzResearch.WordTrace tailWord_7705292 prefixEnd_7705292 3956518379243572243314013 := by
  unfold tailWord_7705292
  simp only [CollatzResearch.WordTrace]
  refine ⟨140517543600525258974927065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187356724800700345299902753 140517543600525258974927065)
  ·
    refine ⟨105388157700393944231195299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140517543600525258974927065 105388157700393944231195299)
    ·
      refine ⟨158082236550590916346792949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105388157700393944231195299 158082236550590916346792949)
      ·
        refine ⟨14820209676617898407511839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158082236550590916346792949 14820209676617898407511839)
        ·
          refine ⟨22230314514926847611267759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14820209676617898407511839 22230314514926847611267759)
          ·
            refine ⟨33345471772390271416901639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22230314514926847611267759 33345471772390271416901639)
            ·
              refine ⟨50018207658585407125352459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33345471772390271416901639 50018207658585407125352459)
              ·
                refine ⟨75027311487878110688028689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50018207658585407125352459 75027311487878110688028689)
                ·
                  refine ⟨56270483615908583016021517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75027311487878110688028689 56270483615908583016021517)
                  ·
                    refine ⟨21101431355965718631008069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56270483615908583016021517 21101431355965718631008069)
                    ·
                      refine ⟨3956518379243572243314013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21101431355965718631008069 3956518379243572243314013)
                      ·
                        rfl

theorem cell23_7705292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_7705292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705292 prefixEnd_7705292 := by exact prefixLift 7705292
  have htrace : WordTrace (prefixWord ++ tailWord_7705292) baseStart_7705292 baseEnd_7705292 := by
    simpa [prefixWord, tailWord_7705292, baseEnd_7705292] using wordTrace_append hprefix tailTrace_7705292
  have hstable : (prefixWord ++ tailWord_7705292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705292).length < 2 ^ (prefixWord ++ tailWord_7705292).sum := by decide
  have hdescent : baseEnd_7705292 < baseStart_7705292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705355 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 7]
def baseStart_7705355 : Nat := 118140960795 + 7705355 * 2 ^ 59
def prefixEnd_7705355 : Nat := 4983230072969 + 3 ^ 40 * 7705355 * 2
def baseEnd_7705355 : Nat := 3956550728524805496826223

theorem tailTrace_7705355 : CollatzResearch.WordTrace tailWord_7705355 prefixEnd_7705355 3956550728524805496826223 := by
  unfold tailWord_7705355
  simp only [CollatzResearch.WordTrace]
  refine ⟨281037384999822279709397519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187358256666548186472931679 281037384999822279709397519)
  ·
    refine ⟨421556077499733419564096279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281037384999822279709397519 421556077499733419564096279)
    ·
      refine ⟨632334116249600129346144419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421556077499733419564096279 632334116249600129346144419)
      ·
        refine ⟨948501174374400194019216629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632334116249600129346144419 948501174374400194019216629)
        ·
          refine ⟨88921985097600018189301559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 948501174374400194019216629 88921985097600018189301559)
          ·
            refine ⟨133382977646400027283952339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88921985097600018189301559 133382977646400027283952339)
            ·
              refine ⟨200074466469600040925928509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133382977646400027283952339 200074466469600040925928509)
              ·
                refine ⟨75027924926100015347223191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200074466469600040925928509 75027924926100015347223191)
                ·
                  refine ⟨112541887389150023020834787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75027924926100015347223191 112541887389150023020834787)
                  ·
                    refine ⟨168812831083725034531252181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112541887389150023020834787 168812831083725034531252181)
                    ·
                      refine ⟨3956550728524805496826223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168812831083725034531252181 3956550728524805496826223)
                      ·
                        rfl

theorem cell23_7705355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_7705355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705355 prefixEnd_7705355 := by exact prefixLift 7705355
  have htrace : WordTrace (prefixWord ++ tailWord_7705355) baseStart_7705355 baseEnd_7705355 := by
    simpa [prefixWord, tailWord_7705355, baseEnd_7705355] using wordTrace_append hprefix tailTrace_7705355
  have hstable : (prefixWord ++ tailWord_7705355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705355).length < 2 ^ (prefixWord ++ tailWord_7705355).sum := by decide
  have hdescent : baseEnd_7705355 < baseStart_7705355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705392 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 5, 4]
def baseStart_7705392 : Nat := 118140960795 + 7705392 * 2 ^ 59
def prefixEnd_7705392 : Nat := 4983230072969 + 3 ^ 40 * 7705392 * 2
def baseEnd_7705392 : Nat := 1318856575769673950687851

theorem tailTrace_7705392 : CollatzResearch.WordTrace tailWord_7705392 prefixEnd_7705392 1318856575769673950687851 := by
  unfold tailWord_7705392
  simp only [CollatzResearch.WordTrace]
  refine ⟨140519367250344117514247215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187359156333792156685662953 140519367250344117514247215)
  ·
    refine ⟨210779050875516176271370823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140519367250344117514247215 210779050875516176271370823)
    ·
      refine ⟨316168576313274264407056235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210779050875516176271370823 316168576313274264407056235)
      ·
        refine ⟨474252864469911396610584353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316168576313274264407056235 474252864469911396610584353)
        ·
          refine ⟨355689648352433547457938265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474252864469911396610584353 355689648352433547457938265)
          ·
            refine ⟨266767236264325160593453699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355689648352433547457938265 266767236264325160593453699)
            ·
              refine ⟨400150854396487740890180549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266767236264325160593453699 400150854396487740890180549)
              ·
                refine ⟨75028285199341451416908853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400150854396487740890180549 75028285199341451416908853)
                ·
                  refine ⟨7033901737438261070335205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75028285199341451416908853 7033901737438261070335205)
                  ·
                    refine ⟨1318856575769673950687851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7033901737438261070335205 1318856575769673950687851)
                    ·
                      rfl

theorem cell23_7705392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 5, 4].length) (baseStart_7705392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705392 prefixEnd_7705392 := by exact prefixLift 7705392
  have htrace : WordTrace (prefixWord ++ tailWord_7705392) baseStart_7705392 baseEnd_7705392 := by
    simpa [prefixWord, tailWord_7705392, baseEnd_7705392] using wordTrace_append hprefix tailTrace_7705392
  have hstable : (prefixWord ++ tailWord_7705392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705392).length < 2 ^ (prefixWord ++ tailWord_7705392).sum := by decide
  have hdescent : baseEnd_7705392 < baseStart_7705392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705396 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_7705396 : Nat := 118140960795 + 7705396 * 2 ^ 59
def prefixEnd_7705396 : Nat := 4983230072969 + 3 ^ 40 * 7705396 * 2
def baseEnd_7705396 : Nat := 1318857260410546612137845

theorem tailTrace_7705396 : CollatzResearch.WordTrace tailWord_7705396 prefixEnd_7705396 1318857260410546612137845 := by
  unfold tailWord_7705396
  simp only [CollatzResearch.WordTrace]
  refine ⟨140519440196336871855820021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187359253595115829141093361 140519440196336871855820021)
  ·
    refine ⟨13173697518406581736483127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140519440196336871855820021 13173697518406581736483127)
    ·
      refine ⟨19760546277609872604724691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13173697518406581736483127 19760546277609872604724691)
      ·
        refine ⟨29640819416414808907087037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19760546277609872604724691 29640819416414808907087037)
        ·
          refine ⟨11115307281155553340157639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29640819416414808907087037 11115307281155553340157639)
          ·
            refine ⟨16672960921733330010236459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11115307281155553340157639 16672960921733330010236459)
            ·
              refine ⟨25009441382599995015354689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16672960921733330010236459 25009441382599995015354689)
              ·
                refine ⟨18757081036949996261516017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25009441382599995015354689 18757081036949996261516017)
                ·
                  refine ⟨14067810777712497196137013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18757081036949996261516017 14067810777712497196137013)
                  ·
                    refine ⟨1318857260410546612137845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14067810777712497196137013 1318857260410546612137845)
                    ·
                      rfl

theorem cell23_7705396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_7705396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705396 prefixEnd_7705396 := by exact prefixLift 7705396
  have htrace : WordTrace (prefixWord ++ tailWord_7705396) baseStart_7705396 baseEnd_7705396 := by
    simpa [prefixWord, tailWord_7705396, baseEnd_7705396] using wordTrace_append hprefix tailTrace_7705396
  have hstable : (prefixWord ++ tailWord_7705396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705396).length < 2 ^ (prefixWord ++ tailWord_7705396).sum := by decide
  have hdescent : baseEnd_7705396 < baseStart_7705396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705432 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 2, 5, 3]
def baseStart_7705432 : Nat := 118140960795 + 7705432 * 2 ^ 59
def prefixEnd_7705432 : Nat := 4983230072969 + 3 ^ 40 * 7705432 * 2
def baseEnd_7705432 : Nat := 3956590266535201695563369

theorem tailTrace_7705432 : CollatzResearch.WordTrace tailWord_7705432 prefixEnd_7705432 3956590266535201695563369 := by
  unfold tailWord_7705432
  simp only [CollatzResearch.WordTrace]
  refine ⟨140520096710271660929975275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187360128947028881239967033 140520096710271660929975275)
  ·
    refine ⟨210780145065407491394962913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140520096710271660929975275 210780145065407491394962913)
    ·
      refine ⟨158085108799055618546222185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210780145065407491394962913 158085108799055618546222185)
      ·
        refine ⟨118563831599291713909666639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158085108799055618546222185 118563831599291713909666639)
        ·
          refine ⟨177845747398937570864499959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118563831599291713909666639 177845747398937570864499959)
          ·
            refine ⟨266768621098406356296749939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177845747398937570864499959 266768621098406356296749939)
            ·
              refine ⟨400152931647609534445124909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266768621098406356296749939 400152931647609534445124909)
              ·
                refine ⟨150057349367853575416921841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400152931647609534445124909 150057349367853575416921841)
                ·
                  refine ⟨112543012025890181562691381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150057349367853575416921841 112543012025890181562691381)
                  ·
                    refine ⟨10550907377427204521502317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112543012025890181562691381 10550907377427204521502317)
                    ·
                      refine ⟨3956590266535201695563369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10550907377427204521502317 3956590266535201695563369)
                      ·
                        rfl

theorem cell23_7705432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_7705432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705432 prefixEnd_7705432 := by exact prefixLift 7705432
  have htrace : WordTrace (prefixWord ++ tailWord_7705432) baseStart_7705432 baseEnd_7705432 := by
    simpa [prefixWord, tailWord_7705432, baseEnd_7705432] using wordTrace_append hprefix tailTrace_7705432
  have hstable : (prefixWord ++ tailWord_7705432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705432).length < 2 ^ (prefixWord ++ tailWord_7705432).sum := by decide
  have hdescent : baseEnd_7705432 < baseStart_7705432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705436 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_7705436 : Nat := 118140960795 + 7705436 * 2 ^ 59
def prefixEnd_7705436 : Nat := 4983230072969 + 3 ^ 40 * 7705436 * 2
def baseEnd_7705436 : Nat := 3956592320457819679913351

theorem tailTrace_7705436 : CollatzResearch.WordTrace tailWord_7705436 prefixEnd_7705436 3956592320457819679913351 := by
  unfold tailWord_7705436
  simp only [CollatzResearch.WordTrace]
  refine ⟨140520169656264415271548081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187360226208352553695397441 140520169656264415271548081)
  ·
    refine ⟨105390127242198311453661061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140520169656264415271548081 105390127242198311453661061)
    ·
      refine ⟨19760648857912183397561449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105390127242198311453661061 19760648857912183397561449)
      ·
        refine ⟨14820486643434137548171087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19760648857912183397561449 14820486643434137548171087)
        ·
          refine ⟨22230729965151206322256631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14820486643434137548171087 22230729965151206322256631)
          ·
            refine ⟨33346094947726809483384947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22230729965151206322256631 33346094947726809483384947)
            ·
              refine ⟨50019142421590214225077421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33346094947726809483384947 50019142421590214225077421)
              ·
                refine ⟨18757178408096330334404033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50019142421590214225077421 18757178408096330334404033)
                ·
                  refine ⟨14067883806072247750803025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18757178408096330334404033 14067883806072247750803025)
                  ·
                    refine ⟨10550912854554185813102269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14067883806072247750803025 10550912854554185813102269)
                    ·
                      refine ⟨3956592320457819679913351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10550912854554185813102269 3956592320457819679913351)
                      ·
                        rfl

theorem cell23_7705436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_7705436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705436 prefixEnd_7705436 := by exact prefixLift 7705436
  have htrace : WordTrace (prefixWord ++ tailWord_7705436) baseStart_7705436 baseEnd_7705436 := by
    simpa [prefixWord, tailWord_7705436, baseEnd_7705436] using wordTrace_append hprefix tailTrace_7705436
  have hstable : (prefixWord ++ tailWord_7705436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705436).length < 2 ^ (prefixWord ++ tailWord_7705436).sum := by decide
  have hdescent : baseEnd_7705436 < baseStart_7705436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705489 : List Nat := [1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 4]
def baseStart_7705489 : Nat := 118140960795 + 7705489 * 2 ^ 59
def prefixEnd_7705489 : Nat := 4983230072969 + 3 ^ 40 * 7705489 * 2
def baseEnd_7705489 : Nat := 3956619534932507972550607

theorem tailTrace_7705489 : CollatzResearch.WordTrace tailWord_7705489 prefixEnd_7705489 3956619534932507972550607 := by
  unfold tailWord_7705489
  simp only [CollatzResearch.WordTrace]
  refine ⟨281042272381336820594775521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187361514920891213729850347 281042272381336820594775521)
  ·
    refine ⟨210781704286002615446081641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281042272381336820594775521 210781704286002615446081641)
    ·
      refine ⟨158086278214501961584561231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210781704286002615446081641 158086278214501961584561231)
      ·
        refine ⟨237129417321752942376841847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158086278214501961584561231 237129417321752942376841847)
        ·
          refine ⟨355694125982629413565262771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237129417321752942376841847 355694125982629413565262771)
          ·
            refine ⟨533541188973944120347894157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355694125982629413565262771 533541188973944120347894157)
            ·
              refine ⟨200077945865229045130460309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 533541188973944120347894157 200077945865229045130460309)
              ·
                refine ⟨9378653712432611490490327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 200077945865229045130460309 9378653712432611490490327)
                ·
                  refine ⟨14067980568648917235735491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9378653712432611490490327 14067980568648917235735491)
                  ·
                    refine ⟨21101970852973375853603237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14067980568648917235735491 21101970852973375853603237)
                    ·
                      refine ⟨3956619534932507972550607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21101970852973375853603237 3956619534932507972550607)
                      ·
                        rfl

theorem cell23_7705489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_7705489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705489 prefixEnd_7705489 := by exact prefixLift 7705489
  have htrace : WordTrace (prefixWord ++ tailWord_7705489) baseStart_7705489 baseEnd_7705489 := by
    simpa [prefixWord, tailWord_7705489, baseEnd_7705489] using wordTrace_append hprefix tailTrace_7705489
  have hstable : (prefixWord ++ tailWord_7705489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705489).length < 2 ^ (prefixWord ++ tailWord_7705489).sum := by decide
  have hdescent : baseEnd_7705489 < baseStart_7705489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705493 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 2, 3, 2]
def baseStart_7705493 : Nat := 118140960795 + 7705493 * 2 ^ 59
def prefixEnd_7705493 : Nat := 4983230072969 + 3 ^ 40 * 7705493 * 2
def baseEnd_7705493 : Nat := 3956621588855125956900589

theorem tailTrace_7705493 : CollatzResearch.WordTrace tailWord_7705493 prefixEnd_7705493 3956621588855125956900589 := by
  unfold tailWord_7705493
  simp only [CollatzResearch.WordTrace]
  refine ⟨281042418273322329277921133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187361612182214886185280755 281042418273322329277921133)
  ·
    refine ⟨105390906852495873479220425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281042418273322329277921133 105390906852495873479220425)
    ·
      refine ⟨79043180139371905109415319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105390906852495873479220425 79043180139371905109415319)
      ·
        refine ⟨118564770209057857664122979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79043180139371905109415319 118564770209057857664122979)
        ·
          refine ⟨177847155313586786496184469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118564770209057857664122979 177847155313586786496184469)
          ·
            refine ⟨8336585405324380617008647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177847155313586786496184469 8336585405324380617008647)
            ·
              refine ⟨12504878107986570925512971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336585405324380617008647 12504878107986570925512971)
              ·
                refine ⟨18757317161979856388269457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12504878107986570925512971 18757317161979856388269457)
                ·
                  refine ⟨14067987871484892291202093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18757317161979856388269457 14067987871484892291202093)
                  ·
                    refine ⟨5275495451806834609200785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14067987871484892291202093 5275495451806834609200785)
                    ·
                      refine ⟨3956621588855125956900589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5275495451806834609200785 3956621588855125956900589)
                      ·
                        rfl

theorem cell23_7705493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_7705493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705493 prefixEnd_7705493 := by exact prefixLift 7705493
  have htrace : WordTrace (prefixWord ++ tailWord_7705493) baseStart_7705493 baseEnd_7705493 := by
    simpa [prefixWord, tailWord_7705493, baseEnd_7705493] using wordTrace_append hprefix tailTrace_7705493
  have hstable : (prefixWord ++ tailWord_7705493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705493).length < 2 ^ (prefixWord ++ tailWord_7705493).sum := by decide
  have hdescent : baseEnd_7705493 < baseStart_7705493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705503 : List Nat := [1, 1, 2, 5, 2, 3, 2, 1, 1, 5]
def baseStart_7705503 : Nat := 118140960795 + 7705503 * 2 ^ 59
def prefixEnd_7705503 : Nat := 4983230072969 + 3 ^ 40 * 7705503 * 2
def baseEnd_7705503 : Nat := 1318875574553890305925181

theorem tailTrace_7705503 : CollatzResearch.WordTrace tailWord_7705503 prefixEnd_7705503 1318875574553890305925181 := by
  unfold tailWord_7705503
  simp only [CollatzResearch.WordTrace]
  refine ⟨281042783003286100985785163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187361855335524067323856775 281042783003286100985785163)
  ·
    refine ⟨421564174504929151478677745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281042783003286100985785163 421564174504929151478677745)
    ·
      refine ⟨316173130878696863609008309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421564174504929151478677745 316173130878696863609008309)
      ·
        refine ⟨29641231019877830963344529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 316173130878696863609008309 29641231019877830963344529)
        ·
          refine ⟨22230923264908373222508397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29641231019877830963344529 22230923264908373222508397)
          ·
            refine ⟨8336596224340639958440649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22230923264908373222508397 8336596224340639958440649)
            ·
              refine ⟨6252447168255479968830487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8336596224340639958440649 6252447168255479968830487)
              ·
                refine ⟨9378670752383219953245731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6252447168255479968830487 9378670752383219953245731)
                ·
                  refine ⟨14068006128574829929868597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9378670752383219953245731 14068006128574829929868597)
                  ·
                    refine ⟨1318875574553890305925181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14068006128574829929868597 1318875574553890305925181)
                    ·
                      rfl

theorem cell23_7705503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 1, 5].length) (baseStart_7705503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705503 prefixEnd_7705503 := by exact prefixLift 7705503
  have htrace : WordTrace (prefixWord ++ tailWord_7705503) baseStart_7705503 baseEnd_7705503 := by
    simpa [prefixWord, tailWord_7705503, baseEnd_7705503] using wordTrace_append hprefix tailTrace_7705503
  have hstable : (prefixWord ++ tailWord_7705503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705503).length < 2 ^ (prefixWord ++ tailWord_7705503).sum := by decide
  have hdescent : baseEnd_7705503 < baseStart_7705503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705522 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_7705522 : Nat := 118140960795 + 7705522 * 2 ^ 59
def prefixEnd_7705522 : Nat := 4983230072969 + 3 ^ 40 * 7705522 * 2
def baseEnd_7705522 : Nat := 3956636479794106343437955

theorem tailTrace_7705522 : CollatzResearch.WordTrace tailWord_7705522 prefixEnd_7705522 3956636479794106343437955 := by
  unfold tailWord_7705522
  simp only [CollatzResearch.WordTrace]
  refine ⟨70260868997554316807681705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187362317326811511487151213 70260868997554316807681705)
  ·
    refine ⟨52695651748165737605761279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70260868997554316807681705 52695651748165737605761279)
    ·
      refine ⟨79043477622248606408641919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52695651748165737605761279 79043477622248606408641919)
      ·
        refine ⟨118565216433372909612962879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79043477622248606408641919 118565216433372909612962879)
        ·
          refine ⟨177847824650059364419444319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118565216433372909612962879 177847824650059364419444319)
          ·
            refine ⟨266771736975089046629166479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177847824650059364419444319 266771736975089046629166479)
            ·
              refine ⟨400157605462633569943749719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266771736975089046629166479 400157605462633569943749719)
              ·
                refine ⟨600236408193950354915624579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400157605462633569943749719 600236408193950354915624579)
                ·
                  refine ⟨900354612290925532373436869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600236408193950354915624579 900354612290925532373436869)
                  ·
                    refine ⟨168816489804548537320019413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 900354612290925532373436869 168816489804548537320019413)
                    ·
                      refine ⟨3956636479794106343437955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168816489804548537320019413 3956636479794106343437955)
                      ·
                        rfl

theorem cell23_7705522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_7705522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705522 prefixEnd_7705522 := by exact prefixLift 7705522
  have htrace : WordTrace (prefixWord ++ tailWord_7705522) baseStart_7705522 baseEnd_7705522 := by
    simpa [prefixWord, tailWord_7705522, baseEnd_7705522] using wordTrace_append hprefix tailTrace_7705522
  have hstable : (prefixWord ++ tailWord_7705522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705522).length < 2 ^ (prefixWord ++ tailWord_7705522).sum := by decide
  have hdescent : baseEnd_7705522 < baseStart_7705522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705533 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_7705533 : Nat := 118140960795 + 7705533 * 2 ^ 59
def prefixEnd_7705533 : Nat := 4983230072969 + 3 ^ 40 * 7705533 * 2
def baseEnd_7705533 : Nat := 1318880709360435266800135

theorem tailTrace_7705533 : CollatzResearch.WordTrace tailWord_7705533 prefixEnd_7705533 1318880709360435266800135 := by
  unfold tailWord_7705533
  simp only [CollatzResearch.WordTrace]
  refine ⟨281043877193177416109377253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187362584795451610739584835 281043877193177416109377253)
  ·
    refine ⟨52695726973720765520508235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281043877193177416109377253 52695726973720765520508235)
    ·
      refine ⟨79043590460581148280762353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52695726973720765520508235 79043590460581148280762353)
      ·
        refine ⟨59282692845435861210571765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79043590460581148280762353 59282692845435861210571765)
        ·
          refine ⟨5557752454259611988491103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59282692845435861210571765 5557752454259611988491103)
          ·
            refine ⟨8336628681389417982736655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5557752454259611988491103 8336628681389417982736655)
            ·
              refine ⟨12504943022084126974104983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336628681389417982736655 12504943022084126974104983)
              ·
                refine ⟨18757414533126190461157475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12504943022084126974104983 18757414533126190461157475)
                ·
                  refine ⟨28136121799689285691736213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18757414533126190461157475 28136121799689285691736213)
                  ·
                    refine ⟨1318880709360435266800135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28136121799689285691736213 1318880709360435266800135)
                    ·
                      rfl

theorem cell23_7705533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_7705533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705533 prefixEnd_7705533 := by exact prefixLift 7705533
  have htrace : WordTrace (prefixWord ++ tailWord_7705533) baseStart_7705533 baseEnd_7705533 := by
    simpa [prefixWord, tailWord_7705533, baseEnd_7705533] using wordTrace_append hprefix tailTrace_7705533
  have hstable : (prefixWord ++ tailWord_7705533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705533).length < 2 ^ (prefixWord ++ tailWord_7705533).sum := by decide
  have hdescent : baseEnd_7705533 < baseStart_7705533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705536 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 4]
def baseStart_7705536 : Nat := 118140960795 + 7705536 * 2 ^ 59
def prefixEnd_7705536 : Nat := 4983230072969 + 3 ^ 40 * 7705536 * 2
def baseEnd_7705536 : Nat := 3956643668523269288662891

theorem tailTrace_7705536 : CollatzResearch.WordTrace tailWord_7705536 prefixEnd_7705536 3956643668523269288662891 := by
  unfold tailWord_7705536
  simp only [CollatzResearch.WordTrace]
  refine ⟨140521993306083273810868231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187362657741444365081157641 140521993306083273810868231)
  ·
    refine ⟨210782989959124910716302347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140521993306083273810868231 210782989959124910716302347)
    ·
      refine ⟨316174484938687366074453521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210782989959124910716302347 316174484938687366074453521)
      ·
        refine ⟨237130863704015524555840141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316174484938687366074453521 237130863704015524555840141)
        ·
          refine ⟨88924073889005821708440053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237130863704015524555840141 88924073889005821708440053)
          ·
            refine ⟨8336631927094295785166255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88924073889005821708440053 8336631927094295785166255)
            ·
              refine ⟨12504947890641443677749383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336631927094295785166255 12504947890641443677749383)
              ·
                refine ⟨18757421835962165516624075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12504947890641443677749383 18757421835962165516624075)
                ·
                  refine ⟨28136132753943248274936113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18757421835962165516624075 28136132753943248274936113)
                  ·
                    refine ⟨21102099565457436206202085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28136132753943248274936113 21102099565457436206202085)
                    ·
                      refine ⟨3956643668523269288662891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21102099565457436206202085 3956643668523269288662891)
                      ·
                        rfl

theorem cell23_7705536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_7705536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705536 prefixEnd_7705536 := by exact prefixLift 7705536
  have htrace : WordTrace (prefixWord ++ tailWord_7705536) baseStart_7705536 baseEnd_7705536 := by
    simpa [prefixWord, tailWord_7705536, baseEnd_7705536] using wordTrace_append hprefix tailTrace_7705536
  have hstable : (prefixWord ++ tailWord_7705536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705536).length < 2 ^ (prefixWord ++ tailWord_7705536).sum := by decide
  have hdescent : baseEnd_7705536 < baseStart_7705536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705540 : List Nat := [2, 3, 3, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_7705540 : Nat := 118140960795 + 7705540 * 2 ^ 59
def prefixEnd_7705540 : Nat := 4983230072969 + 3 ^ 40 * 7705540 * 2
def baseEnd_7705540 : Nat := 3956645722445887273012873

theorem tailTrace_7705540 : CollatzResearch.WordTrace tailWord_7705540 prefixEnd_7705540 3956645722445887273012873 := by
  unfold tailWord_7705540
  simp only [CollatzResearch.WordTrace]
  refine ⟨140522066252076028152441037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187362755002768037536588049 140522066252076028152441037)
  ·
    refine ⟨52695774844528510557165389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140522066252076028152441037 52695774844528510557165389)
    ·
      refine ⟨19760915566698191458937021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52695774844528510557165389 19760915566698191458937021)
      ·
        refine ⟨7410343337511821797101383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19760915566698191458937021 7410343337511821797101383)
        ·
          refine ⟨11115515006267732695652075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7410343337511821797101383 11115515006267732695652075)
          ·
            refine ⟨16673272509401599043478113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11115515006267732695652075 16673272509401599043478113)
            ·
              refine ⟨12504954382051199282608585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16673272509401599043478113 12504954382051199282608585)
              ·
                refine ⟨9378715786538399461956439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12504954382051199282608585 9378715786538399461956439)
                ·
                  refine ⟨14068073679807599192934659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9378715786538399461956439 14068073679807599192934659)
                  ·
                    refine ⟨21102110519711398789401989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14068073679807599192934659 21102110519711398789401989)
                    ·
                      refine ⟨3956645722445887273012873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21102110519711398789401989 3956645722445887273012873)
                      ·
                        rfl

theorem cell23_7705540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_7705540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705540 prefixEnd_7705540 := by exact prefixLift 7705540
  have htrace : WordTrace (prefixWord ++ tailWord_7705540) baseStart_7705540 baseEnd_7705540 := by
    simpa [prefixWord, tailWord_7705540, baseEnd_7705540] using wordTrace_append hprefix tailTrace_7705540
  have hstable : (prefixWord ++ tailWord_7705540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705540).length < 2 ^ (prefixWord ++ tailWord_7705540).sum := by decide
  have hdescent : baseEnd_7705540 < baseStart_7705540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705590 : List Nat := [5, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_7705590 : Nat := 118140960795 + 7705590 * 2 ^ 59
def prefixEnd_7705590 : Nat := 4983230072969 + 3 ^ 40 * 7705590 * 2
def baseEnd_7705590 : Nat := 3956671396478612077387643

theorem tailTrace_7705590 : CollatzResearch.WordTrace tailWord_7705590 prefixEnd_7705590 3956671396478612077387643 := by
  unfold tailWord_7705590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17565372259623182177762639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187363970769313943229468149 17565372259623182177762639)
  ·
    refine ⟨26348058389434773266643959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17565372259623182177762639 26348058389434773266643959)
    ·
      refine ⟨39522087584152159899965939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26348058389434773266643959 39522087584152159899965939)
      ·
        refine ⟨59283131376228239849948909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39522087584152159899965939 59283131376228239849948909)
        ·
          refine ⟨22231174266085589943730841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59283131376228239849948909 22231174266085589943730841)
          ·
            refine ⟨16673380699564192457798131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22231174266085589943730841 16673380699564192457798131)
            ·
              refine ⟨25010071049346288686697197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16673380699564192457798131 25010071049346288686697197)
              ·
                refine ⟨9378776643504858257511449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25010071049346288686697197 9378776643504858257511449)
                ·
                  refine ⟨7034082482628643693133587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9378776643504858257511449 7034082482628643693133587)
                  ·
                    refine ⟨10551123723942965539700381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7034082482628643693133587 10551123723942965539700381)
                    ·
                      refine ⟨3956671396478612077387643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10551123723942965539700381 3956671396478612077387643)
                      ·
                        rfl

theorem cell23_7705590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_7705590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705590 prefixEnd_7705590 := by exact prefixLift 7705590
  have htrace : WordTrace (prefixWord ++ tailWord_7705590) baseStart_7705590 baseEnd_7705590 := by
    simpa [prefixWord, tailWord_7705590, baseEnd_7705590] using wordTrace_append hprefix tailTrace_7705590
  have hstable : (prefixWord ++ tailWord_7705590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705590).length < 2 ^ (prefixWord ++ tailWord_7705590).sum := by decide
  have hdescent : baseEnd_7705590 < baseStart_7705590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705649 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 1, 7]
def baseStart_7705649 : Nat := 118140960795 + 7705649 * 2 ^ 59
def prefixEnd_7705649 : Nat := 4983230072969 + 3 ^ 40 * 7705649 * 2
def baseEnd_7705649 : Nat := 1318900563945742448849957

theorem tailTrace_7705649 : CollatzResearch.WordTrace tailWord_7705649 prefixEnd_7705649 1318900563945742448849957 := by
  unfold tailWord_7705649
  simp only [CollatzResearch.WordTrace]
  refine ⟨281048108060757167920600001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187365405373838111947066667 281048108060757167920600001)
  ·
    refine ⟨210786081045567875940450001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281048108060757167920600001 210786081045567875940450001)
    ·
      refine ⟨158089560784175906955337501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210786081045567875940450001 158089560784175906955337501)
      ·
        refine ⟨59283585294065965108251563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158089560784175906955337501 59283585294065965108251563)
        ·
          refine ⟨88925377941098947662377345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59283585294065965108251563 88925377941098947662377345)
          ·
            refine ⟨66694033455824210746783009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88925377941098947662377345 66694033455824210746783009)
            ·
              refine ⟨50020525091868158060087257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66694033455824210746783009 50020525091868158060087257)
              ·
                refine ⟨37515393818901118545065443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50020525091868158060087257 37515393818901118545065443)
                ·
                  refine ⟨56273090728351677817598165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37515393818901118545065443 56273090728351677817598165)
                  ·
                    refine ⟨1318900563945742448849957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56273090728351677817598165 1318900563945742448849957)
                    ·
                      rfl

theorem cell23_7705649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_7705649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705649 prefixEnd_7705649 := by exact prefixLift 7705649
  have htrace : WordTrace (prefixWord ++ tailWord_7705649) baseStart_7705649 baseEnd_7705649 := by
    simpa [prefixWord, tailWord_7705649, baseEnd_7705649] using wordTrace_append hprefix tailTrace_7705649
  have hstable : (prefixWord ++ tailWord_7705649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705649).length < 2 ^ (prefixWord ++ tailWord_7705649).sum := by decide
  have hdescent : baseEnd_7705649 < baseStart_7705649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705670 : List Nat := [6, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_7705670 : Nat := 118140960795 + 7705670 * 2 ^ 59
def prefixEnd_7705670 : Nat := 4983230072969 + 3 ^ 40 * 7705670 * 2
def baseEnd_7705670 : Nat := 439634719436774640487475

theorem tailTrace_7705670 : CollatzResearch.WordTrace tailWord_7705670 prefixEnd_7705670 439634719436774640487475 := by
  unfold tailWord_7705670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8782777312302534015847327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187365915995787392338076309 8782777312302534015847327)
  ·
    refine ⟨13174165968453801023770991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8782777312302534015847327 13174165968453801023770991)
    ·
      refine ⟨19761248952680701535656487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13174165968453801023770991 19761248952680701535656487)
      ·
        refine ⟨29641873429021052303484731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19761248952680701535656487 29641873429021052303484731)
        ·
          refine ⟨44462810143531578455227097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29641873429021052303484731 44462810143531578455227097)
          ·
            refine ⟨33347107607648683841420323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44462810143531578455227097 33347107607648683841420323)
            ·
              refine ⟨50020661411473025762130485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33347107607648683841420323 50020661411473025762130485)
              ·
                refine ⟨4689437007325596165199733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50020661411473025762130485 4689437007325596165199733)
                ·
                  refine ⟨439634719436774640487475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4689437007325596165199733 439634719436774640487475)
                  ·
                    rfl

theorem cell23_7705670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_7705670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705670 prefixEnd_7705670 := by exact prefixLift 7705670
  have htrace : WordTrace (prefixWord ++ tailWord_7705670) baseStart_7705670 baseEnd_7705670 := by
    simpa [prefixWord, tailWord_7705670, baseEnd_7705670] using wordTrace_append hprefix tailTrace_7705670
  have hstable : (prefixWord ++ tailWord_7705670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705670).length < 2 ^ (prefixWord ++ tailWord_7705670).sum := by decide
  have hdescent : baseEnd_7705670 < baseStart_7705670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705699 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 6]
def baseStart_7705699 : Nat := 118140960795 + 7705699 * 2 ^ 59
def prefixEnd_7705699 : Nat := 4983230072969 + 3 ^ 40 * 7705699 * 2
def baseEnd_7705699 : Nat := 3956727365869952150924641

theorem tailTrace_7705699 : CollatzResearch.WordTrace tailWord_7705699 prefixEnd_7705699 3956727365869952150924641 := by
  unfold tailWord_7705699
  simp only [CollatzResearch.WordTrace]
  refine ⟨281049931710576026459920151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187366621140384017639946767 281049931710576026459920151)
  ·
    refine ⟨421574897565864039689880227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281049931710576026459920151 421574897565864039689880227)
    ·
      refine ⟨632362346348796059534820341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421574897565864039689880227 632362346348796059534820341)
      ·
        refine ⟨59283969970199630581389407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 632362346348796059534820341 59283969970199630581389407)
        ·
          refine ⟨88925954955299445872084111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59283969970199630581389407 88925954955299445872084111)
          ·
            refine ⟨133388932432949168808126167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88925954955299445872084111 133388932432949168808126167)
            ·
              refine ⟨200083398649423753212189251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133388932432949168808126167 200083398649423753212189251)
              ·
                refine ⟨300125097974135629818283877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200083398649423753212189251 300125097974135629818283877)
                ·
                  refine ⟨56273455870150430590928227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300125097974135629818283877 56273455870150430590928227)
                  ·
                    refine ⟨84410183805225645886392341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56273455870150430590928227 84410183805225645886392341)
                    ·
                      refine ⟨3956727365869952150924641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84410183805225645886392341 3956727365869952150924641)
                      ·
                        rfl

theorem cell23_7705699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_7705699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705699 prefixEnd_7705699 := by exact prefixLift 7705699
  have htrace : WordTrace (prefixWord ++ tailWord_7705699) baseStart_7705699 baseEnd_7705699 := by
    simpa [prefixWord, tailWord_7705699, baseEnd_7705699] using wordTrace_append hprefix tailTrace_7705699
  have hstable : (prefixWord ++ tailWord_7705699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705699).length < 2 ^ (prefixWord ++ tailWord_7705699).sum := by decide
  have hdescent : baseEnd_7705699 < baseStart_7705699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705703 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_7705703 : Nat := 118140960795 + 7705703 * 2 ^ 59
def prefixEnd_7705703 : Nat := 4983230072969 + 3 ^ 40 * 7705703 * 2
def baseEnd_7705703 : Nat := 3956729419792570135274623

theorem tailTrace_7705703 : CollatzResearch.WordTrace tailWord_7705703 prefixEnd_7705703 3956729419792570135274623 := by
  unfold tailWord_7705703
  simp only [CollatzResearch.WordTrace]
  refine ⟨281050077602561535143065763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187366718401707690095377175 281050077602561535143065763)
  ·
    refine ⟨421575116403842302714598645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281050077602561535143065763 421575116403842302714598645)
    ·
      refine ⟨39522667162860215879493623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 421575116403842302714598645 39522667162860215879493623)
      ·
        refine ⟨59284000744290323819240435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39522667162860215879493623 59284000744290323819240435)
        ·
          refine ⟨88926001116435485728860653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59284000744290323819240435 88926001116435485728860653)
          ·
            refine ⟨33347250418663307148322745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88926001116435485728860653 33347250418663307148322745)
            ·
              refine ⟨25010437813997480361242059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33347250418663307148322745 25010437813997480361242059)
              ·
                refine ⟨37515656720996220541863089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25010437813997480361242059 37515656720996220541863089)
                ·
                  refine ⟨28136742540747165406397317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37515656720996220541863089 28136742540747165406397317)
                  ·
                    refine ⟨5275639226390093513699497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28136742540747165406397317 5275639226390093513699497)
                    ·
                      refine ⟨3956729419792570135274623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5275639226390093513699497 3956729419792570135274623)
                      ·
                        rfl

theorem cell23_7705703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_7705703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705703 prefixEnd_7705703 := by exact prefixLift 7705703
  have htrace : WordTrace (prefixWord ++ tailWord_7705703) baseStart_7705703 baseEnd_7705703 := by
    simpa [prefixWord, tailWord_7705703, baseEnd_7705703] using wordTrace_append hprefix tailTrace_7705703
  have hstable : (prefixWord ++ tailWord_7705703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705703).length < 2 ^ (prefixWord ++ tailWord_7705703).sum := by decide
  have hdescent : baseEnd_7705703 < baseStart_7705703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705776 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 4]
def baseStart_7705776 : Nat := 118140960795 + 7705776 * 2 ^ 59
def prefixEnd_7705776 : Nat := 4983230072969 + 3 ^ 40 * 7705776 * 2
def baseEnd_7705776 : Nat := 3956766903880348349661787

theorem tailTrace_7705776 : CollatzResearch.WordTrace tailWord_7705776 prefixEnd_7705776 3956766903880348349661787 := by
  unfold tailWord_7705776
  simp only [CollatzResearch.WordTrace]
  refine ⟨140526370065648534305236591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187368493420864712406982121 140526370065648534305236591)
  ·
    refine ⟨210789555098472801457854887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140526370065648534305236591 210789555098472801457854887)
    ·
      refine ⟨316184332647709202186782331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210789555098472801457854887 316184332647709202186782331)
      ·
        refine ⟨474276498971563803280173497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316184332647709202186782331 474276498971563803280173497)
        ·
          refine ⟨355707374228672852460130123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474276498971563803280173497 355707374228672852460130123)
          ·
            refine ⟨533561061343009278690195185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355707374228672852460130123 533561061343009278690195185)
            ·
              refine ⟨400170796007256959017646389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533561061343009278690195185 400170796007256959017646389)
              ·
                refine ⟨37516012125680339907904349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 400170796007256959017646389 37516012125680339907904349)
                ·
                  refine ⟨14068504547130127465464131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37516012125680339907904349 14068504547130127465464131)
                  ·
                    refine ⟨21102756820695191198196197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14068504547130127465464131 21102756820695191198196197)
                    ·
                      refine ⟨3956766903880348349661787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21102756820695191198196197 3956766903880348349661787)
                      ·
                        rfl

theorem cell23_7705776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_7705776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705776 prefixEnd_7705776 := by exact prefixLift 7705776
  have htrace : WordTrace (prefixWord ++ tailWord_7705776) baseStart_7705776 baseEnd_7705776 := by
    simpa [prefixWord, tailWord_7705776, baseEnd_7705776] using wordTrace_append hprefix tailTrace_7705776
  have hstable : (prefixWord ++ tailWord_7705776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705776).length < 2 ^ (prefixWord ++ tailWord_7705776).sum := by decide
  have hdescent : baseEnd_7705776 < baseStart_7705776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705843 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 3]
def baseStart_7705843 : Nat := 118140960795 + 7705843 * 2 ^ 59
def prefixEnd_7705843 : Nat := 4983230072969 + 3 ^ 40 * 7705843 * 2
def baseEnd_7705843 : Nat := 3956801307084199587523979

theorem tailTrace_7705843 : CollatzResearch.WordTrace tailWord_7705843 prefixEnd_7705843 3956801307084199587523979 := by
  unfold tailWord_7705843
  simp only [CollatzResearch.WordTrace]
  refine ⟨281055183822054339053162183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187370122548036226035441455 281055183822054339053162183)
  ·
    refine ⟨421582775733081508579743275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281055183822054339053162183 421582775733081508579743275)
    ·
      refine ⟨632374163599622262869614913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421582775733081508579743275 632374163599622262869614913)
      ·
        refine ⟨474280622699716697152211185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632374163599622262869614913 474280622699716697152211185)
        ·
          refine ⟨355710467024787522864158389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474280622699716697152211185 355710467024787522864158389)
          ·
            refine ⟨33347856283573830268514849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 355710467024787522864158389 33347856283573830268514849)
            ·
              refine ⟨25010892212680372701386137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33347856283573830268514849 25010892212680372701386137)
              ·
                refine ⟨18758169159510279526039603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25010892212680372701386137 18758169159510279526039603)
                ·
                  refine ⟨28137253739265419289059405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18758169159510279526039603 28137253739265419289059405)
                  ·
                    refine ⟨10551470152224532233397277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28137253739265419289059405 10551470152224532233397277)
                    ·
                      refine ⟨3956801307084199587523979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10551470152224532233397277 3956801307084199587523979)
                      ·
                        rfl

theorem cell23_7705843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 3].length) (baseStart_7705843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705843 prefixEnd_7705843 := by exact prefixLift 7705843
  have htrace : WordTrace (prefixWord ++ tailWord_7705843) baseStart_7705843 baseEnd_7705843 := by
    simpa [prefixWord, tailWord_7705843, baseEnd_7705843] using wordTrace_append hprefix tailTrace_7705843
  have hstable : (prefixWord ++ tailWord_7705843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705843).length < 2 ^ (prefixWord ++ tailWord_7705843).sum := by decide
  have hdescent : baseEnd_7705843 < baseStart_7705843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7705874 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7705874 : Nat := 118140960795 + 7705874 * 2 ^ 59
def prefixEnd_7705874 : Nat := 4983230072969 + 3 ^ 40 * 7705874 * 2
def baseEnd_7705874 : Nat := 3956817224984488966236337

theorem tailTrace_7705874 : CollatzResearch.WordTrace tailWord_7705874 prefixEnd_7705874 3956817224984488966236337 := by
  unfold tailWord_7705874
  simp only [CollatzResearch.WordTrace]
  refine ⟨70264078621235507836885169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187370876323294687565027117 70264078621235507836885169)
  ·
    refine ⟨52698058965926630877663877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70264078621235507836885169 52698058965926630877663877)
    ·
      refine ⟨9880886056111243289561977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52698058965926630877663877 9880886056111243289561977)
      ·
        refine ⟨7410664542083432467171483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9880886056111243289561977 7410664542083432467171483)
        ·
          refine ⟨11115996813125148700757225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7410664542083432467171483 11115996813125148700757225)
          ·
            refine ⟨8336997609843861525567919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11115996813125148700757225 8336997609843861525567919)
            ·
              refine ⟨12505496414765792288351879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8336997609843861525567919 12505496414765792288351879)
              ·
                refine ⟨18758244622148688432527819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12505496414765792288351879 18758244622148688432527819)
                ·
                  refine ⟨28137366933223032648791729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18758244622148688432527819 28137366933223032648791729)
                  ·
                    refine ⟨21103025199917274486593797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28137366933223032648791729 21103025199917274486593797)
                    ·
                      refine ⟨3956817224984488966236337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21103025199917274486593797 3956817224984488966236337)
                      ·
                        rfl

theorem cell23_7705874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7705874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7705874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7705874 prefixEnd_7705874 := by exact prefixLift 7705874
  have htrace : WordTrace (prefixWord ++ tailWord_7705874) baseStart_7705874 baseEnd_7705874 := by
    simpa [prefixWord, tailWord_7705874, baseEnd_7705874] using wordTrace_append hprefix tailTrace_7705874
  have hstable : (prefixWord ++ tailWord_7705874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7705874).length < 2 ^ (prefixWord ++ tailWord_7705874).sum := by decide
  have hdescent : baseEnd_7705874 < baseStart_7705874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7705874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706010 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3]
def baseStart_7706010 : Nat := 118140960795 + 7706010 * 2 ^ 59
def prefixEnd_7706010 : Nat := 4983230072969 + 3 ^ 40 * 7706010 * 2
def baseEnd_7706010 : Nat := 3956887058353500434135711

theorem tailTrace_7706010 : CollatzResearch.WordTrace tailWord_7706010 prefixEnd_7706010 3956887058353500434135711 := by
  unfold tailWord_7706010
  simp only [CollatzResearch.WordTrace]
  refine ⟨70265318703112331643622871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187374183208299551049660989 70265318703112331643622871)
  ·
    refine ⟨105397978054668497465434307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70265318703112331643622871 105397978054668497465434307)
    ·
      refine ⟨158096967082002746198151461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105397978054668497465434307 158096967082002746198151461)
      ·
        refine ⟨29643181327875514912153399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158096967082002746198151461 29643181327875514912153399)
        ·
          refine ⟨44464771991813272368230099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29643181327875514912153399 44464771991813272368230099)
          ·
            refine ⟨66697157987719908552345149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44464771991813272368230099 66697157987719908552345149)
            ·
              refine ⟨25011434245394965707129431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66697157987719908552345149 25011434245394965707129431)
              ·
                refine ⟨37517151368092448560694147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25011434245394965707129431 37517151368092448560694147)
                ·
                  refine ⟨56275727052138672841041221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37517151368092448560694147 56275727052138672841041221)
                  ·
                    refine ⟨10551698822276001157695229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56275727052138672841041221 10551698822276001157695229)
                    ·
                      refine ⟨3956887058353500434135711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10551698822276001157695229 3956887058353500434135711)
                      ·
                        rfl

theorem cell23_7706010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_7706010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706010 prefixEnd_7706010 := by exact prefixLift 7706010
  have htrace : WordTrace (prefixWord ++ tailWord_7706010) baseStart_7706010 baseEnd_7706010 := by
    simpa [prefixWord, tailWord_7706010, baseEnd_7706010] using wordTrace_append hprefix tailTrace_7706010
  have hstable : (prefixWord ++ tailWord_7706010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706010).length < 2 ^ (prefixWord ++ tailWord_7706010).sum := by decide
  have hdescent : baseEnd_7706010 < baseStart_7706010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706033 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_7706033 : Nat := 118140960795 + 7706033 * 2 ^ 59
def prefixEnd_7706033 : Nat := 4983230072969 + 3 ^ 40 * 7706033 * 2
def baseEnd_7706033 : Nat := 3956898868408553844148105

theorem tailTrace_7706033 : CollatzResearch.WordTrace tailWord_7706033 prefixEnd_7706033 3956898868408553844148105 := by
  unfold tailWord_7706033
  simp only [CollatzResearch.WordTrace]
  refine ⟨281062113691366001502578753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187374742460910667668385835 281062113691366001502578753)
  ·
    refine ⟨210796585268524501126934065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281062113691366001502578753 210796585268524501126934065)
    ·
      refine ⟨158097438951393375845200549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210796585268524501126934065 158097438951393375845200549)
      ·
        refine ⟨29643269803386257970975103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158097438951393375845200549 29643269803386257970975103)
        ·
          refine ⟨44464904705079386956462655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29643269803386257970975103 44464904705079386956462655)
          ·
            refine ⟨66697357057619080434693983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44464904705079386956462655 66697357057619080434693983)
            ·
              refine ⟨100046035586428620652040975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66697357057619080434693983 100046035586428620652040975)
              ·
                refine ⟨150069053379642930978061463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100046035586428620652040975 150069053379642930978061463)
                ·
                  refine ⟨225103580069464396467092195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150069053379642930978061463 225103580069464396467092195)
                  ·
                    refine ⟨337655370104196594700638293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 225103580069464396467092195 337655370104196594700638293)
                    ·
                      refine ⟨3956898868408553844148105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 337655370104196594700638293 3956898868408553844148105)
                      ·
                        rfl

theorem cell23_7706033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_7706033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706033 prefixEnd_7706033 := by exact prefixLift 7706033
  have htrace : WordTrace (prefixWord ++ tailWord_7706033) baseStart_7706033 baseEnd_7706033 := by
    simpa [prefixWord, tailWord_7706033, baseEnd_7706033] using wordTrace_append hprefix tailTrace_7706033
  have hstable : (prefixWord ++ tailWord_7706033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706033).length < 2 ^ (prefixWord ++ tailWord_7706033).sum := by decide
  have hdescent : baseEnd_7706033 < baseStart_7706033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706068 : List Nat := [2, 4, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_7706068 : Nat := 118140960795 + 7706068 * 2 ^ 59
def prefixEnd_7706068 : Nat := 4983230072969 + 3 ^ 40 * 7706068 * 2
def baseEnd_7706068 : Nat := 1318972280077153735736815

theorem tailTrace_7706068 : CollatzResearch.WordTrace tailWord_7706068 prefixEnd_7706068 1318972280077153735736815 := by
  unfold tailWord_7706068
  simp only [CollatzResearch.WordTrace]
  refine ⟨140531695123119601240051429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187375593497492801653401905 140531695123119601240051429)
  ·
    refine ⟨26349692835584925232509643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140531695123119601240051429 26349692835584925232509643)
    ·
      refine ⟨39524539253377387848764465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26349692835584925232509643 39524539253377387848764465)
      ·
        refine ⟨29643404440033040886573349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39524539253377387848764465 29643404440033040886573349)
        ·
          refine ⟨5558138332506195166232503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29643404440033040886573349 5558138332506195166232503)
          ·
            refine ⟨8337207498759292749348755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5558138332506195166232503 8337207498759292749348755)
            ·
              refine ⟨12505811248138939124023133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8337207498759292749348755 12505811248138939124023133)
              ·
                refine ⟨4689679218052102171508675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12505811248138939124023133 4689679218052102171508675)
                ·
                  refine ⟨7034518827078153257263013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689679218052102171508675 7034518827078153257263013)
                  ·
                    refine ⟨1318972280077153735736815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7034518827078153257263013 1318972280077153735736815)
                    ·
                      rfl

theorem cell23_7706068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_7706068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706068 prefixEnd_7706068 := by exact prefixLift 7706068
  have htrace : WordTrace (prefixWord ++ tailWord_7706068) baseStart_7706068 baseEnd_7706068 := by
    simpa [prefixWord, tailWord_7706068, baseEnd_7706068] using wordTrace_append hprefix tailTrace_7706068
  have hstable : (prefixWord ++ tailWord_7706068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706068).length < 2 ^ (prefixWord ++ tailWord_7706068).sum := by decide
  have hdescent : baseEnd_7706068 < baseStart_7706068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706077 : List Nat := [1, 4, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_7706077 : Nat := 118140960795 + 7706077 * 2 ^ 59
def prefixEnd_7706077 : Nat := 4983230072969 + 3 ^ 40 * 7706077 * 2
def baseEnd_7706077 : Nat := 1318973820519117223999301

theorem tailTrace_7706077 : CollatzResearch.WordTrace tailWord_7706077 prefixEnd_7706077 1318973820519117223999301 := by
  unfold tailWord_7706077
  simp only [CollatzResearch.WordTrace]
  refine ⟨281063718503206597017180485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187375812335471064678120323 281063718503206597017180485)
  ·
    refine ⟨52699447219351236940721341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281063718503206597017180485 52699447219351236940721341)
    ·
      refine ⟨19762292707256713852770503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52699447219351236940721341 19762292707256713852770503)
      ·
        refine ⟨29643439060885070779155755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19762292707256713852770503 29643439060885070779155755)
        ·
          refine ⟨44465158591327606168733633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29643439060885070779155755 44465158591327606168733633)
          ·
            refine ⟨33348868943495704626550225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44465158591327606168733633 33348868943495704626550225)
            ·
              refine ⟨25011651707621778469912669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33348868943495704626550225 25011651707621778469912669)
              ·
                refine ⟨9379369390358166926217251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25011651707621778469912669 9379369390358166926217251)
                ·
                  refine ⟨14069054085537250389325877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9379369390358166926217251 14069054085537250389325877)
                  ·
                    refine ⟨1318973820519117223999301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14069054085537250389325877 1318973820519117223999301)
                    ·
                      rfl

theorem cell23_7706077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_7706077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706077 prefixEnd_7706077 := by exact prefixLift 7706077
  have htrace : WordTrace (prefixWord ++ tailWord_7706077) baseStart_7706077 baseEnd_7706077 := by
    simpa [prefixWord, tailWord_7706077, baseEnd_7706077] using wordTrace_append hprefix tailTrace_7706077
  have hstable : (prefixWord ++ tailWord_7706077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706077).length < 2 ^ (prefixWord ++ tailWord_7706077).sum := by decide
  have hdescent : baseEnd_7706077 < baseStart_7706077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706114 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7706114 : Nat := 118140960795 + 7706114 * 2 ^ 59
def prefixEnd_7706114 : Nat := 4983230072969 + 3 ^ 40 * 7706114 * 2
def baseEnd_7706114 : Nat := 3956940460341568027235233

theorem tailTrace_7706114 : CollatzResearch.WordTrace tailWord_7706114 prefixEnd_7706114 3956940460341568027235233 := by
  unfold tailWord_7706114
  simp only [CollatzResearch.WordTrace]
  refine ⟨70266267001018138084069349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187376712002715034890851597 70266267001018138084069349)
  ·
    refine ⟨13174925062690900890763003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70266267001018138084069349 13174925062690900890763003)
    ·
      refine ⟨19762387594036351336144505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13174925062690900890763003 19762387594036351336144505)
      ·
        refine ⟨14821790695527263502108379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19762387594036351336144505 14821790695527263502108379)
        ·
          refine ⟨22232686043290895253162569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14821790695527263502108379 22232686043290895253162569)
          ·
            refine ⟨16674514532468171439871927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22232686043290895253162569 16674514532468171439871927)
            ·
              refine ⟨25011771798702257159807891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16674514532468171439871927 25011771798702257159807891)
              ·
                refine ⟨37517657698053385739711837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25011771798702257159807891 37517657698053385739711837)
                ·
                  refine ⟨14069121636770019652391939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37517657698053385739711837 14069121636770019652391939)
                  ·
                    refine ⟨21103682455155029478587909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14069121636770019652391939 21103682455155029478587909)
                    ·
                      refine ⟨3956940460341568027235233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21103682455155029478587909 3956940460341568027235233)
                      ·
                        rfl

theorem cell23_7706114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7706114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706114 prefixEnd_7706114 := by exact prefixLift 7706114
  have htrace : WordTrace (prefixWord ++ tailWord_7706114) baseStart_7706114 baseEnd_7706114 := by
    simpa [prefixWord, tailWord_7706114, baseEnd_7706114] using wordTrace_append hprefix tailTrace_7706114
  have hstable : (prefixWord ++ tailWord_7706114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706114).length < 2 ^ (prefixWord ++ tailWord_7706114).sum := by decide
  have hdescent : baseEnd_7706114 < baseStart_7706114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706142 : List Nat := [4, 3, 3, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_7706142 : Nat := 118140960795 + 7706142 * 2 ^ 59
def prefixEnd_7706142 : Nat := 4983230072969 + 3 ^ 40 * 7706142 * 2
def baseEnd_7706142 : Nat := 3956954837799893917685105

theorem tailTrace_7706142 : CollatzResearch.WordTrace tailWord_7706142 prefixEnd_7706142 3956954837799893917685105 := by
  unfold tailWord_7706142
  simp only [CollatzResearch.WordTrace]
  refine ⟨35133261155996389139787085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187377392831980742078864453 35133261155996389139787085)
  ·
    refine ⟨13174972933498645927420157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35133261155996389139787085 13174972933498645927420157)
    ·
      refine ⟨4940614850061992222782559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13174972933498645927420157 4940614850061992222782559)
      ·
        refine ⟨7410922275092988334173839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4940614850061992222782559 7410922275092988334173839)
        ·
          refine ⟨11116383412639482501260759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7410922275092988334173839 11116383412639482501260759)
          ·
            refine ⟨16674575118959223751891139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11116383412639482501260759 16674575118959223751891139)
            ·
              refine ⟨25011862678438835627836709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16674575118959223751891139 25011862678438835627836709)
              ·
                refine ⟨4689724252207281680219383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25011862678438835627836709 4689724252207281680219383)
                ·
                  refine ⟨7034586378310922520329075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689724252207281680219383 7034586378310922520329075)
                  ·
                    refine ⟨10551879567466383780493613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7034586378310922520329075 10551879567466383780493613)
                    ·
                      refine ⟨3956954837799893917685105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10551879567466383780493613 3956954837799893917685105)
                      ·
                        rfl

theorem cell23_7706142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_7706142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706142 prefixEnd_7706142 := by exact prefixLift 7706142
  have htrace : WordTrace (prefixWord ++ tailWord_7706142) baseStart_7706142 baseEnd_7706142 := by
    simpa [prefixWord, tailWord_7706142, baseEnd_7706142] using wordTrace_append hprefix tailTrace_7706142
  have hstable : (prefixWord ++ tailWord_7706142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706142).length < 2 ^ (prefixWord ++ tailWord_7706142).sum := by decide
  have hdescent : baseEnd_7706142 < baseStart_7706142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706170 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_7706170 : Nat := 118140960795 + 7706170 * 2 ^ 59
def prefixEnd_7706170 : Nat := 4983230072969 + 3 ^ 40 * 7706170 * 2
def baseEnd_7706170 : Nat := 3956969215258219808134975

theorem tailTrace_7706170 : CollatzResearch.WordTrace tailWord_7706170 prefixEnd_7706170 3956969215258219808134975 := by
  unfold tailWord_7706170
  simp only [CollatzResearch.WordTrace]
  refine ⟨70266777622967418475078991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187378073661246449266877309 70266777622967418475078991)
  ·
    refine ⟨105400166434451127712618487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70266777622967418475078991 105400166434451127712618487)
    ·
      refine ⟨158100249651676691568927731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105400166434451127712618487 158100249651676691568927731)
      ·
        refine ⟨237150374477515037353391597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158100249651676691568927731 237150374477515037353391597)
        ·
          refine ⟨88931390429068139007521849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237150374477515037353391597 88931390429068139007521849)
          ·
            refine ⟨66698542821801104255641387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88931390429068139007521849 66698542821801104255641387)
            ·
              refine ⟨100047814232701656383462081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66698542821801104255641387 100047814232701656383462081)
              ·
                refine ⟨75035860674526242287596561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100047814232701656383462081 75035860674526242287596561)
                ·
                  refine ⟨56276895505894681715697421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75035860674526242287596561 56276895505894681715697421)
                  ·
                    refine ⟨21103835814710505643386533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56276895505894681715697421 21103835814710505643386533)
                    ·
                      refine ⟨3956969215258219808134975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21103835814710505643386533 3956969215258219808134975)
                      ·
                        rfl

theorem cell23_7706170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_7706170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706170 prefixEnd_7706170 := by exact prefixLift 7706170
  have htrace : WordTrace (prefixWord ++ tailWord_7706170) baseStart_7706170 baseEnd_7706170 := by
    simpa [prefixWord, tailWord_7706170, baseEnd_7706170] using wordTrace_append hprefix tailTrace_7706170
  have hstable : (prefixWord ++ tailWord_7706170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706170).length < 2 ^ (prefixWord ++ tailWord_7706170).sum := by decide
  have hdescent : baseEnd_7706170 < baseStart_7706170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706182 : List Nat := [6, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_7706182 : Nat := 118140960795 + 7706182 * 2 ^ 59
def prefixEnd_7706182 : Nat := 4983230072969 + 3 ^ 40 * 7706182 * 2
def baseEnd_7706182 : Nat := 3956975377026073761184921

theorem tailTrace_7706182 : CollatzResearch.WordTrace tailWord_7706182 prefixEnd_7706182 3956975377026073761184921 := by
  unfold tailWord_7706182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8783360880244568748429775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187378365445217466633168533 8783360880244568748429775)
  ·
    refine ⟨13175041320366853122644663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8783360880244568748429775 13175041320366853122644663)
    ·
      refine ⟨19762561980550279683966995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13175041320366853122644663 19762561980550279683966995)
      ·
        refine ⟨29643842970825419525950493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19762561980550279683966995 29643842970825419525950493)
        ·
          refine ⟨11116441114059532322231435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29643842970825419525950493 11116441114059532322231435)
          ·
            refine ⟨16674661671089298483347153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11116441114059532322231435 16674661671089298483347153)
            ·
              refine ⟨12505996253316973862510365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16674661671089298483347153 12505996253316973862510365)
              ·
                refine ⟨4689748594993865198441387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12505996253316973862510365 4689748594993865198441387)
                ·
                  refine ⟨7034622892490797797662081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689748594993865198441387 7034622892490797797662081)
                  ·
                    refine ⟨5275967169368098348246561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7034622892490797797662081 5275967169368098348246561)
                    ·
                      refine ⟨3956975377026073761184921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5275967169368098348246561 3956975377026073761184921)
                      ·
                        rfl

theorem cell23_7706182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_7706182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706182 prefixEnd_7706182 := by exact prefixLift 7706182
  have htrace : WordTrace (prefixWord ++ tailWord_7706182) baseStart_7706182 baseEnd_7706182 := by
    simpa [prefixWord, tailWord_7706182, baseEnd_7706182] using wordTrace_append hprefix tailTrace_7706182
  have hstable : (prefixWord ++ tailWord_7706182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706182).length < 2 ^ (prefixWord ++ tailWord_7706182).sum := by decide
  have hdescent : baseEnd_7706182 < baseStart_7706182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706190 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_7706190 : Nat := 118140960795 + 7706190 * 2 ^ 59
def prefixEnd_7706190 : Nat := 4983230072969 + 3 ^ 40 * 7706190 * 2
def baseEnd_7706190 : Nat := 3956979484871309729884883

theorem tailTrace_7706190 : CollatzResearch.WordTrace tailWord_7706190 prefixEnd_7706190 3956979484871309729884883 := by
  unfold tailWord_7706190
  simp only [CollatzResearch.WordTrace]
  refine ⟨35133479993974652164505503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187378559967864811544029349 35133479993974652164505503)
  ·
    refine ⟨52700219990961978246758255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35133479993974652164505503 52700219990961978246758255)
    ·
      refine ⟨79050329986442967370137383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52700219990961978246758255 79050329986442967370137383)
      ·
        refine ⟨118575494979664451055206075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79050329986442967370137383 118575494979664451055206075)
        ·
          refine ⟨177863242469496676582809113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118575494979664451055206075 177863242469496676582809113)
          ·
            refine ⟨133397431852122507437106835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177863242469496676582809113 133397431852122507437106835)
            ·
              refine ⟨200096147778183761155660253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133397431852122507437106835 200096147778183761155660253)
              ·
                refine ⟨75036055416818910433372595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200096147778183761155660253 75036055416818910433372595)
                ·
                  refine ⟨112554083125228365650058893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75036055416818910433372595 112554083125228365650058893)
                  ·
                    refine ⟨42207781171960637118772085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112554083125228365650058893 42207781171960637118772085)
                    ·
                      refine ⟨3956979484871309729884883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42207781171960637118772085 3956979484871309729884883)
                      ·
                        rfl

theorem cell23_7706190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_7706190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706190 prefixEnd_7706190 := by exact prefixLift 7706190
  have htrace : WordTrace (prefixWord ++ tailWord_7706190) baseStart_7706190 baseEnd_7706190 := by
    simpa [prefixWord, tailWord_7706190, baseEnd_7706190] using wordTrace_append hprefix tailTrace_7706190
  have hstable : (prefixWord ++ tailWord_7706190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706190).length < 2 ^ (prefixWord ++ tailWord_7706190).sum := by decide
  have hdescent : baseEnd_7706190 < baseStart_7706190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706240 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 1, 7]
def baseStart_7706240 : Nat := 118140960795 + 7706240 * 2 ^ 59
def prefixEnd_7706240 : Nat := 4983230072969 + 3 ^ 40 * 7706240 * 2
def baseEnd_7706240 : Nat := 1319001719634678178086551

theorem tailTrace_7706240 : CollatzResearch.WordTrace tailWord_7706240 prefixEnd_7706240 1319001719634678178086551 := by
  unfold tailWord_7706240
  simp only [CollatzResearch.WordTrace]
  refine ⟨140534831800808037927682087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187379775734410717236909449 140534831800808037927682087)
  ·
    refine ⟨210802247701212056891523131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140534831800808037927682087 210802247701212056891523131)
    ·
      refine ⟨316203371551818085337284697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210802247701212056891523131 316203371551818085337284697)
      ·
        refine ⟨237152528663863564002963523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316203371551818085337284697 237152528663863564002963523)
        ·
          refine ⟨355728792995795346004445285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237152528663863564002963523 355728792995795346004445285)
          ·
            refine ⟨66699148686711627375833491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355728792995795346004445285 66699148686711627375833491)
            ·
              refine ⟨100048723030067441063750237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66699148686711627375833491 100048723030067441063750237)
              ·
                refine ⟨37518271136275290398906339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100048723030067441063750237 37518271136275290398906339)
                ·
                  refine ⟨56277406704412935598359509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37518271136275290398906339 56277406704412935598359509)
                  ·
                    refine ⟨1319001719634678178086551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56277406704412935598359509 1319001719634678178086551)
                    ·
                      rfl

theorem cell23_7706240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_7706240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706240 prefixEnd_7706240 := by exact prefixLift 7706240
  have htrace : WordTrace (prefixWord ++ tailWord_7706240) baseStart_7706240 baseEnd_7706240 := by
    simpa [prefixWord, tailWord_7706240, baseEnd_7706240] using wordTrace_append hprefix tailTrace_7706240
  have hstable : (prefixWord ++ tailWord_7706240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706240).length < 2 ^ (prefixWord ++ tailWord_7706240).sum := by decide
  have hdescent : baseEnd_7706240 < baseStart_7706240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706287 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 5, 4]
def baseStart_7706287 : Nat := 118140960795 + 7706287 * 2 ^ 59
def prefixEnd_7706287 : Nat := 4983230072969 + 3 ^ 40 * 7706287 * 2
def baseEnd_7706287 : Nat := 1319009764164931950123979

theorem tailTrace_7706287 : CollatzResearch.WordTrace tailWord_7706287 prefixEnd_7706287 1319009764164931950123979 := by
  unfold tailWord_7706287
  simp only [CollatzResearch.WordTrace]
  refine ⟨281071377832445802882325115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187380918554963868588216743 281071377832445802882325115)
  ·
    refine ⟨421607066748668704323487673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281071377832445802882325115 421607066748668704323487673)
    ·
      refine ⟨316205300061501528242615755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421607066748668704323487673 316205300061501528242615755)
      ·
        refine ⟨474307950092252292363923633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316205300061501528242615755 474307950092252292363923633)
        ·
          refine ⟨355730962569189219272942725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474307950092252292363923633 355730962569189219272942725)
          ·
            refine ⟨66699555481722978613676761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355730962569189219272942725 66699555481722978613676761)
            ·
              refine ⟨50024666611292233960257571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66699555481722978613676761 50024666611292233960257571)
              ·
                refine ⟨75036999916938350940386357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50024666611292233960257571 75036999916938350940386357)
                ·
                  refine ⟨7034718742212970400661221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75036999916938350940386357 7034718742212970400661221)
                  ·
                    refine ⟨1319009764164931950123979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7034718742212970400661221 1319009764164931950123979)
                    ·
                      rfl

theorem cell23_7706287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 4].length) (baseStart_7706287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706287 prefixEnd_7706287 := by exact prefixLift 7706287
  have htrace : WordTrace (prefixWord ++ tailWord_7706287) baseStart_7706287 baseEnd_7706287 := by
    simpa [prefixWord, tailWord_7706287, baseEnd_7706287] using wordTrace_append hprefix tailTrace_7706287
  have hstable : (prefixWord ++ tailWord_7706287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706287).length < 2 ^ (prefixWord ++ tailWord_7706287).sum := by decide
  have hdescent : baseEnd_7706287 < baseStart_7706287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706297 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 1, 4, 3]
def baseStart_7706297 : Nat := 118140960795 + 7706297 * 2 ^ 59
def prefixEnd_7706297 : Nat := 4983230072969 + 3 ^ 40 * 7706297 * 2
def baseEnd_7706297 : Nat := 3957034427301340811246891

theorem tailTrace_7706297 : CollatzResearch.WordTrace tailWord_7706297 prefixEnd_7706297 3957034427301340811246891 := by
  unfold tailWord_7706297
  simp only [CollatzResearch.WordTrace]
  refine ⟨281071742562409574590189145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187381161708273049726792763 281071742562409574590189145)
  ·
    refine ⟨210803806921807180942641859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281071742562409574590189145 210803806921807180942641859)
    ·
      refine ⟨316205710382710771413962789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210803806921807180942641859 316205710382710771413962789)
      ·
        refine ⟨59288570696758269640118023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316205710382710771413962789 59288570696758269640118023)
        ·
          refine ⟨88932856045137404460177035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59288570696758269640118023 88932856045137404460177035)
          ·
            refine ⟨133399284067706106690265553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88932856045137404460177035 133399284067706106690265553)
            ·
              refine ⟨100049463050779580017699165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133399284067706106690265553 100049463050779580017699165)
              ·
                refine ⟨37518548644042342506637187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100049463050779580017699165 37518548644042342506637187)
                ·
                  refine ⟨56277822966063513759955781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37518548644042342506637187 56277822966063513759955781)
                  ·
                    refine ⟨10552091806136908829991709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56277822966063513759955781 10552091806136908829991709)
                    ·
                      refine ⟨3957034427301340811246891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10552091806136908829991709 3957034427301340811246891)
                      ·
                        rfl

theorem cell23_7706297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_7706297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706297 prefixEnd_7706297 := by exact prefixLift 7706297
  have htrace : WordTrace (prefixWord ++ tailWord_7706297) baseStart_7706297 baseEnd_7706297 := by
    simpa [prefixWord, tailWord_7706297, baseEnd_7706297] using wordTrace_append hprefix tailTrace_7706297
  have hstable : (prefixWord ++ tailWord_7706297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706297).length < 2 ^ (prefixWord ++ tailWord_7706297).sum := by decide
  have hdescent : baseEnd_7706297 < baseStart_7706297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706321 : List Nat := [1, 2, 2, 1, 2, 5, 1, 4, 1, 4]
def baseStart_7706321 : Nat := 118140960795 + 7706321 * 2 ^ 59
def prefixEnd_7706321 : Nat := 4983230072969 + 3 ^ 40 * 7706321 * 2
def baseEnd_7706321 : Nat := 1319015583612349572448927

theorem tailTrace_7706321 : CollatzResearch.WordTrace tailWord_7706321 prefixEnd_7706321 1319015583612349572448927 := by
  unfold tailWord_7706321
  simp only [CollatzResearch.WordTrace]
  refine ⟨281072617914322626689062817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187381745276215084459375211 281072617914322626689062817)
  ·
    refine ⟨210804463435741970016797113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281072617914322626689062817 210804463435741970016797113)
    ·
      refine ⟨158103347576806477512597835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210804463435741970016797113 158103347576806477512597835)
      ·
        refine ⟨237155021365209716268896753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158103347576806477512597835 237155021365209716268896753)
        ·
          refine ⟨177866266023907287201672565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237155021365209716268896753 177866266023907287201672565)
          ·
            refine ⟨16674962439741308175156803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177866266023907287201672565 16674962439741308175156803)
            ·
              refine ⟨25012443659611962262735205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16674962439741308175156803 25012443659611962262735205)
              ·
                refine ⟨4689833186177242924262851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25012443659611962262735205 4689833186177242924262851)
                ·
                  refine ⟨7034749779265864386394277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689833186177242924262851 7034749779265864386394277)
                  ·
                    refine ⟨1319015583612349572448927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7034749779265864386394277 1319015583612349572448927)
                    ·
                      rfl

theorem cell23_7706321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_7706321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706321 prefixEnd_7706321 := by exact prefixLift 7706321
  have htrace : WordTrace (prefixWord ++ tailWord_7706321) baseStart_7706321 baseEnd_7706321 := by
    simpa [prefixWord, tailWord_7706321, baseEnd_7706321] using wordTrace_append hprefix tailTrace_7706321
  have hstable : (prefixWord ++ tailWord_7706321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706321).length < 2 ^ (prefixWord ++ tailWord_7706321).sum := by decide
  have hdescent : baseEnd_7706321 < baseStart_7706321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706347 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 3, 5]
def baseStart_7706347 : Nat := 118140960795 + 7706347 * 2 ^ 59
def prefixEnd_7706347 : Nat := 4983230072969 + 3 ^ 40 * 7706347 * 2
def baseEnd_7706347 : Nat := 1319020033778021871873887

theorem tailTrace_7706347 : CollatzResearch.WordTrace tailWord_7706347 prefixEnd_7706347 1319020033778021871873887 := by
  unfold tailWord_7706347
  simp only [CollatzResearch.WordTrace]
  refine ⟨281073566212228433129509295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187382377474818955419672863 281073566212228433129509295)
  ·
    refine ⟨421610349318342649694263943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281073566212228433129509295 421610349318342649694263943)
    ·
      refine ⟨632415523977513974541395915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421610349318342649694263943 632415523977513974541395915)
      ·
        refine ⟨948623285966270961812093873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632415523977513974541395915 948623285966270961812093873)
        ·
          refine ⟨711467464474703221359070405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 948623285966270961812093873 711467464474703221359070405)
          ·
            refine ⟨133400149589006854004825701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 711467464474703221359070405 133400149589006854004825701)
            ·
              refine ⟨25012528047938785125904819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133400149589006854004825701 25012528047938785125904819)
              ·
                refine ⟨37518792071908177688857229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25012528047938785125904819 37518792071908177688857229)
                ·
                  refine ⟨14069547026965566633321461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37518792071908177688857229 14069547026965566633321461)
                  ·
                    refine ⟨1319020033778021871873887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14069547026965566633321461 1319020033778021871873887)
                    ·
                      rfl

theorem cell23_7706347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 5].length) (baseStart_7706347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706347 prefixEnd_7706347 := by exact prefixLift 7706347
  have htrace : WordTrace (prefixWord ++ tailWord_7706347) baseStart_7706347 baseEnd_7706347 := by
    simpa [prefixWord, tailWord_7706347, baseEnd_7706347] using wordTrace_append hprefix tailTrace_7706347
  have hstable : (prefixWord ++ tailWord_7706347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706347).length < 2 ^ (prefixWord ++ tailWord_7706347).sum := by decide
  have hdescent : baseEnd_7706347 < baseStart_7706347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706364 : List Nat := [2, 2, 2, 1, 3, 1, 3, 3, 1, 5]
def baseStart_7706364 : Nat := 118140960795 + 7706364 * 2 ^ 59
def prefixEnd_7706364 : Nat := 4983230072969 + 3 ^ 40 * 7706364 * 2
def baseEnd_7706364 : Nat := 1319022943501730683036361

theorem tailTrace_7706364 : CollatzResearch.WordTrace tailWord_7706364 prefixEnd_7706364 1319022943501730683036361 := by
  unfold tailWord_7706364
  simp only [CollatzResearch.WordTrace]
  refine ⟨140537093126583422516439073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187382790835444563355252097 140537093126583422516439073)
  ·
    refine ⟨105402819844937566887329305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140537093126583422516439073 105402819844937566887329305)
    ·
      refine ⟨79052114883703175165496979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105402819844937566887329305 79052114883703175165496979)
      ·
        refine ⟨118578172325554762748245469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79052114883703175165496979 118578172325554762748245469)
        ·
          refine ⟨44466814622083036030592051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118578172325554762748245469 44466814622083036030592051)
          ·
            refine ⟨66700221933124554045888077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44466814622083036030592051 66700221933124554045888077)
            ·
              refine ⟨25012583224921707767208029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66700221933124554045888077 25012583224921707767208029)
              ·
                refine ⟨9379718709345640412703011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25012583224921707767208029 9379718709345640412703011)
                ·
                  refine ⟨14069578064018460619054517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9379718709345640412703011 14069578064018460619054517)
                  ·
                    refine ⟨1319022943501730683036361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14069578064018460619054517 1319022943501730683036361)
                    ·
                      rfl

theorem cell23_7706364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_7706364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706364 prefixEnd_7706364 := by exact prefixLift 7706364
  have htrace : WordTrace (prefixWord ++ tailWord_7706364) baseStart_7706364 baseEnd_7706364 := by
    simpa [prefixWord, tailWord_7706364, baseEnd_7706364] using wordTrace_append hprefix tailTrace_7706364
  have hstable : (prefixWord ++ tailWord_7706364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706364).length < 2 ^ (prefixWord ++ tailWord_7706364).sum := by decide
  have hdescent : baseEnd_7706364 < baseStart_7706364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706378 : List Nat := [3, 1, 2, 2, 1, 3, 2, 4, 1, 1, 3]
def baseStart_7706378 : Nat := 118140960795 + 7706378 * 2 ^ 59
def prefixEnd_7706378 : Nat := 4983230072969 + 3 ^ 40 * 7706378 * 2
def baseEnd_7706378 : Nat := 3957076019234354994334019

theorem tailTrace_7706378 : CollatzResearch.WordTrace tailWord_7706378 prefixEnd_7706378 3957076019234354994334019 := by
  unfold tailWord_7706378
  simp only [CollatzResearch.WordTrace]
  refine ⟨70268674218779031355971947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187383131250077416949258525 70268674218779031355971947)
  ·
    refine ⟨105403011328168547033957921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70268674218779031355971947 105403011328168547033957921)
    ·
      refine ⟨79052258496126410275468441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105403011328168547033957921 79052258496126410275468441)
      ·
        refine ⟨59289193872094807706601331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79052258496126410275468441 59289193872094807706601331)
        ·
          refine ⟨88933790808142211559901997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59289193872094807706601331 88933790808142211559901997)
          ·
            refine ⟨33350171553053329334963249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88933790808142211559901997 33350171553053329334963249)
            ·
              refine ⟨25012628664789997001222437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33350171553053329334963249 25012628664789997001222437)
              ·
                refine ⟨4689867874648124437729207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25012628664789997001222437 4689867874648124437729207)
                ·
                  refine ⟨7034801811972186656593811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689867874648124437729207 7034801811972186656593811)
                  ·
                    refine ⟨10552202717958279984890717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7034801811972186656593811 10552202717958279984890717)
                    ·
                      refine ⟨3957076019234354994334019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10552202717958279984890717 3957076019234354994334019)
                      ·
                        rfl

theorem cell23_7706378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_7706378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706378 prefixEnd_7706378 := by exact prefixLift 7706378
  have htrace : WordTrace (prefixWord ++ tailWord_7706378) baseStart_7706378 baseEnd_7706378 := by
    simpa [prefixWord, tailWord_7706378, baseEnd_7706378] using wordTrace_append hprefix tailTrace_7706378
  have hstable : (prefixWord ++ tailWord_7706378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706378).length < 2 ^ (prefixWord ++ tailWord_7706378).sum := by decide
  have hdescent : baseEnd_7706378 < baseStart_7706378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706387 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 3]
def baseStart_7706387 : Nat := 118140960795 + 7706387 * 2 ^ 59
def prefixEnd_7706387 : Nat := 4983230072969 + 3 ^ 40 * 7706387 * 2
def baseEnd_7706387 : Nat := 3957080640560245459121477

theorem tailTrace_7706387 : CollatzResearch.WordTrace tailWord_7706387 prefixEnd_7706387 3957080640560245459121477 := by
  unfold tailWord_7706387
  simp only [CollatzResearch.WordTrace]
  refine ⟨281075025132083519960965415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187383350088055679973976943 281075025132083519960965415)
  ·
    refine ⟨421612537698125279941448123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281075025132083519960965415 421612537698125279941448123)
    ·
      refine ⟨632418806547187919912172185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421612537698125279941448123 632418806547187919912172185)
      ·
        refine ⟨474314104910390939934129139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632418806547187919912172185 474314104910390939934129139)
        ·
          refine ⟨711471157365586409901193709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474314104910390939934129139 711471157365586409901193709)
          ·
            refine ⟨266801684012094903712947641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 711471157365586409901193709 266801684012094903712947641)
            ·
              refine ⟨200101263009071177784710731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266801684012094903712947641 200101263009071177784710731)
              ·
                refine ⟨300151894513606766677066097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200101263009071177784710731 300151894513606766677066097)
                ·
                  refine ⟨225113920885205075007799573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300151894513606766677066097 225113920885205075007799573)
                  ·
                    refine ⟨10552215041493987890990605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 225113920885205075007799573 10552215041493987890990605)
                    ·
                      refine ⟨3957080640560245459121477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10552215041493987890990605 3957080640560245459121477)
                      ·
                        rfl

theorem cell23_7706387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 3].length) (baseStart_7706387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706387 prefixEnd_7706387 := by exact prefixLift 7706387
  have htrace : WordTrace (prefixWord ++ tailWord_7706387) baseStart_7706387 baseEnd_7706387 := by
    simpa [prefixWord, tailWord_7706387, baseEnd_7706387] using wordTrace_append hprefix tailTrace_7706387
  have hstable : (prefixWord ++ tailWord_7706387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706387).length < 2 ^ (prefixWord ++ tailWord_7706387).sum := by decide
  have hdescent : baseEnd_7706387 < baseStart_7706387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706394 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 1, 6]
def baseStart_7706394 : Nat := 118140960795 + 7706394 * 2 ^ 59
def prefixEnd_7706394 : Nat := 4983230072969 + 3 ^ 40 * 7706394 * 2
def baseEnd_7706394 : Nat := 1319028078308275643911315

theorem tailTrace_7706394 : CollatzResearch.WordTrace tailWord_7706394 prefixEnd_7706394 1319028078308275643911315 := by
  unfold tailWord_7706394
  simp only [CollatzResearch.WordTrace]
  refine ⟨70268820110764540039117559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187383520295372106770980157 70268820110764540039117559)
  ·
    refine ⟨105403230166146810058676339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70268820110764540039117559 105403230166146810058676339)
    ·
      refine ⟨158104845249220215088014509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105403230166146810058676339 158104845249220215088014509)
      ·
        refine ⟨59289316968457580658005441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158104845249220215088014509 59289316968457580658005441)
        ·
          refine ⟨44466987726343185493504081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59289316968457580658005441 44466987726343185493504081)
          ·
            refine ⟨33350240794757389120128061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44466987726343185493504081 33350240794757389120128061)
            ·
              refine ⟨12506340298034020920048023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33350240794757389120128061 12506340298034020920048023)
              ·
                refine ⟨18759510447051031380072035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12506340298034020920048023 18759510447051031380072035)
                ·
                  refine ⟨28139265670576547070108053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18759510447051031380072035 28139265670576547070108053)
                  ·
                    refine ⟨1319028078308275643911315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28139265670576547070108053 1319028078308275643911315)
                    ·
                      rfl

theorem cell23_7706394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_7706394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706394 prefixEnd_7706394 := by exact prefixLift 7706394
  have htrace : WordTrace (prefixWord ++ tailWord_7706394) baseStart_7706394 baseEnd_7706394 := by
    simpa [prefixWord, tailWord_7706394, baseEnd_7706394] using wordTrace_append hprefix tailTrace_7706394
  have hstable : (prefixWord ++ tailWord_7706394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706394).length < 2 ^ (prefixWord ++ tailWord_7706394).sum := by decide
  have hdescent : baseEnd_7706394 < baseStart_7706394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706401 : List Nat := [1, 2, 3, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_7706401 : Nat := 118140960795 + 7706401 * 2 ^ 59
def prefixEnd_7706401 : Nat := 4983230072969 + 3 ^ 40 * 7706401 * 2
def baseEnd_7706401 : Nat := 3957087829289408404346413

theorem tailTrace_7706401 : CollatzResearch.WordTrace tailWord_7706401 prefixEnd_7706401 3957087829289408404346413 := by
  unfold tailWord_7706401
  simp only [CollatzResearch.WordTrace]
  refine ⟨281075535754032800351975057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187383690502688533567983371 281075535754032800351975057)
  ·
    refine ⟨210806651815524600263981293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281075535754032800351975057 210806651815524600263981293)
    ·
      refine ⟨79052494430821725098992985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210806651815524600263981293 79052494430821725098992985)
      ·
        refine ⟨59289370823116293824244739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79052494430821725098992985 59289370823116293824244739)
        ·
          refine ⟨88934056234674440736367109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59289370823116293824244739 88934056234674440736367109)
          ·
            refine ⟨16675135544001457638068833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88934056234674440736367109 16675135544001457638068833)
            ·
              refine ⟨12506351658001093228551625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16675135544001457638068833 12506351658001093228551625)
              ·
                refine ⟨9379763743500819921413719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12506351658001093228551625 9379763743500819921413719)
                ·
                  refine ⟨14069645615251229882120579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9379763743500819921413719 14069645615251229882120579)
                  ·
                    refine ⟨21104468422876844823180869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14069645615251229882120579 21104468422876844823180869)
                    ·
                      refine ⟨3957087829289408404346413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21104468422876844823180869 3957087829289408404346413)
                      ·
                        rfl

theorem cell23_7706401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_7706401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706401 prefixEnd_7706401 := by exact prefixLift 7706401
  have htrace : WordTrace (prefixWord ++ tailWord_7706401) baseStart_7706401 baseEnd_7706401 := by
    simpa [prefixWord, tailWord_7706401, baseEnd_7706401] using wordTrace_append hprefix tailTrace_7706401
  have hstable : (prefixWord ++ tailWord_7706401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706401).length < 2 ^ (prefixWord ++ tailWord_7706401).sum := by decide
  have hdescent : baseEnd_7706401 < baseStart_7706401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706421 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_7706421 : Nat := 118140960795 + 7706421 * 2 ^ 59
def prefixEnd_7706421 : Nat := 4983230072969 + 3 ^ 40 * 7706421 * 2
def baseEnd_7706421 : Nat := 3957098098902498326096321

theorem tailTrace_7706421 : CollatzResearch.WordTrace tailWord_7706421 prefixEnd_7706421 3957098098902498326096321 := by
  unfold tailWord_7706421
  simp only [CollatzResearch.WordTrace]
  refine ⟨281076265213960343767703117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187384176809306895845135411 281076265213960343767703117)
  ·
    refine ⟨105403599455235128912888669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281076265213960343767703117 105403599455235128912888669)
    ·
      refine ⟨39526349795713173342333251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105403599455235128912888669 39526349795713173342333251)
      ·
        refine ⟨59289524693569760013499877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39526349795713173342333251 59289524693569760013499877)
        ·
          refine ⟨11116785880044330002531227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59289524693569760013499877 11116785880044330002531227)
          ·
            refine ⟨16675178820066495003796841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11116785880044330002531227 16675178820066495003796841)
            ·
              refine ⟨12506384115049871252847631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16675178820066495003796841 12506384115049871252847631)
              ·
                refine ⟨18759576172574806879271447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12506384115049871252847631 18759576172574806879271447)
                ·
                  refine ⟨28139364258862210318907171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18759576172574806879271447 28139364258862210318907171)
                  ·
                    refine ⟨42209046388293315478360757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28139364258862210318907171 42209046388293315478360757)
                    ·
                      refine ⟨3957098098902498326096321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42209046388293315478360757 3957098098902498326096321)
                      ·
                        rfl

theorem cell23_7706421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_7706421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706421 prefixEnd_7706421 := by exact prefixLift 7706421
  have htrace : WordTrace (prefixWord ++ tailWord_7706421) baseStart_7706421 baseEnd_7706421 := by
    simpa [prefixWord, tailWord_7706421, baseEnd_7706421] using wordTrace_append hprefix tailTrace_7706421
  have hstable : (prefixWord ++ tailWord_7706421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706421).length < 2 ^ (prefixWord ++ tailWord_7706421).sum := by decide
  have hdescent : baseEnd_7706421 < baseStart_7706421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706437 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 2, 7]
def baseStart_7706437 : Nat := 118140960795 + 7706437 * 2 ^ 59
def prefixEnd_7706437 : Nat := 4983230072969 + 3 ^ 40 * 7706437 * 2
def baseEnd_7706437 : Nat := 1319035438197656754498749

theorem tailTrace_7706437 : CollatzResearch.WordTrace tailWord_7706437 prefixEnd_7706437 1319035438197656754498749 := by
  unfold tailWord_7706437
  simp only [CollatzResearch.WordTrace]
  refine ⟨281076848781902378500285565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187384565854601585666857043 281076848781902378500285565)
  ·
    refine ⟨105403818293213391937607087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281076848781902378500285565 105403818293213391937607087)
    ·
      refine ⟨158105727439820087906410631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105403818293213391937607087 158105727439820087906410631)
      ·
        refine ⟨237158591159730131859615947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158105727439820087906410631 237158591159730131859615947)
        ·
          refine ⟨355737886739595197789423921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237158591159730131859615947 355737886739595197789423921)
          ·
            refine ⟨266803415054696398342067941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355737886739595197789423921 266803415054696398342067941)
            ·
              refine ⟨50025640322755574689137739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266803415054696398342067941 50025640322755574689137739)
              ·
                refine ⟨75038460484133362033706609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50025640322755574689137739 75038460484133362033706609)
                ·
                  refine ⟨56278845363100021525279957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75038460484133362033706609 56278845363100021525279957)
                  ·
                    refine ⟨1319035438197656754498749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56278845363100021525279957 1319035438197656754498749)
                    ·
                      rfl

theorem cell23_7706437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_7706437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706437 prefixEnd_7706437 := by exact prefixLift 7706437
  have htrace : WordTrace (prefixWord ++ tailWord_7706437) baseStart_7706437 baseEnd_7706437 := by
    simpa [prefixWord, tailWord_7706437, baseEnd_7706437] using wordTrace_append hprefix tailTrace_7706437
  have hstable : (prefixWord ++ tailWord_7706437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706437).length < 2 ^ (prefixWord ++ tailWord_7706437).sum := by decide
  have hdescent : baseEnd_7706437 < baseStart_7706437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706438 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_7706438 : Nat := 118140960795 + 7706438 * 2 ^ 59
def prefixEnd_7706438 : Nat := 4983230072969 + 3 ^ 40 * 7706438 * 2
def baseEnd_7706438 : Nat := 3957106828073624759583743

theorem tailTrace_7706438 : CollatzResearch.WordTrace tailWord_7706438 prefixEnd_7706438 3957106828073624759583743 := by
  unfold tailWord_7706438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8783652664215586114720999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187384590169932503780714645 8783652664215586114720999)
  ·
    refine ⟨13175478996323379172081499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8783652664215586114720999 13175478996323379172081499)
    ·
      refine ⟨19763218494485068758122249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13175478996323379172081499 19763218494485068758122249)
      ·
        refine ⟨14822413870863801568591687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19763218494485068758122249 14822413870863801568591687)
        ·
          refine ⟨22233620806295702352887531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14822413870863801568591687 22233620806295702352887531)
          ·
            refine ⟨33350431209443553529331297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22233620806295702352887531 33350431209443553529331297)
            ·
              refine ⟨25012823407082665146998473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33350431209443553529331297 25012823407082665146998473)
              ·
                refine ⟨18759617555311998860248855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25012823407082665146998473 18759617555311998860248855)
                ·
                  refine ⟨28139426332967998290373283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18759617555311998860248855 28139426332967998290373283)
                  ·
                    refine ⟨42209139499451997435559925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28139426332967998290373283 42209139499451997435559925)
                    ·
                      refine ⟨3957106828073624759583743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42209139499451997435559925 3957106828073624759583743)
                      ·
                        rfl

theorem cell23_7706438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_7706438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706438 prefixEnd_7706438 := by exact prefixLift 7706438
  have htrace : WordTrace (prefixWord ++ tailWord_7706438) baseStart_7706438 baseEnd_7706438 := by
    simpa [prefixWord, tailWord_7706438, baseEnd_7706438] using wordTrace_append hprefix tailTrace_7706438
  have hstable : (prefixWord ++ tailWord_7706438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706438).length < 2 ^ (prefixWord ++ tailWord_7706438).sum := by decide
  have hdescent : baseEnd_7706438 < baseStart_7706438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706445 : List Nat := [1, 6, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_7706445 : Nat := 118140960795 + 7706445 * 2 ^ 59
def prefixEnd_7706445 : Nat := 4983230072969 + 3 ^ 40 * 7706445 * 2
def baseEnd_7706445 : Nat := 1319036807479402077398737

theorem tailTrace_7706445 : CollatzResearch.WordTrace tailWord_7706445 prefixEnd_7706445 1319036807479402077398737 := by
  unfold tailWord_7706445
  simp only [CollatzResearch.WordTrace]
  refine ⟨281077140565873395866576789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187384760377248930577717859 281077140565873395866576789)
  ·
    refine ⟨13175490964025315431245787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 281077140565873395866576789 13175490964025315431245787)
    ·
      refine ⟨19763236446037973146868681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13175490964025315431245787 19763236446037973146868681)
      ·
        refine ⟨14822427334528479860151511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19763236446037973146868681 14822427334528479860151511)
        ·
          refine ⟨22233641001792719790227267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14822427334528479860151511 22233641001792719790227267)
          ·
            refine ⟨33350461502689079685340901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22233641001792719790227267 33350461502689079685340901)
            ·
              refine ⟨6253211531754202441001419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33350461502689079685340901 6253211531754202441001419)
              ·
                refine ⟨9379817297631303661502129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6253211531754202441001419 9379817297631303661502129)
                ·
                  refine ⟨7034862973223477746126597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9379817297631303661502129 7034862973223477746126597)
                  ·
                    refine ⟨1319036807479402077398737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7034862973223477746126597 1319036807479402077398737)
                    ·
                      rfl

theorem cell23_7706445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_7706445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706445 prefixEnd_7706445 := by exact prefixLift 7706445
  have htrace : WordTrace (prefixWord ++ tailWord_7706445) baseStart_7706445 baseEnd_7706445 := by
    simpa [prefixWord, tailWord_7706445, baseEnd_7706445] using wordTrace_append hprefix tailTrace_7706445
  have hstable : (prefixWord ++ tailWord_7706445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706445).length < 2 ^ (prefixWord ++ tailWord_7706445).sum := by decide
  have hdescent : baseEnd_7706445 < baseStart_7706445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706455 : List Nat := [1, 1, 3, 2, 6, 1, 1, 2, 1, 2, 3]
def baseStart_7706455 : Nat := 118140960795 + 7706455 * 2 ^ 59
def prefixEnd_7706455 : Nat := 4983230072969 + 3 ^ 40 * 7706455 * 2
def baseEnd_7706455 : Nat := 3957115557244751193071165

theorem tailTrace_7706455 : CollatzResearch.WordTrace tailWord_7706455 prefixEnd_7706455 3957115557244751193071165 := by
  unfold tailWord_7706455
  simp only [CollatzResearch.WordTrace]
  refine ⟨281077505295837167574440819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187385003530558111716293879 281077505295837167574440819)
  ·
    refine ⟨421616257943755751361661229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281077505295837167574440819 421616257943755751361661229)
    ·
      refine ⟨158106096728908406760622961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421616257943755751361661229 158106096728908406760622961)
      ·
        refine ⟨118579572546681305070467221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158106096728908406760622961 118579572546681305070467221)
        ·
          refine ⟨5558417463125686175178151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118579572546681305070467221 5558417463125686175178151)
          ·
            refine ⟨8337626194688529262767227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5558417463125686175178151 8337626194688529262767227)
            ·
              refine ⟨12506439292032793894150841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8337626194688529262767227 12506439292032793894150841)
              ·
                refine ⟨9379829469024595420613131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12506439292032793894150841 9379829469024595420613131)
                ·
                  refine ⟨14069744203536893130919697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9379829469024595420613131 14069744203536893130919697)
                  ·
                    refine ⟨10552308152652669848189773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14069744203536893130919697 10552308152652669848189773)
                    ·
                      refine ⟨3957115557244751193071165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10552308152652669848189773 3957115557244751193071165)
                      ·
                        rfl

theorem cell23_7706455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_7706455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706455 prefixEnd_7706455 := by exact prefixLift 7706455
  have htrace : WordTrace (prefixWord ++ tailWord_7706455) baseStart_7706455 baseEnd_7706455 := by
    simpa [prefixWord, tailWord_7706455, baseEnd_7706455] using wordTrace_append hprefix tailTrace_7706455
  have hstable : (prefixWord ++ tailWord_7706455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706455).length < 2 ^ (prefixWord ++ tailWord_7706455).sum := by decide
  have hdescent : baseEnd_7706455 < baseStart_7706455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706486 : List Nat := [5, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_7706486 : Nat := 118140960795 + 7706486 * 2 ^ 59
def prefixEnd_7706486 : Nat := 4983230072969 + 3 ^ 40 * 7706486 * 2
def baseEnd_7706486 : Nat := 3957131475145040571783523

theorem tailTrace_7706486 : CollatzResearch.WordTrace tailWord_7706486 prefixEnd_7706486 3957131475145040571783523 := by
  unfold tailWord_7706486
  simp only [CollatzResearch.WordTrace]
  refine ⟨17567414747420303741801207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187385757305816573245879541 17567414747420303741801207)
  ·
    refine ⟨26351122121130455612701811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17567414747420303741801207 26351122121130455612701811)
    ·
      refine ⟨39526683181695683419052717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26351122121130455612701811 39526683181695683419052717)
      ·
        refine ⟨14822506193135881282144769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39526683181695683419052717 14822506193135881282144769)
        ·
          refine ⟨11116879644851910961608577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14822506193135881282144769 11116879644851910961608577)
          ·
            refine ⟨8337659733638933221206433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11116879644851910961608577 8337659733638933221206433)
            ·
              refine ⟨6253244800229199915904825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8337659733638933221206433 6253244800229199915904825)
              ·
                refine ⟨4689933600171899936928619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6253244800229199915904825 4689933600171899936928619)
                ·
                  refine ⟨7034900400257849905392929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4689933600171899936928619 7034900400257849905392929)
                  ·
                    refine ⟨5276175300193387429044697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7034900400257849905392929 5276175300193387429044697)
                    ·
                      refine ⟨3957131475145040571783523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5276175300193387429044697 3957131475145040571783523)
                      ·
                        rfl

theorem cell23_7706486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_7706486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706486 prefixEnd_7706486 := by exact prefixLift 7706486
  have htrace : WordTrace (prefixWord ++ tailWord_7706486) baseStart_7706486 baseEnd_7706486 := by
    simpa [prefixWord, tailWord_7706486, baseEnd_7706486] using wordTrace_append hprefix tailTrace_7706486
  have hstable : (prefixWord ++ tailWord_7706486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706486).length < 2 ^ (prefixWord ++ tailWord_7706486).sum := by decide
  have hdescent : baseEnd_7706486 < baseStart_7706486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706487 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_7706487 : Nat := 118140960795 + 7706487 * 2 ^ 59
def prefixEnd_7706487 : Nat := 4983230072969 + 3 ^ 40 * 7706487 * 2
def baseEnd_7706487 : Nat := 3957131988625695067871017

theorem tailTrace_7706487 : CollatzResearch.WordTrace tailWord_7706487 prefixEnd_7706487 3957131988625695067871017 := by
  unfold tailWord_7706487
  simp only [CollatzResearch.WordTrace]
  refine ⟨281078672431721237039605715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187385781621147491359737143 281078672431721237039605715)
  ·
    refine ⟨421618008647581855559408573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281078672431721237039605715 421618008647581855559408573)
    ·
      refine ⟨158106753242843195834778215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421618008647581855559408573 158106753242843195834778215)
      ·
        refine ⟨237160129864264793752167323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158106753242843195834778215 237160129864264793752167323)
        ·
          refine ⟨355740194796397190628250985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237160129864264793752167323 355740194796397190628250985)
          ·
            refine ⟨266805146097297892971188239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355740194796397190628250985 266805146097297892971188239)
            ·
              refine ⟨400207719145946839456782359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266805146097297892971188239 400207719145946839456782359)
              ·
                refine ⟨600311578718920259185173539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400207719145946839456782359 600311578718920259185173539)
                ·
                  refine ⟨900467368078380388777760309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600311578718920259185173539 900467368078380388777760309)
                  ·
                    refine ⟨84418815757348161447915029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 900467368078380388777760309 84418815757348161447915029)
                    ·
                      refine ⟨3957131988625695067871017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84418815757348161447915029 3957131988625695067871017)
                      ·
                        rfl

theorem cell23_7706487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_7706487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706487 prefixEnd_7706487 := by exact prefixLift 7706487
  have htrace : WordTrace (prefixWord ++ tailWord_7706487) baseStart_7706487 baseEnd_7706487 := by
    simpa [prefixWord, tailWord_7706487, baseEnd_7706487] using wordTrace_append hprefix tailTrace_7706487
  have hstable : (prefixWord ++ tailWord_7706487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706487).length < 2 ^ (prefixWord ++ tailWord_7706487).sum := by decide
  have hdescent : baseEnd_7706487 < baseStart_7706487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706529 : List Nat := [1, 2, 3, 4, 3, 1, 2, 1, 1, 3, 2]
def baseStart_7706529 : Nat := 118140960795 + 7706529 * 2 ^ 59
def prefixEnd_7706529 : Nat := 4983230072969 + 3 ^ 40 * 7706529 * 2
def baseEnd_7706529 : Nat := 3957153554813183903545825

theorem tailTrace_7706529 : CollatzResearch.WordTrace tailWord_7706529 prefixEnd_7706529 3957153554813183903545825 := by
  unfold tailWord_7706529
  simp only [CollatzResearch.WordTrace]
  refine ⟨281080204297569078212634641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187386802865046052141756427 281080204297569078212634641)
  ·
    refine ⟨210810153223176808659475981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281080204297569078212634641 210810153223176808659475981)
    ·
      refine ⟨79053807458691303247303493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210810153223176808659475981 79053807458691303247303493)
      ·
        refine ⟨14822588898504619358869405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79053807458691303247303493 14822588898504619358869405)
        ·
          refine ⟨5558470836939232259576027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14822588898504619358869405 5558470836939232259576027)
          ·
            refine ⟨8337706255408848389364041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5558470836939232259576027 8337706255408848389364041)
            ·
              refine ⟨6253279691556636292023031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8337706255408848389364041 6253279691556636292023031)
              ·
                refine ⟨9379919537334954438034547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6253279691556636292023031 9379919537334954438034547)
                ·
                  refine ⟨14069879306002431657051821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9379919537334954438034547 14069879306002431657051821)
                  ·
                    refine ⟨5276204739750911871394433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14069879306002431657051821 5276204739750911871394433)
                    ·
                      refine ⟨3957153554813183903545825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5276204739750911871394433 3957153554813183903545825)
                      ·
                        rfl

theorem cell23_7706529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_7706529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706529 prefixEnd_7706529 := by exact prefixLift 7706529
  have htrace : WordTrace (prefixWord ++ tailWord_7706529) baseStart_7706529 baseEnd_7706529 := by
    simpa [prefixWord, tailWord_7706529, baseEnd_7706529] using wordTrace_append hprefix tailTrace_7706529
  have hstable : (prefixWord ++ tailWord_7706529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706529).length < 2 ^ (prefixWord ++ tailWord_7706529).sum := by decide
  have hdescent : baseEnd_7706529 < baseStart_7706529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706574 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_7706574 : Nat := 118140960795 + 7706574 * 2 ^ 59
def prefixEnd_7706574 : Nat := 4983230072969 + 3 ^ 40 * 7706574 * 2
def baseEnd_7706574 : Nat := 1319058887147545409161039

theorem tailTrace_7706574 : CollatzResearch.WordTrace tailWord_7706574 prefixEnd_7706574 1319058887147545409161039 := by
  unfold tailWord_7706574
  simp only [CollatzResearch.WordTrace]
  refine ⟨35135230697800756362252847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187387897054937367265348517 35135230697800756362252847)
  ·
    refine ⟨52702846046701134543379271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35135230697800756362252847 52702846046701134543379271)
    ·
      refine ⟨79054269070051701815068907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52702846046701134543379271 79054269070051701815068907)
      ·
        refine ⟨118581403605077552722603361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79054269070051701815068907 118581403605077552722603361)
        ·
          refine ⟨88936052703808164541952521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118581403605077552722603361 88936052703808164541952521)
          ·
            refine ⟨66702039527856123406464391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88936052703808164541952521 66702039527856123406464391)
            ·
              refine ⟨100053059291784185109696587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66702039527856123406464391 100053059291784185109696587)
              ·
                refine ⟨150079588937676277664544881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100053059291784185109696587 150079588937676277664544881)
                ·
                  refine ⟨112559691703257208248408661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150079588937676277664544881 112559691703257208248408661)
                  ·
                    refine ⟨1319058887147545409161039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112559691703257208248408661 1319058887147545409161039)
                    ·
                      rfl

theorem cell23_7706574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_7706574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706574 prefixEnd_7706574 := by exact prefixLift 7706574
  have htrace : WordTrace (prefixWord ++ tailWord_7706574) baseStart_7706574 baseEnd_7706574 := by
    simpa [prefixWord, tailWord_7706574, baseEnd_7706574] using wordTrace_append hprefix tailTrace_7706574
  have hstable : (prefixWord ++ tailWord_7706574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706574).length < 2 ^ (prefixWord ++ tailWord_7706574).sum := by decide
  have hdescent : baseEnd_7706574 < baseStart_7706574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706581 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_7706581 : Nat := 118140960795 + 7706581 * 2 ^ 59
def prefixEnd_7706581 : Nat := 4983230072969 + 3 ^ 40 * 7706581 * 2
def baseEnd_7706581 : Nat := 3957180255807217700095585

theorem tailTrace_7706581 : CollatzResearch.WordTrace tailWord_7706581 prefixEnd_7706581 3957180255807217700095585 := by
  unfold tailWord_7706581
  simp only [CollatzResearch.WordTrace]
  refine ⟨281082100893380691093527597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187388067262253794062351731 281082100893380691093527597)
  ·
    refine ⟨105405787835017759160072849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281082100893380691093527597 105405787835017759160072849)
    ·
      refine ⟨79054340876263319370054637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105405787835017759160072849 79054340876263319370054637)
      ·
        refine ⟨29645377828598744763770489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79054340876263319370054637 29645377828598744763770489)
        ·
          refine ⟨22234033371449058572827867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29645377828598744763770489 22234033371449058572827867)
          ·
            refine ⟨33351050057173587859241801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22234033371449058572827867 33351050057173587859241801)
            ·
              refine ⟨25013287542880190894431351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33351050057173587859241801 25013287542880190894431351)
              ·
                refine ⟨37519931314320286341647027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25013287542880190894431351 37519931314320286341647027)
                ·
                  refine ⟨56279896971480429512470541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37519931314320286341647027 56279896971480429512470541)
                  ·
                    refine ⟨21104961364305161067176453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56279896971480429512470541 21104961364305161067176453)
                    ·
                      refine ⟨3957180255807217700095585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21104961364305161067176453 3957180255807217700095585)
                      ·
                        rfl

theorem cell23_7706581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_7706581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706581 prefixEnd_7706581 := by exact prefixLift 7706581
  have htrace : WordTrace (prefixWord ++ tailWord_7706581) baseStart_7706581 baseEnd_7706581 := by
    simpa [prefixWord, tailWord_7706581, baseEnd_7706581] using wordTrace_append hprefix tailTrace_7706581
  have hstable : (prefixWord ++ tailWord_7706581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706581).length < 2 ^ (prefixWord ++ tailWord_7706581).sum := by decide
  have hdescent : baseEnd_7706581 < baseStart_7706581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706582 : List Nat := [5, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_7706582 : Nat := 118140960795 + 7706582 * 2 ^ 59
def prefixEnd_7706582 : Nat := 4983230072969 + 3 ^ 40 * 7706582 * 2
def baseEnd_7706582 : Nat := 439686752143096910687009

theorem tailTrace_7706582 : CollatzResearch.WordTrace tailWord_7706582 prefixEnd_7706582 439686752143096910687009 := by
  unfold tailWord_7706582
  simp only [CollatzResearch.WordTrace]
  refine ⟨17567633585398566766519625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187388091577584712176209333 17567633585398566766519625)
  ·
    refine ⟨13175725189048925074889719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17567633585398566766519625 13175725189048925074889719)
    ·
      refine ⟨19763587783573387612334579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13175725189048925074889719 19763587783573387612334579)
      ·
        refine ⟨29645381675360081418501869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19763587783573387612334579 29645381675360081418501869)
        ·
          refine ⟨11117018128260030531938201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29645381675360081418501869 11117018128260030531938201)
          ·
            refine ⟨8337763596195022898953651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11117018128260030531938201 8337763596195022898953651)
            ·
              refine ⟨12506645394292534348430477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8337763596195022898953651 12506645394292534348430477)
              ·
                refine ⟨4689992022859700380661429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12506645394292534348430477 4689992022859700380661429)
                ·
                  refine ⟨439686752143096910687009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4689992022859700380661429 439686752143096910687009)
                  ·
                    rfl

theorem cell23_7706582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_7706582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706582 prefixEnd_7706582 := by exact prefixLift 7706582
  have htrace : WordTrace (prefixWord ++ tailWord_7706582) baseStart_7706582 baseEnd_7706582 := by
    simpa [prefixWord, tailWord_7706582, baseEnd_7706582] using wordTrace_append hprefix tailTrace_7706582
  have hstable : (prefixWord ++ tailWord_7706582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706582).length < 2 ^ (prefixWord ++ tailWord_7706582).sum := by decide
  have hdescent : baseEnd_7706582 < baseStart_7706582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706608 : List Nat := [2, 1, 1, 1, 3, 2, 2, 6, 1, 4]
def baseStart_7706608 : Nat := 118140960795 + 7706608 * 2 ^ 59
def prefixEnd_7706608 : Nat := 4983230072969 + 3 ^ 40 * 7706608 * 2
def baseEnd_7706608 : Nat := 1319064706594963031485987

theorem tailTrace_7706608 : CollatzResearch.WordTrace tailWord_7706608 prefixEnd_7706608 1319064706594963031485987 := by
  unfold tailWord_7706608
  simp only [CollatzResearch.WordTrace]
  refine ⟨140541542832141437352380239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187388723776188583136506985 140541542832141437352380239)
  ·
    refine ⟨210812314248212156028570359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140541542832141437352380239 210812314248212156028570359)
    ·
      refine ⟨316218471372318234042855539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210812314248212156028570359 316218471372318234042855539)
      ·
        refine ⟨474327707058477351064283309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316218471372318234042855539 474327707058477351064283309)
        ·
          refine ⟨177872890146929006649106241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474327707058477351064283309 177872890146929006649106241)
          ·
            refine ⟨133404667610196754986829681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177872890146929006649106241 133404667610196754986829681)
            ·
              refine ⟨100053500707647566240122261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133404667610196754986829681 100053500707647566240122261)
              ·
                refine ⟨4690007845670979667505731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100053500707647566240122261 4690007845670979667505731)
                ·
                  refine ⟨7035011768506469501258597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4690007845670979667505731 7035011768506469501258597)
                  ·
                    refine ⟨1319064706594963031485987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7035011768506469501258597 1319064706594963031485987)
                    ·
                      rfl

theorem cell23_7706608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 1, 4].length) (baseStart_7706608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706608 prefixEnd_7706608 := by exact prefixLift 7706608
  have htrace : WordTrace (prefixWord ++ tailWord_7706608) baseStart_7706608 baseEnd_7706608 := by
    simpa [prefixWord, tailWord_7706608, baseEnd_7706608] using wordTrace_append hprefix tailTrace_7706608
  have hstable : (prefixWord ++ tailWord_7706608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706608).length < 2 ^ (prefixWord ++ tailWord_7706608).sum := by decide
  have hdescent : baseEnd_7706608 < baseStart_7706608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706742 : List Nat := [5, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_7706742 : Nat := 118140960795 + 7706742 * 2 ^ 59
def prefixEnd_7706742 : Nat := 4983230072969 + 3 ^ 40 * 7706742 * 2
def baseEnd_7706742 : Nat := 3957262926192591570182345

theorem tailTrace_7706742 : CollatzResearch.WordTrace tailWord_7706742 prefixEnd_7706742 3957262926192591570182345 := by
  unfold tailWord_7706742
  simp only [CollatzResearch.WordTrace]
  refine ⟨17567998315362338474383655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187391982030531610393425653 17567998315362338474383655)
  ·
    refine ⟨26351997473043507711575483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17567998315362338474383655 26351997473043507711575483)
    ·
      refine ⟨39527996209565261567363225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26351997473043507711575483 39527996209565261567363225)
      ·
        refine ⟨29645997157173946175522419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39527996209565261567363225 29645997157173946175522419)
        ·
          refine ⟨44468995735760919263283629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29645997157173946175522419 44468995735760919263283629)
          ·
            refine ⟨16675873400910344723731361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44468995735760919263283629 16675873400910344723731361)
            ·
              refine ⟨12506905050682758542798521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16675873400910344723731361 12506905050682758542798521)
              ·
                refine ⟨9380178788012068907098891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12506905050682758542798521 9380178788012068907098891)
                ·
                  refine ⟨14070268182018103360648337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9380178788012068907098891 14070268182018103360648337)
                  ·
                    refine ⟨10552701136513577520486253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14070268182018103360648337 10552701136513577520486253)
                    ·
                      refine ⟨3957262926192591570182345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10552701136513577520486253 3957262926192591570182345)
                      ·
                        rfl

theorem cell23_7706742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_7706742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706742 prefixEnd_7706742 := by exact prefixLift 7706742
  have htrace : WordTrace (prefixWord ++ tailWord_7706742) baseStart_7706742 baseEnd_7706742 := by
    simpa [prefixWord, tailWord_7706742, baseEnd_7706742] using wordTrace_append hprefix tailTrace_7706742
  have hstable : (prefixWord ++ tailWord_7706742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706742).length < 2 ^ (prefixWord ++ tailWord_7706742).sum := by decide
  have hdescent : baseEnd_7706742 < baseStart_7706742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706812 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 1, 4, 2]
def baseStart_7706812 : Nat := 118140960795 + 7706812 * 2 ^ 59
def prefixEnd_7706812 : Nat := 4983230072969 + 3 ^ 40 * 7706812 * 2
def baseEnd_7706812 : Nat := 3957298869838406296307023

theorem tailTrace_7706812 : CollatzResearch.WordTrace tailWord_7706812 prefixEnd_7706812 3957298869838406296307023 := by
  unfold tailWord_7706812
  simp only [CollatzResearch.WordTrace]
  refine ⟨140545263077771908772593345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187393684103695878363457793 140545263077771908772593345)
  ·
    refine ⟨105408947308328931579445009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140545263077771908772593345 105408947308328931579445009)
    ·
      refine ⟨79056710481246698684583757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105408947308328931579445009 79056710481246698684583757)
      ·
        refine ⟨29646266430467512006718909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79056710481246698684583757 29646266430467512006718909)
        ·
          refine ⟨11117349911425317002519591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29646266430467512006718909 11117349911425317002519591)
          ·
            refine ⟨16676024867137975503779387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11117349911425317002519591 16676024867137975503779387)
            ·
              refine ⟨25014037300706963255669081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16676024867137975503779387 25014037300706963255669081)
              ·
                refine ⟨18760527975530222441751811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25014037300706963255669081 18760527975530222441751811)
                ·
                  refine ⟨28140791963295333662627717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18760527975530222441751811 28140791963295333662627717)
                  ·
                    refine ⟨5276398493117875061742697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28140791963295333662627717 5276398493117875061742697)
                    ·
                      refine ⟨3957298869838406296307023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5276398493117875061742697 3957298869838406296307023)
                      ·
                        rfl

theorem cell23_7706812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_7706812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706812 prefixEnd_7706812 := by exact prefixLift 7706812
  have htrace : WordTrace (prefixWord ++ tailWord_7706812) baseStart_7706812 baseEnd_7706812 := by
    simpa [prefixWord, tailWord_7706812, baseEnd_7706812] using wordTrace_append hprefix tailTrace_7706812
  have hstable : (prefixWord ++ tailWord_7706812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706812).length < 2 ^ (prefixWord ++ tailWord_7706812).sum := by decide
  have hdescent : baseEnd_7706812 < baseStart_7706812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706845 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_7706845 : Nat := 118140960795 + 7706845 * 2 ^ 59
def prefixEnd_7706845 : Nat := 4983230072969 + 3 ^ 40 * 7706845 * 2
def baseEnd_7706845 : Nat := 3957315814700004667194371

theorem tailTrace_7706845 : CollatzResearch.WordTrace tailWord_7706845 prefixEnd_7706845 3957315814700004667194371 := by
  unfold tailWord_7706845
  simp only [CollatzResearch.WordTrace]
  refine ⟨281091729764424264181137989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187394486509616176120758659 281091729764424264181137989)
  ·
    refine ⟨52704699330829549533963373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281091729764424264181137989 52704699330829549533963373)
    ·
      refine ⟨19764262249061081075236265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52704699330829549533963373 19764262249061081075236265)
      ·
        refine ⟨14823196686795810806427199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19764262249061081075236265 14823196686795810806427199)
        ·
          refine ⟨22234795030193716209640799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14823196686795810806427199 22234795030193716209640799)
          ·
            refine ⟨33352192545290574314461199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22234795030193716209640799 33352192545290574314461199)
            ·
              refine ⟨50028288817935861471691799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33352192545290574314461199 50028288817935861471691799)
              ·
                refine ⟨75042433226903792207537699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50028288817935861471691799 75042433226903792207537699)
                ·
                  refine ⟨112563649840355688311306549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75042433226903792207537699 112563649840355688311306549)
                  ·
                    refine ⟨10552842172533345779184989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112563649840355688311306549 10552842172533345779184989)
                    ·
                      refine ⟨3957315814700004667194371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10552842172533345779184989 3957315814700004667194371)
                      ·
                        rfl

theorem cell23_7706845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_7706845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706845 prefixEnd_7706845 := by exact prefixLift 7706845
  have htrace : WordTrace (prefixWord ++ tailWord_7706845) baseStart_7706845 baseEnd_7706845 := by
    simpa [prefixWord, tailWord_7706845, baseEnd_7706845] using wordTrace_append hprefix tailTrace_7706845
  have hstable : (prefixWord ++ tailWord_7706845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706845).length < 2 ^ (prefixWord ++ tailWord_7706845).sum := by decide
  have hdescent : baseEnd_7706845 < baseStart_7706845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706871 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_7706871 : Nat := 118140960795 + 7706871 * 2 ^ 59
def prefixEnd_7706871 : Nat := 4983230072969 + 3 ^ 40 * 7706871 * 2
def baseEnd_7706871 : Nat := 3957329165197021565469251

theorem tailTrace_7706871 : CollatzResearch.WordTrace tailWord_7706871 prefixEnd_7706871 3957329165197021565469251 := by
  unfold tailWord_7706871
  simp only [CollatzResearch.WordTrace]
  refine ⟨281092678062330070621584467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187395118708220047081056311 281092678062330070621584467)
  ·
    refine ⟨421639017093495105932376701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281092678062330070621584467 421639017093495105932376701)
    ·
      refine ⟨158114631410060664724641263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421639017093495105932376701 158114631410060664724641263)
      ·
        refine ⟨237171947115090997086961895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158114631410060664724641263 237171947115090997086961895)
        ·
          refine ⟨355757920672636495630442843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237171947115090997086961895 355757920672636495630442843)
          ·
            refine ⟨533636881008954743445664265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355757920672636495630442843 533636881008954743445664265)
            ·
              refine ⟨400227660756716057584248199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533636881008954743445664265 400227660756716057584248199)
              ·
                refine ⟨600341491135074086376372299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400227660756716057584248199 600341491135074086376372299)
                ·
                  refine ⟨900512236702611129564558449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600341491135074086376372299 900512236702611129564558449)
                  ·
                    refine ⟨675384177526958347173418837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 900512236702611129564558449 675384177526958347173418837)
                    ·
                      refine ⟨3957329165197021565469251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 675384177526958347173418837 3957329165197021565469251)
                      ·
                        rfl

theorem cell23_7706871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_7706871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706871 prefixEnd_7706871 := by exact prefixLift 7706871
  have htrace : WordTrace (prefixWord ++ tailWord_7706871) baseStart_7706871 baseEnd_7706871 := by
    simpa [prefixWord, tailWord_7706871, baseEnd_7706871] using wordTrace_append hprefix tailTrace_7706871
  have hstable : (prefixWord ++ tailWord_7706871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706871).length < 2 ^ (prefixWord ++ tailWord_7706871).sum := by decide
  have hdescent : baseEnd_7706871 < baseStart_7706871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706935 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 5, 1, 3]
def baseStart_7706935 : Nat := 118140960795 + 7706935 * 2 ^ 59
def prefixEnd_7706935 : Nat := 4983230072969 + 3 ^ 40 * 7706935 * 2
def baseEnd_7706935 : Nat := 3957362027958909315068957

theorem tailTrace_7706935 : CollatzResearch.WordTrace tailWord_7706935 prefixEnd_7706935 3957362027958909315068957 := by
  unfold tailWord_7706935
  simp only [CollatzResearch.WordTrace]
  refine ⟨281095012334098209551914259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187396674889398806367942839 281095012334098209551914259)
  ·
    refine ⟨421642518501147314327871389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281095012334098209551914259 421642518501147314327871389)
    ·
      refine ⟨158115944437930242872951771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421642518501147314327871389 158115944437930242872951771)
      ·
        refine ⟨237173916656895364309427657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158115944437930242872951771 237173916656895364309427657)
        ·
          refine ⟨177880437492671523232070743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237173916656895364309427657 177880437492671523232070743)
          ·
            refine ⟨266820656239007284848106115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177880437492671523232070743 266820656239007284848106115)
            ·
              refine ⟨400230984358510927272159173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266820656239007284848106115 400230984358510927272159173)
              ·
                refine ⟨75043309567220798863529845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400230984358510927272159173 75043309567220798863529845)
                ·
                  refine ⟨7035310271926949893455923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75043309567220798863529845 7035310271926949893455923)
                  ·
                    refine ⟨10552965407890424840183885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7035310271926949893455923 10552965407890424840183885)
                    ·
                      refine ⟨3957362027958909315068957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10552965407890424840183885 3957362027958909315068957)
                      ·
                        rfl

theorem cell23_7706935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_7706935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706935 prefixEnd_7706935 := by exact prefixLift 7706935
  have htrace : WordTrace (prefixWord ++ tailWord_7706935) baseStart_7706935 baseEnd_7706935 := by
    simpa [prefixWord, tailWord_7706935, baseEnd_7706935] using wordTrace_append hprefix tailTrace_7706935
  have hstable : (prefixWord ++ tailWord_7706935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706935).length < 2 ^ (prefixWord ++ tailWord_7706935).sum := by decide
  have hdescent : baseEnd_7706935 < baseStart_7706935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706952 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_7706952 : Nat := 118140960795 + 7706952 * 2 ^ 59
def prefixEnd_7706952 : Nat := 4983230072969 + 3 ^ 40 * 7706952 * 2
def baseEnd_7706952 : Nat := 3957370757130035748556379

theorem tailTrace_7706952 : CollatzResearch.WordTrace tailWord_7706952 prefixEnd_7706952 3957370757130035748556379 := by
  unfold tailWord_7706952
  simp only [CollatzResearch.WordTrace]
  refine ⟨140547816187518310727641555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187397088250024414303522073 140547816187518310727641555)
  ·
    refine ⟨210821724281277466091462333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140547816187518310727641555 210821724281277466091462333)
    ·
      refine ⟨79058146605479049784298375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210821724281277466091462333 79058146605479049784298375)
      ·
        refine ⟨118587219908218574676447563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79058146605479049784298375 118587219908218574676447563)
        ·
          refine ⟨177880829862327862014671345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118587219908218574676447563 177880829862327862014671345)
          ·
            refine ⟨133410622396745896511003509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177880829862327862014671345 133410622396745896511003509)
            ·
              refine ⟨12507245849694927797906579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133410622396745896511003509 12507245849694927797906579)
              ·
                refine ⟨18760868774542391696859869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12507245849694927797906579 18760868774542391696859869)
                ·
                  refine ⟨7035325790453396886322451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18760868774542391696859869 7035325790453396886322451)
                  ·
                    refine ⟨10552988685680095329483677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7035325790453396886322451 10552988685680095329483677)
                    ·
                      refine ⟨3957370757130035748556379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10552988685680095329483677 3957370757130035748556379)
                      ·
                        rfl

theorem cell23_7706952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_7706952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706952 prefixEnd_7706952 := by exact prefixLift 7706952
  have htrace : WordTrace (prefixWord ++ tailWord_7706952) baseStart_7706952 baseEnd_7706952 := by
    simpa [prefixWord, tailWord_7706952, baseEnd_7706952] using wordTrace_append hprefix tailTrace_7706952
  have hstable : (prefixWord ++ tailWord_7706952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706952).length < 2 ^ (prefixWord ++ tailWord_7706952).sum := by decide
  have hdescent : baseEnd_7706952 < baseStart_7706952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7706975 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 2, 6, 2]
def baseStart_7706975 : Nat := 118140960795 + 7706975 * 2 ^ 59
def prefixEnd_7706975 : Nat := 4983230072969 + 3 ^ 40 * 7706975 * 2
def baseEnd_7706975 : Nat := 3957382567185089158568773

theorem tailTrace_7706975 : CollatzResearch.WordTrace tailWord_7706975 prefixEnd_7706975 3957382567185089158568773 := by
  unfold tailWord_7706975
  simp only [CollatzResearch.WordTrace]
  refine ⟨281096471253953296383370379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187397647502635530922246919 281096471253953296383370379)
  ·
    refine ⟨421644706880929944575055569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281096471253953296383370379 421644706880929944575055569)
    ·
      refine ⟨316233530160697458431291677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421644706880929944575055569 316233530160697458431291677)
      ·
        refine ⟨118587573810261546911734379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316233530160697458431291677 118587573810261546911734379)
        ·
          refine ⟨177881360715392320367601569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118587573810261546911734379 177881360715392320367601569)
          ·
            refine ⟨133411020536544240275701177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177881360715392320367601569 133411020536544240275701177)
            ·
              refine ⟨100058265402408180206775883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133411020536544240275701177 100058265402408180206775883)
              ·
                refine ⟨150087398103612270310163825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100058265402408180206775883 150087398103612270310163825)
                ·
                  refine ⟨112565548577709202732622869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150087398103612270310163825 112565548577709202732622869)
                  ·
                    refine ⟨5276510089580118878091697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112565548577709202732622869 5276510089580118878091697)
                    ·
                      refine ⟨3957382567185089158568773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5276510089580118878091697 3957382567185089158568773)
                      ·
                        rfl

theorem cell23_7706975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_7706975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7706975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7706975 prefixEnd_7706975 := by exact prefixLift 7706975
  have htrace : WordTrace (prefixWord ++ tailWord_7706975) baseStart_7706975 baseEnd_7706975 := by
    simpa [prefixWord, tailWord_7706975, baseEnd_7706975] using wordTrace_append hprefix tailTrace_7706975
  have hstable : (prefixWord ++ tailWord_7706975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7706975).length < 2 ^ (prefixWord ++ tailWord_7706975).sum := by decide
  have hdescent : baseEnd_7706975 < baseStart_7706975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7706975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707022 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_7707022 : Nat := 118140960795 + 7707022 * 2 ^ 59
def prefixEnd_7707022 : Nat := 4983230072969 + 3 ^ 40 * 7707022 * 2
def baseEnd_7707022 : Nat := 3957406700775850474681057

theorem tailTrace_7707022 : CollatzResearch.WordTrace tailWord_7707022 prefixEnd_7707022 3957406700775850474681057 := by
  unfold tailWord_7707022
  simp only [CollatzResearch.WordTrace]
  refine ⟨35137273185597877926291415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187398790323188682273554213 35137273185597877926291415)
  ·
    refine ⟨52705909778396816889437123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35137273185597877926291415 52705909778396816889437123)
    ·
      refine ⟨79058864667595225334155685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52705909778396816889437123 79058864667595225334155685)
      ·
        refine ⟨14823537125174104750154191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79058864667595225334155685 14823537125174104750154191)
        ·
          refine ⟨22235305687761157125231287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14823537125174104750154191 22235305687761157125231287)
          ·
            refine ⟨33352958531641735687846931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22235305687761157125231287 33352958531641735687846931)
            ·
              refine ⟨50029437797462603531770397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33352958531641735687846931 50029437797462603531770397)
              ·
                refine ⟨18761039174048476324413899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50029437797462603531770397 18761039174048476324413899)
                ·
                  refine ⟨28141558761072714486620849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18761039174048476324413899 28141558761072714486620849)
                  ·
                    refine ⟨21106169070804535864965637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28141558761072714486620849 21106169070804535864965637)
                    ·
                      refine ⟨3957406700775850474681057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21106169070804535864965637 3957406700775850474681057)
                      ·
                        rfl

theorem cell23_7707022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_7707022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707022 prefixEnd_7707022 := by exact prefixLift 7707022
  have htrace : WordTrace (prefixWord ++ tailWord_7707022) baseStart_7707022 baseEnd_7707022 := by
    simpa [prefixWord, tailWord_7707022, baseEnd_7707022] using wordTrace_append hprefix tailTrace_7707022
  have hstable : (prefixWord ++ tailWord_7707022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707022).length < 2 ^ (prefixWord ++ tailWord_7707022).sum := by decide
  have hdescent : baseEnd_7707022 < baseStart_7707022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707032 : List Nat := [2, 1, 2, 5, 1, 2, 3, 7]
def baseStart_7707032 : Nat := 118140960795 + 7707032 * 2 ^ 59
def prefixEnd_7707032 : Nat := 4983230072969 + 3 ^ 40 * 7707032 * 2
def baseEnd_7707032 : Nat := 146570808725273905020593

theorem tailTrace_7707032 : CollatzResearch.WordTrace tailWord_7707032 prefixEnd_7707032 146570808725273905020593 := by
  unfold tailWord_7707032
  simp only [CollatzResearch.WordTrace]
  refine ⟨140549275107373397559097675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187399033476497863412130233 140549275107373397559097675)
  ·
    refine ⟨210823912661060096338646513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140549275107373397559097675 210823912661060096338646513)
    ·
      refine ⟨158117934495795072253984885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210823912661060096338646513 158117934495795072253984885)
      ·
        refine ⟨14823556358980788023811083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158117934495795072253984885 14823556358980788023811083)
        ·
          refine ⟨22235334538471182035716625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14823556358980788023811083 22235334538471182035716625)
          ·
            refine ⟨16676500903853386526787469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22235334538471182035716625 16676500903853386526787469)
            ·
              refine ⟨6253687838945019947545301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16676500903853386526787469 6253687838945019947545301)
              ·
                refine ⟨146570808725273905020593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6253687838945019947545301 146570808725273905020593)
                ·
                  rfl

theorem cell23_7707032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 7].length) (baseStart_7707032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707032 prefixEnd_7707032 := by exact prefixLift 7707032
  have htrace : WordTrace (prefixWord ++ tailWord_7707032) baseStart_7707032 baseEnd_7707032 := by
    simpa [prefixWord, tailWord_7707032, baseEnd_7707032] using wordTrace_append hprefix tailTrace_7707032
  have hstable : (prefixWord ++ tailWord_7707032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707032).length < 2 ^ (prefixWord ++ tailWord_7707032).sum := by decide
  have hdescent : baseEnd_7707032 < baseStart_7707032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707042 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_7707042 : Nat := 118140960795 + 7707042 * 2 ^ 59
def prefixEnd_7707042 : Nat := 4983230072969 + 3 ^ 40 * 7707042 * 2
def baseEnd_7707042 : Nat := 3957416970388940396430965

theorem tailTrace_7707042 : CollatzResearch.WordTrace tailWord_7707042 prefixEnd_7707042 3957416970388940396430965 := by
  unfold tailWord_7707042
  simp only [CollatzResearch.WordTrace]
  refine ⟨70274728736177641706514845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187399276629807044550706253 70274728736177641706514845)
  ·
    refine ⟨26353023276066615639943067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70274728736177641706514845 26353023276066615639943067)
    ·
      refine ⟨39529534914099923459914601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26353023276066615639943067 39529534914099923459914601)
      ·
        refine ⟨29647151185574942594935951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39529534914099923459914601 29647151185574942594935951)
        ·
          refine ⟨44470726778362413892403927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29647151185574942594935951 44470726778362413892403927)
          ·
            refine ⟨66706090167543620838605891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44470726778362413892403927 66706090167543620838605891)
            ·
              refine ⟨100059135251315431257908837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66706090167543620838605891 100059135251315431257908837)
              ·
                refine ⟨18761087859621643360857907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100059135251315431257908837 18761087859621643360857907)
                ·
                  refine ⟨28141631789432465041286861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18761087859621643360857907 28141631789432465041286861)
                  ·
                    refine ⟨10553111921037174390482573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28141631789432465041286861 10553111921037174390482573)
                    ·
                      refine ⟨3957416970388940396430965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10553111921037174390482573 3957416970388940396430965)
                      ·
                        rfl

theorem cell23_7707042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_7707042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707042 prefixEnd_7707042 := by exact prefixLift 7707042
  have htrace : WordTrace (prefixWord ++ tailWord_7707042) baseStart_7707042 baseEnd_7707042 := by
    simpa [prefixWord, tailWord_7707042, baseEnd_7707042] using wordTrace_append hprefix tailTrace_7707042
  have hstable : (prefixWord ++ tailWord_7707042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707042).length < 2 ^ (prefixWord ++ tailWord_7707042).sum := by decide
  have hdescent : baseEnd_7707042 < baseStart_7707042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707053 : List Nat := [1, 5, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_7707053 : Nat := 118140960795 + 7707053 * 2 ^ 59
def prefixEnd_7707053 : Nat := 4983230072969 + 3 ^ 40 * 7707053 * 2
def baseEnd_7707053 : Nat := 1319140872892046617797805

theorem tailTrace_7707053 : CollatzResearch.WordTrace tailWord_7707053 prefixEnd_7707053 1319140872892046617797805 := by
  unfold tailWord_7707053
  simp only [CollatzResearch.WordTrace]
  refine ⟨281099316147670715704709813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187399544098447143803139875 281099316147670715704709813)
  ·
    refine ⟨26353060888844129597316545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281099316147670715704709813 26353060888844129597316545)
    ·
      refine ⟨19764795666633097197987409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26353060888844129597316545 19764795666633097197987409)
      ·
        refine ⟨14823596749974822898490557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19764795666633097197987409 14823596749974822898490557)
        ·
          refine ⟨5558848781240558586933959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14823596749974822898490557 5558848781240558586933959)
          ·
            refine ⟨8338273171860837880400939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5558848781240558586933959 8338273171860837880400939)
            ·
              refine ⟨12507409757791256820601409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8338273171860837880400939 12507409757791256820601409)
              ·
                refine ⟨9380557318343442615451057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12507409757791256820601409 9380557318343442615451057)
                ·
                  refine ⟨7035417988757581961588293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9380557318343442615451057 7035417988757581961588293)
                  ·
                    refine ⟨1319140872892046617797805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7035417988757581961588293 1319140872892046617797805)
                    ·
                      rfl

theorem cell23_7707053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_7707053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707053 prefixEnd_7707053 := by exact prefixLift 7707053
  have htrace : WordTrace (prefixWord ++ tailWord_7707053) baseStart_7707053 baseEnd_7707053 := by
    simpa [prefixWord, tailWord_7707053, baseEnd_7707053] using wordTrace_append hprefix tailTrace_7707053
  have hstable : (prefixWord ++ tailWord_7707053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707053).length < 2 ^ (prefixWord ++ tailWord_7707053).sum := by decide
  have hdescent : baseEnd_7707053 < baseStart_7707053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707060 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_7707060 : Nat := 118140960795 + 7707060 * 2 ^ 59
def prefixEnd_7707060 : Nat := 4983230072969 + 3 ^ 40 * 7707060 * 2
def baseEnd_7707060 : Nat := 3957426213040721326005883

theorem tailTrace_7707060 : CollatzResearch.WordTrace tailWord_7707060 prefixEnd_7707060 3957426213040721326005883 := by
  unfold tailWord_7707060
  simp only [CollatzResearch.WordTrace]
  refine ⟨140549785729322677950107317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187399714305763570600143089 140549785729322677950107317)
  ·
    refine ⟨13176542412124001057822561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140549785729322677950107317 13176542412124001057822561)
    ·
      refine ⟨9882406809093000793366921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13176542412124001057822561 9882406809093000793366921)
      ·
        refine ⟨7411805106819750595025191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9882406809093000793366921 7411805106819750595025191)
        ·
          refine ⟨11117707660229625892537787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7411805106819750595025191 11117707660229625892537787)
          ·
            refine ⟨16676561490344438838806681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11117707660229625892537787 16676561490344438838806681)
            ·
              refine ⟨12507421117758329129105011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16676561490344438838806681 12507421117758329129105011)
              ·
                refine ⟨18761131676637493693657517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12507421117758329129105011 18761131676637493693657517)
                ·
                  refine ⟨7035424378739060135121569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18761131676637493693657517 7035424378739060135121569)
                  ·
                    refine ⟨5276568284054295101341177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7035424378739060135121569 5276568284054295101341177)
                    ·
                      refine ⟨3957426213040721326005883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5276568284054295101341177 3957426213040721326005883)
                      ·
                        rfl

theorem cell23_7707060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_7707060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707060 prefixEnd_7707060 := by exact prefixLift 7707060
  have htrace : WordTrace (prefixWord ++ tailWord_7707060) baseStart_7707060 baseEnd_7707060 := by
    simpa [prefixWord, tailWord_7707060, baseEnd_7707060] using wordTrace_append hprefix tailTrace_7707060
  have hstable : (prefixWord ++ tailWord_7707060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707060).length < 2 ^ (prefixWord ++ tailWord_7707060).sum := by decide
  have hdescent : baseEnd_7707060 < baseStart_7707060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707073 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7707073 : Nat := 118140960795 + 7707073 * 2 ^ 59
def prefixEnd_7707073 : Nat := 4983230072969 + 3 ^ 40 * 7707073 * 2
def baseEnd_7707073 : Nat := 3957432888289229775143323

theorem tailTrace_7707073 : CollatzResearch.WordTrace tailWord_7707073 prefixEnd_7707073 3957432888289229775143323 := by
  unfold tailWord_7707073
  simp only [CollatzResearch.WordTrace]
  refine ⟨281100045607598259120437873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187400030405065506080291915 281100045607598259120437873)
  ·
    refine ⟨210825034205698694340328405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281100045607598259120437873 210825034205698694340328405)
    ·
      refine ⟨4941211739196063148601447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 210825034205698694340328405 4941211739196063148601447)
      ·
        refine ⟨7411817608794094722902171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4941211739196063148601447 7411817608794094722902171)
        ·
          refine ⟨11117726413191142084353257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7411817608794094722902171 11117726413191142084353257)
          ·
            refine ⟨8338294809893356563264943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11117726413191142084353257 8338294809893356563264943)
            ·
              refine ⟨12507442214840034844897415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8338294809893356563264943 12507442214840034844897415)
              ·
                refine ⟨18761163322260052267346123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12507442214840034844897415 18761163322260052267346123)
                ·
                  refine ⟨28141744983390078401019185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18761163322260052267346123 28141744983390078401019185)
                  ·
                    refine ⟨21106308737542558800764389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28141744983390078401019185 21106308737542558800764389)
                    ·
                      refine ⟨3957432888289229775143323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21106308737542558800764389 3957432888289229775143323)
                      ·
                        rfl

theorem cell23_7707073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7707073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707073 prefixEnd_7707073 := by exact prefixLift 7707073
  have htrace : WordTrace (prefixWord ++ tailWord_7707073) baseStart_7707073 baseEnd_7707073 := by
    simpa [prefixWord, tailWord_7707073, baseEnd_7707073] using wordTrace_append hprefix tailTrace_7707073
  have hstable : (prefixWord ++ tailWord_7707073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707073).length < 2 ^ (prefixWord ++ tailWord_7707073).sum := by decide
  have hdescent : baseEnd_7707073 < baseStart_7707073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707076 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_7707076 : Nat := 118140960795 + 7707076 * 2 ^ 59
def prefixEnd_7707076 : Nat := 4983230072969 + 3 ^ 40 * 7707076 * 2
def baseEnd_7707076 : Nat := 3957434428731193263405809

theorem tailTrace_7707076 : CollatzResearch.WordTrace tailWord_7707076 prefixEnd_7707076 3957434428731193263405809 := by
  unfold tailWord_7707076
  simp only [CollatzResearch.WordTrace]
  refine ⟨140550077513293695316398541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187400103351058260421864721 140550077513293695316398541)
  ·
    refine ⟨52706279067485135743649453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140550077513293695316398541 52706279067485135743649453)
    ·
      refine ⟨19764854650306925903868545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52706279067485135743649453 19764854650306925903868545)
      ·
        refine ⟨14823640987730194427901409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19764854650306925903868545 14823640987730194427901409)
        ·
          refine ⟨11117730740797645820926057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14823640987730194427901409 11117730740797645820926057)
          ·
            refine ⟨8338298055598234365694543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11117730740797645820926057 8338298055598234365694543)
            ·
              refine ⟨12507447083397351548541815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8338298055598234365694543 12507447083397351548541815)
              ·
                refine ⟨18761170625096027322812723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12507447083397351548541815 18761170625096027322812723)
                ·
                  refine ⟨28141755937644040984219085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18761170625096027322812723 28141755937644040984219085)
                  ·
                    refine ⟨10553158476616515369082157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28141755937644040984219085 10553158476616515369082157)
                    ·
                      refine ⟨3957434428731193263405809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10553158476616515369082157 3957434428731193263405809)
                      ·
                        rfl

theorem cell23_7707076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_7707076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707076 prefixEnd_7707076 := by exact prefixLift 7707076
  have htrace : WordTrace (prefixWord ++ tailWord_7707076) baseStart_7707076 baseEnd_7707076 := by
    simpa [prefixWord, tailWord_7707076, baseEnd_7707076] using wordTrace_append hprefix tailTrace_7707076
  have hstable : (prefixWord ++ tailWord_7707076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707076).length < 2 ^ (prefixWord ++ tailWord_7707076).sum := by decide
  have hdescent : baseEnd_7707076 < baseStart_7707076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707135 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 4, 5]
def baseStart_7707135 : Nat := 118140960795 + 7707135 * 2 ^ 59
def prefixEnd_7707135 : Nat := 4983230072969 + 3 ^ 40 * 7707135 * 2
def baseEnd_7707135 : Nat := 1319154908029936177522679

theorem tailTrace_7707135 : CollatzResearch.WordTrace tailWord_7707135 prefixEnd_7707135 1319154908029936177522679 := by
  unfold tailWord_7707135
  simp only [CollatzResearch.WordTrace]
  refine ⟨281102306933373643709194859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187401537955582429139463239 281102306933373643709194859)
  ·
    refine ⟨421653460400060465563792289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281102306933373643709194859 421653460400060465563792289)
    ·
      refine ⟨316240095300045349172844217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421653460400060465563792289 316240095300045349172844217)
      ·
        refine ⟨237180071475034011879633163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316240095300045349172844217 237180071475034011879633163)
        ·
          refine ⟨355770107212551017819449745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237180071475034011879633163 355770107212551017819449745)
          ·
            refine ⟨266827580409413263364587309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355770107212551017819449745 266827580409413263364587309)
            ·
              refine ⟨100060342653529973761720241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266827580409413263364587309 100060342653529973761720241)
              ·
                refine ⟨75045256990147480321290181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100060342653529973761720241 75045256990147480321290181)
                ·
                  refine ⟨14070985685652652560241909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75045256990147480321290181 14070985685652652560241909)
                  ·
                    refine ⟨1319154908029936177522679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14070985685652652560241909 1319154908029936177522679)
                    ·
                      rfl

theorem cell23_7707135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 5].length) (baseStart_7707135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707135 prefixEnd_7707135 := by exact prefixLift 7707135
  have htrace : WordTrace (prefixWord ++ tailWord_7707135) baseStart_7707135 baseEnd_7707135 := by
    simpa [prefixWord, tailWord_7707135, baseEnd_7707135] using wordTrace_append hprefix tailTrace_7707135
  have hstable : (prefixWord ++ tailWord_7707135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707135).length < 2 ^ (prefixWord ++ tailWord_7707135).sum := by decide
  have hdescent : baseEnd_7707135 < baseStart_7707135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707189 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_7707189 : Nat := 118140960795 + 7707189 * 2 ^ 59
def prefixEnd_7707189 : Nat := 4983230072969 + 3 ^ 40 * 7707189 * 2
def baseEnd_7707189 : Nat := 3957492452045151321292789

theorem tailTrace_7707189 : CollatzResearch.WordTrace tailWord_7707189 prefixEnd_7707189 3957492452045151321292789 := by
  unfold tailWord_7707189
  simp only [CollatzResearch.WordTrace]
  refine ⟨281104276475178010931660621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187402850983452007287773747 281104276475178010931660621)
  ·
    refine ⟨105414103678191754099372733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281104276475178010931660621 105414103678191754099372733)
    ·
      refine ⟨39530288879321907787264775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105414103678191754099372733 39530288879321907787264775)
      ·
        refine ⟨59295433318982861680897163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39530288879321907787264775 59295433318982861680897163)
        ·
          refine ⟨88943149978474292521345745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59295433318982861680897163 88943149978474292521345745)
          ·
            refine ⟨66707362483855719391009309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88943149978474292521345745 66707362483855719391009309)
            ·
              refine ⟨25015260931445894771628491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66707362483855719391009309 25015260931445894771628491)
              ·
                refine ⟨37522891397168842157442737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25015260931445894771628491 37522891397168842157442737)
                ·
                  refine ⟨28142168547876631618082053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37522891397168842157442737 28142168547876631618082053)
                  ·
                    refine ⟨5276656602726868428390385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28142168547876631618082053 5276656602726868428390385)
                    ·
                      refine ⟨3957492452045151321292789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5276656602726868428390385 3957492452045151321292789)
                      ·
                        rfl

theorem cell23_7707189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_7707189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707189 prefixEnd_7707189 := by exact prefixLift 7707189
  have htrace : WordTrace (prefixWord ++ tailWord_7707189) baseStart_7707189 baseEnd_7707189 := by
    simpa [prefixWord, tailWord_7707189, baseEnd_7707189] using wordTrace_append hprefix tailTrace_7707189
  have hstable : (prefixWord ++ tailWord_7707189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707189).length < 2 ^ (prefixWord ++ tailWord_7707189).sum := by decide
  have hdescent : baseEnd_7707189 < baseStart_7707189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707192 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 1, 4, 3]
def baseStart_7707192 : Nat := 118140960795 + 7707192 * 2 ^ 59
def prefixEnd_7707192 : Nat := 4983230072969 + 3 ^ 40 * 7707192 * 2
def baseEnd_7707192 : Nat := 3957493992487114809555275

theorem tailTrace_7707192 : CollatzResearch.WordTrace tailWord_7707192 prefixEnd_7707192 3957493992487114809555275 := by
  unfold tailWord_7707192
  simp only [CollatzResearch.WordTrace]
  refine ⟨140552192947083571222009915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187402923929444761629346553 140552192947083571222009915)
  ·
    refine ⟨210828289420625356833014873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140552192947083571222009915 210828289420625356833014873)
    ·
      refine ⟨158121217065469017624761155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210828289420625356833014873 158121217065469017624761155)
      ·
        refine ⟨237181825598203526437141733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158121217065469017624761155 237181825598203526437141733)
        ·
          refine ⟨44471592299663161206964075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237181825598203526437141733 44471592299663161206964075)
          ·
            refine ⟨66707388449494741810446113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44471592299663161206964075 66707388449494741810446113)
            ·
              refine ⟨50030541337121056357834585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66707388449494741810446113 50030541337121056357834585)
              ·
                refine ⟨37522906002840792268375939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50030541337121056357834585 37522906002840792268375939)
                ·
                  refine ⟨56284359004261188402563909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37522906002840792268375939 56284359004261188402563909)
                  ·
                    refine ⟨10553317313298972825480733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56284359004261188402563909 10553317313298972825480733)
                    ·
                      refine ⟨3957493992487114809555275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10553317313298972825480733 3957493992487114809555275)
                      ·
                        rfl

theorem cell23_7707192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_7707192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707192 prefixEnd_7707192 := by exact prefixLift 7707192
  have htrace : WordTrace (prefixWord ++ tailWord_7707192) baseStart_7707192 baseEnd_7707192 := by
    simpa [prefixWord, tailWord_7707192, baseEnd_7707192] using wordTrace_append hprefix tailTrace_7707192
  have hstable : (prefixWord ++ tailWord_7707192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707192).length < 2 ^ (prefixWord ++ tailWord_7707192).sum := by decide
  have hdescent : baseEnd_7707192 < baseStart_7707192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707206 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_7707206 : Nat := 118140960795 + 7707206 * 2 ^ 59
def prefixEnd_7707206 : Nat := 4983230072969 + 3 ^ 40 * 7707206 * 2
def baseEnd_7707206 : Nat := 3957501181216277754780211

theorem tailTrace_7707206 : CollatzResearch.WordTrace tailWord_7707206 prefixEnd_7707206 3957501181216277754780211 := by
  unfold tailWord_7707206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8784528016128638213594671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187403264344077615223352981 8784528016128638213594671)
  ·
    refine ⟨13176792024192957320392007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8784528016128638213594671 13176792024192957320392007)
    ·
      refine ⟨19765188036289435980588011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13176792024192957320392007 19765188036289435980588011)
      ·
        refine ⟨29647782054434153970882017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19765188036289435980588011 29647782054434153970882017)
        ·
          refine ⟨22235836540825615478161513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29647782054434153970882017 22235836540825615478161513)
          ·
            refine ⟨16676877405619211608621135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22235836540825615478161513 16676877405619211608621135)
            ·
              refine ⟨25015316108428817412931703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16676877405619211608621135 25015316108428817412931703)
              ·
                refine ⟨37522974162643226119397555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25015316108428817412931703 37522974162643226119397555)
                ·
                  refine ⟨56284461243964839179096333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37522974162643226119397555 56284461243964839179096333)
                  ·
                    refine ⟨21106672966486814692161125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56284461243964839179096333 21106672966486814692161125)
                    ·
                      refine ⟨3957501181216277754780211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21106672966486814692161125 3957501181216277754780211)
                      ·
                        rfl

theorem cell23_7707206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_7707206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707206 prefixEnd_7707206 := by exact prefixLift 7707206
  have htrace : WordTrace (prefixWord ++ tailWord_7707206) baseStart_7707206 baseEnd_7707206 := by
    simpa [prefixWord, tailWord_7707206, baseEnd_7707206] using wordTrace_append hprefix tailTrace_7707206
  have hstable : (prefixWord ++ tailWord_7707206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707206).length < 2 ^ (prefixWord ++ tailWord_7707206).sum := by decide
  have hdescent : baseEnd_7707206 < baseStart_7707206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707246 : List Nat := [4, 1, 2, 2, 2, 2, 3, 1, 6]
def baseStart_7707246 : Nat := 118140960795 + 7707246 * 2 ^ 59
def prefixEnd_7707246 : Nat := 4983230072969 + 3 ^ 40 * 7707246 * 2
def baseEnd_7707246 : Nat := 439724635604717510920003

theorem tailTrace_7707246 : CollatzResearch.WordTrace tailWord_7707246 prefixEnd_7707246 439724635604717510920003 := by
  unfold tailWord_7707246
  simp only [CollatzResearch.WordTrace]
  refine ⟨35138294429496438708310699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187404236957314339777657061 35138294429496438708310699)
  ·
    refine ⟨52707441644244658062466049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35138294429496438708310699 52707441644244658062466049)
    ·
      refine ⟨39530581233183493546849537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52707441644244658062466049 39530581233183493546849537)
      ·
        refine ⟨29647935924887620160137153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39530581233183493546849537 29647935924887620160137153)
        ·
          refine ⟨22235951943665715120102865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29647935924887620160137153 22235951943665715120102865)
          ·
            refine ⟨16676963957749286340077149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22235951943665715120102865 16676963957749286340077149)
            ·
              refine ⟨6253861484155982377528931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16676963957749286340077149 6253861484155982377528931)
              ·
                refine ⟨9380792226233973566293397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6253861484155982377528931 9380792226233973566293397)
                ·
                  refine ⟨439724635604717510920003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9380792226233973566293397 439724635604717510920003)
                  ·
                    rfl

theorem cell23_7707246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_7707246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707246 prefixEnd_7707246 := by exact prefixLift 7707246
  have htrace : WordTrace (prefixWord ++ tailWord_7707246) baseStart_7707246 baseEnd_7707246 := by
    simpa [prefixWord, tailWord_7707246, baseEnd_7707246] using wordTrace_append hprefix tailTrace_7707246
  have hstable : (prefixWord ++ tailWord_7707246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707246).length < 2 ^ (prefixWord ++ tailWord_7707246).sum := by decide
  have hdescent : baseEnd_7707246 < baseStart_7707246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707289 : List Nat := [1, 2, 1, 2, 1, 2, 4, 4, 2, 4]
def baseStart_7707289 : Nat := 118140960795 + 7707289 * 2 ^ 59
def prefixEnd_7707289 : Nat := 4983230072969 + 3 ^ 40 * 7707289 * 2
def baseEnd_7707289 : Nat := 1319181266703533643347443

theorem tailTrace_7707289 : CollatzResearch.WordTrace tailWord_7707289 prefixEnd_7707289 1319181266703533643347443 := by
  unfold tailWord_7707289
  simp only [CollatzResearch.WordTrace]
  refine ⟨281107923774815728010300921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187405282516543818673533947 281107923774815728010300921)
  ·
    refine ⟨210830942831111796007725691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281107923774815728010300921 210830942831111796007725691)
    ·
      refine ⟨316246414246667694011588537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210830942831111796007725691 316246414246667694011588537)
      ·
        refine ⟨237184810685000770508691403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316246414246667694011588537 237184810685000770508691403)
        ·
          refine ⟨355777216027501155763037105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237184810685000770508691403 355777216027501155763037105)
          ·
            refine ⟨266832912020625866822277829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355777216027501155763037105 266832912020625866822277829)
            ·
              refine ⟨50031171003867350029177093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266832912020625866822277829 50031171003867350029177093)
              ·
                refine ⟨9380844563225128130470705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50031171003867350029177093 9380844563225128130470705)
                ·
                  refine ⟨7035633422418846097853029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9380844563225128130470705 7035633422418846097853029)
                  ·
                    refine ⟨1319181266703533643347443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7035633422418846097853029 1319181266703533643347443)
                    ·
                      rfl

theorem cell23_7707289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 4].length) (baseStart_7707289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707289 prefixEnd_7707289 := by exact prefixLift 7707289
  have htrace : WordTrace (prefixWord ++ tailWord_7707289) baseStart_7707289 baseEnd_7707289 := by
    simpa [prefixWord, tailWord_7707289, baseEnd_7707289] using wordTrace_append hprefix tailTrace_7707289
  have hstable : (prefixWord ++ tailWord_7707289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707289).length < 2 ^ (prefixWord ++ tailWord_7707289).sum := by decide
  have hdescent : baseEnd_7707289 < baseStart_7707289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707290 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7707290 : Nat := 118140960795 + 7707290 * 2 ^ 59
def prefixEnd_7707290 : Nat := 4983230072969 + 3 ^ 40 * 7707290 * 2
def baseEnd_7707290 : Nat := 3957544313591255426129825

theorem tailTrace_7707290 : CollatzResearch.WordTrace tailWord_7707290 prefixEnd_7707290 3957544313591255426129825 := by
  unfold tailWord_7707290
  simp only [CollatzResearch.WordTrace]
  refine ⟨70276990061953026295271831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187405306831874736787391549 70276990061953026295271831)
  ·
    refine ⟨105415485092929539442907747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70276990061953026295271831 105415485092929539442907747)
    ·
      refine ⟨158123227639394309164361621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105415485092929539442907747 158123227639394309164361621)
      ·
        refine ⟨7412026295596608242079451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158123227639394309164361621 7412026295596608242079451)
        ·
          refine ⟨11118039443394912363119177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7412026295596608242079451 11118039443394912363119177)
          ·
            refine ⟨8338529582546184272339383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11118039443394912363119177 8338529582546184272339383)
            ·
              refine ⟨12507794373819276408509075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8338529582546184272339383 12507794373819276408509075)
              ·
                refine ⟨18761691560728914612763613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12507794373819276408509075 18761691560728914612763613)
                ·
                  refine ⟨7035634335273342979786355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18761691560728914612763613 7035634335273342979786355)
                  ·
                    refine ⟨10553451502910014469679533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7035634335273342979786355 10553451502910014469679533)
                    ·
                      refine ⟨3957544313591255426129825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10553451502910014469679533 3957544313591255426129825)
                      ·
                        rfl

theorem cell23_7707290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7707290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707290 prefixEnd_7707290 := by exact prefixLift 7707290
  have htrace : WordTrace (prefixWord ++ tailWord_7707290) baseStart_7707290 baseEnd_7707290 := by
    simpa [prefixWord, tailWord_7707290, baseEnd_7707290] using wordTrace_append hprefix tailTrace_7707290
  have hstable : (prefixWord ++ tailWord_7707290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707290).length < 2 ^ (prefixWord ++ tailWord_7707290).sum := by decide
  have hdescent : baseEnd_7707290 < baseStart_7707290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707309 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_7707309 : Nat := 118140960795 + 7707309 * 2 ^ 59
def prefixEnd_7707309 : Nat := 4983230072969 + 3 ^ 40 * 7707309 * 2
def baseEnd_7707309 : Nat := 3957554069723690851792237

theorem tailTrace_7707309 : CollatzResearch.WordTrace tailWord_7707309 prefixEnd_7707309 3957554069723690851792237 := by
  unfold tailWord_7707309
  simp only [CollatzResearch.WordTrace]
  refine ⟨281108653234743271426028981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187405768823162180950685987 281108653234743271426028981)
  ·
    refine ⟨26353936240757181696190217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281108653234743271426028981 26353936240757181696190217)
    ·
      refine ⟨19765452180567886272142663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26353936240757181696190217 19765452180567886272142663)
      ·
        refine ⟨29648178270851829408213995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19765452180567886272142663 29648178270851829408213995)
        ·
          refine ⟨44472267406277744112320993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29648178270851829408213995 44472267406277744112320993)
          ·
            refine ⟨33354200554708308084240745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44472267406277744112320993 33354200554708308084240745)
            ·
              refine ⟨25015650416031231063180559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33354200554708308084240745 25015650416031231063180559)
              ·
                refine ⟨37523475624046846594770839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25015650416031231063180559 37523475624046846594770839)
                ·
                  refine ⟨56285213436070269892156259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37523475624046846594770839 56285213436070269892156259)
                  ·
                    refine ⟨84427820154105404838234389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56285213436070269892156259 84427820154105404838234389)
                    ·
                      refine ⟨3957554069723690851792237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84427820154105404838234389 3957554069723690851792237)
                      ·
                        rfl

theorem cell23_7707309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_7707309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707309 prefixEnd_7707309 := by exact prefixLift 7707309
  have htrace : WordTrace (prefixWord ++ tailWord_7707309) baseStart_7707309 baseEnd_7707309 := by
    simpa [prefixWord, tailWord_7707309, baseEnd_7707309] using wordTrace_append hprefix tailTrace_7707309
  have hstable : (prefixWord ++ tailWord_7707309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707309).length < 2 ^ (prefixWord ++ tailWord_7707309).sum := by decide
  have hdescent : baseEnd_7707309 < baseStart_7707309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707341 : List Nat := [1, 6, 2, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_7707341 : Nat := 118140960795 + 7707341 * 2 ^ 59
def prefixEnd_7707341 : Nat := 4983230072969 + 3 ^ 40 * 7707341 * 2
def baseEnd_7707341 : Nat := 3957570501104634726592091

theorem tailTrace_7707341 : CollatzResearch.WordTrace tailWord_7707341 prefixEnd_7707341 3957570501104634726592091 := by
  unfold tailWord_7707341
  simp only [CollatzResearch.WordTrace]
  refine ⟨281109820370627340891193877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187406546913751560594129251 281109820370627340891193877)
  ·
    refine ⟨13177022829873156604274713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 281109820370627340891193877 13177022829873156604274713)
    ·
      refine ⟨9882767122404867453206035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13177022829873156604274713 9882767122404867453206035)
      ·
        refine ⟨14824150683607301179809053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9882767122404867453206035 14824150683607301179809053)
        ·
          refine ⟨5559056506352737942428395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14824150683607301179809053 5559056506352737942428395)
          ·
            refine ⟨8338584759529106913642593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559056506352737942428395 8338584759529106913642593)
            ·
              refine ⟨6253938569646830185231945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8338584759529106913642593 6253938569646830185231945)
              ·
                refine ⟨4690453927235122638923959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6253938569646830185231945 4690453927235122638923959)
                ·
                  refine ⟨7035680890852683958385939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4690453927235122638923959 7035680890852683958385939)
                  ·
                    refine ⟨10553521336279025937578909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7035680890852683958385939 10553521336279025937578909)
                    ·
                      refine ⟨3957570501104634726592091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10553521336279025937578909 3957570501104634726592091)
                      ·
                        rfl

theorem cell23_7707341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_7707341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707341 prefixEnd_7707341 := by exact prefixLift 7707341
  have htrace : WordTrace (prefixWord ++ tailWord_7707341) baseStart_7707341 baseEnd_7707341 := by
    simpa [prefixWord, tailWord_7707341, baseEnd_7707341] using wordTrace_append hprefix tailTrace_7707341
  have hstable : (prefixWord ++ tailWord_7707341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707341).length < 2 ^ (prefixWord ++ tailWord_7707341).sum := by decide
  have hdescent : baseEnd_7707341 < baseStart_7707341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707363 : List Nat := [1, 1, 1, 7, 1, 1, 2, 3, 2, 1, 3]
def baseStart_7707363 : Nat := 118140960795 + 7707363 * 2 ^ 59
def prefixEnd_7707363 : Nat := 4983230072969 + 3 ^ 40 * 7707363 * 2
def baseEnd_7707363 : Nat := 3957581797679033640516989

theorem tailTrace_7707363 : CollatzResearch.WordTrace tailWord_7707363 prefixEnd_7707363 3957581797679033640516989 := by
  unfold tailWord_7707363
  simp only [CollatzResearch.WordTrace]
  refine ⟨281110622776547638648494743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187407081851031759098996495 281110622776547638648494743)
  ·
    refine ⟨421665934164821457972742115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281110622776547638648494743 421665934164821457972742115)
    ·
      refine ⟨632498901247232186959113173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421665934164821457972742115 632498901247232186959113173)
      ·
        refine ⟨14824192997982004381854215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 632498901247232186959113173 14824192997982004381854215)
        ·
          refine ⟨22236289496973006572781323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14824192997982004381854215 22236289496973006572781323)
          ·
            refine ⟨33354434245459509859171985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22236289496973006572781323 33354434245459509859171985)
            ·
              refine ⟨25015825684094632394378989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33354434245459509859171985 25015825684094632394378989)
              ·
                refine ⟨9380934631535487147892121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25015825684094632394378989 9380934631535487147892121)
                ·
                  refine ⟨7035700973651615360919091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9380934631535487147892121 7035700973651615360919091)
                  ·
                    refine ⟨10553551460477423041378637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7035700973651615360919091 10553551460477423041378637)
                    ·
                      refine ⟨3957581797679033640516989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10553551460477423041378637 3957581797679033640516989)
                      ·
                        rfl

theorem cell23_7707363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_7707363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707363 prefixEnd_7707363 := by exact prefixLift 7707363
  have htrace : WordTrace (prefixWord ++ tailWord_7707363) baseStart_7707363 baseEnd_7707363 := by
    simpa [prefixWord, tailWord_7707363, baseEnd_7707363] using wordTrace_append hprefix tailTrace_7707363
  have hstable : (prefixWord ++ tailWord_7707363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707363).length < 2 ^ (prefixWord ++ tailWord_7707363).sum := by decide
  have hdescent : baseEnd_7707363 < baseStart_7707363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707373 : List Nat := [1, 5, 1, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_7707373 : Nat := 118140960795 + 7707373 * 2 ^ 59
def prefixEnd_7707373 : Nat := 4983230072969 + 3 ^ 40 * 7707373 * 2
def baseEnd_7707373 : Nat := 3957586932485578601391943

theorem tailTrace_7707373 : CollatzResearch.WordTrace tailWord_7707373 prefixEnd_7707373 3957586932485578601391943 := by
  unfold tailWord_7707373
  simp only [CollatzResearch.WordTrace]
  refine ⟨281110987506511410356358773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187407325004340940237572515 281110987506511410356358773)
  ·
    refine ⟨26354155078735444720908635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281110987506511410356358773 26354155078735444720908635)
    ·
      refine ⟨39531232618103167081362953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26354155078735444720908635 39531232618103167081362953)
      ·
        refine ⟨29648424463577375311022215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39531232618103167081362953 29648424463577375311022215)
        ·
          refine ⟨44472636695366062966533323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29648424463577375311022215 44472636695366062966533323)
          ·
            refine ⟨66708955043049094449799985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44472636695366062966533323 66708955043049094449799985)
            ·
              refine ⟨50031716282286820837349989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66708955043049094449799985 50031716282286820837349989)
              ·
                refine ⟨9380946802928778907003123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50031716282286820837349989 9380946802928778907003123)
                ·
                  refine ⟨14071420204393168360504685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9380946802928778907003123 14071420204393168360504685)
                  ·
                    refine ⟨5276782576647438135189257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14071420204393168360504685 5276782576647438135189257)
                    ·
                      refine ⟨3957586932485578601391943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5276782576647438135189257 3957586932485578601391943)
                      ·
                        rfl

theorem cell23_7707373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_7707373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707373 prefixEnd_7707373 := by exact prefixLift 7707373
  have htrace : WordTrace (prefixWord ++ tailWord_7707373) baseStart_7707373 baseEnd_7707373 := by
    simpa [prefixWord, tailWord_7707373, baseEnd_7707373] using wordTrace_append hprefix tailTrace_7707373
  have hstable : (prefixWord ++ tailWord_7707373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707373).length < 2 ^ (prefixWord ++ tailWord_7707373).sum := by decide
  have hdescent : baseEnd_7707373 < baseStart_7707373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707381 : List Nat := [1, 3, 6, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7707381 : Nat := 118140960795 + 7707381 * 2 ^ 59
def prefixEnd_7707381 : Nat := 4983230072969 + 3 ^ 40 * 7707381 * 2
def baseEnd_7707381 : Nat := 3957591040330814570091907

theorem tailTrace_7707381 : CollatzResearch.WordTrace tailWord_7707381 prefixEnd_7707381 3957591040330814570091907 := by
  unfold tailWord_7707381
  simp only [CollatzResearch.WordTrace]
  refine ⟨281111279290482427722649997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187407519526988285148433331 281111279290482427722649997)
  ·
    refine ⟨105416729733930910395993749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281111279290482427722649997 105416729733930910395993749)
    ·
      refine ⟨4941409206278011424812207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105416729733930910395993749 4941409206278011424812207)
      ·
        refine ⟨7412113809417017137218311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4941409206278011424812207 7412113809417017137218311)
        ·
          refine ⟨11118170714125525705827467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7412113809417017137218311 11118170714125525705827467)
          ·
            refine ⟨16677256071188288558741201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11118170714125525705827467 16677256071188288558741201)
            ·
              refine ⟨12507942053391216419055901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16677256071188288558741201 12507942053391216419055901)
              ·
                refine ⟨4690478270021706157145963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12507942053391216419055901 4690478270021706157145963)
                ·
                  refine ⟨7035717405032559235718945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4690478270021706157145963 7035717405032559235718945)
                  ·
                    refine ⟨5276788053774419426789209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7035717405032559235718945 5276788053774419426789209)
                    ·
                      refine ⟨3957591040330814570091907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5276788053774419426789209 3957591040330814570091907)
                      ·
                        rfl

theorem cell23_7707381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7707381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707381 prefixEnd_7707381 := by exact prefixLift 7707381
  have htrace : WordTrace (prefixWord ++ tailWord_7707381) baseStart_7707381 baseEnd_7707381 := by
    simpa [prefixWord, tailWord_7707381, baseEnd_7707381] using wordTrace_append hprefix tailTrace_7707381
  have hstable : (prefixWord ++ tailWord_7707381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707381).length < 2 ^ (prefixWord ++ tailWord_7707381).sum := by decide
  have hdescent : baseEnd_7707381 < baseStart_7707381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707386 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2]
def baseStart_7707386 : Nat := 118140960795 + 7707386 * 2 ^ 59
def prefixEnd_7707386 : Nat := 4983230072969 + 3 ^ 40 * 7707386 * 2
def baseEnd_7707386 : Nat := 3957593607734087050529383

theorem tailTrace_7707386 : CollatzResearch.WordTrace tailWord_7707386 prefixEnd_7707386 3957593607734087050529383 := by
  unfold tailWord_7707386
  simp only [CollatzResearch.WordTrace]
  refine ⟨70277865413866078394145503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187407641103642875717721341 70277865413866078394145503)
  ·
    refine ⟨105416798120799117591218255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70277865413866078394145503 105416798120799117591218255)
    ·
      refine ⟨158125197181198676386827383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105416798120799117591218255 158125197181198676386827383)
      ·
        refine ⟨237187795771798014580241075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158125197181198676386827383 237187795771798014580241075)
        ·
          refine ⟨355781693657697021870361613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237187795771798014580241075 355781693657697021870361613)
          ·
            refine ⟨133418135121636383201385605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355781693657697021870361613 133418135121636383201385605)
            ·
              refine ⟨25015900335306821850259801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133418135121636383201385605 25015900335306821850259801)
              ·
                refine ⟨18761925251480116387694851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25015900335306821850259801 18761925251480116387694851)
                ·
                  refine ⟨28142887877220174581542277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18761925251480116387694851 28142887877220174581542277)
                  ·
                    refine ⟨5276791476978782734039177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28142887877220174581542277 5276791476978782734039177)
                    ·
                      refine ⟨3957593607734087050529383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5276791476978782734039177 3957593607734087050529383)
                      ·
                        rfl

theorem cell23_7707386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2].length) (baseStart_7707386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707386 prefixEnd_7707386 := by exact prefixLift 7707386
  have htrace : WordTrace (prefixWord ++ tailWord_7707386) baseStart_7707386 baseEnd_7707386 := by
    simpa [prefixWord, tailWord_7707386, baseEnd_7707386] using wordTrace_append hprefix tailTrace_7707386
  have hstable : (prefixWord ++ tailWord_7707386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707386).length < 2 ^ (prefixWord ++ tailWord_7707386).sum := by decide
  have hdescent : baseEnd_7707386 < baseStart_7707386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707390 : List Nat := [4, 2, 2, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_7707390 : Nat := 118140960795 + 7707390 * 2 ^ 59
def prefixEnd_7707390 : Nat := 4983230072969 + 3 ^ 40 * 7707390 * 2
def baseEnd_7707390 : Nat := 3957595661656705034879365

theorem tailTrace_7707390 : CollatzResearch.WordTrace tailWord_7707390 prefixEnd_7707390 3957595661656705034879365 := by
  unfold tailWord_7707390
  simp only [CollatzResearch.WordTrace]
  refine ⟨35138950943431227782465953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187407738364966548173151749 35138950943431227782465953)
  ·
    refine ⟨26354213207573420836849465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35138950943431227782465953 26354213207573420836849465)
    ·
      refine ⟨19765659905680065627637099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26354213207573420836849465 19765659905680065627637099)
      ·
        refine ⟨29648489858520098441455649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19765659905680065627637099 29648489858520098441455649)
        ·
          refine ⟨22236367393890073831091737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29648489858520098441455649 22236367393890073831091737)
          ·
            refine ⟨16677275545417555373318803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22236367393890073831091737 16677275545417555373318803)
            ·
              refine ⟨25015913318126333059978205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16677275545417555373318803 25015913318126333059978205)
              ·
                refine ⟨9380967494297374897491827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25015913318126333059978205 9380967494297374897491827)
                ·
                  refine ⟨14071451241446062346237741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9380967494297374897491827 14071451241446062346237741)
                  ·
                    refine ⟨5276794215542273379839153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14071451241446062346237741 5276794215542273379839153)
                    ·
                      refine ⟨3957595661656705034879365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5276794215542273379839153 3957595661656705034879365)
                      ·
                        rfl

theorem cell23_7707390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_7707390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707390 prefixEnd_7707390 := by exact prefixLift 7707390
  have htrace : WordTrace (prefixWord ++ tailWord_7707390) baseStart_7707390 baseEnd_7707390 := by
    simpa [prefixWord, tailWord_7707390, baseEnd_7707390] using wordTrace_append hprefix tailTrace_7707390
  have hstable : (prefixWord ++ tailWord_7707390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707390).length < 2 ^ (prefixWord ++ tailWord_7707390).sum := by decide
  have hdescent : baseEnd_7707390 < baseStart_7707390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707443 : List Nat := [1, 1, 1, 2, 6, 3, 1, 3, 5]
def baseStart_7707443 : Nat := 118140960795 + 7707443 * 2 ^ 59
def prefixEnd_7707443 : Nat := 4983230072969 + 3 ^ 40 * 7707443 * 2
def baseEnd_7707443 : Nat := 439735875125710369724069

theorem tailTrace_7707443 : CollatzResearch.WordTrace tailWord_7707443 prefixEnd_7707443 439735875125710369724069 := by
  unfold tailWord_7707443
  simp only [CollatzResearch.WordTrace]
  refine ⟨281113540616257812311406983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187409027077505208207604655 281113540616257812311406983)
  ·
    refine ⟨421670310924386718467110475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281113540616257812311406983 421670310924386718467110475)
    ·
      refine ⟨632505466386580077700665713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421670310924386718467110475 632505466386580077700665713)
      ·
        refine ⟨474379099789935058275499285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632505466386580077700665713 474379099789935058275499285)
        ·
          refine ⟨22236520302653205856664029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 474379099789935058275499285 22236520302653205856664029)
          ·
            refine ⟨8338695113494952196249011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22236520302653205856664029 8338695113494952196249011)
            ·
              refine ⟨12508042670242428294373517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8338695113494952196249011 12508042670242428294373517)
              ·
                refine ⟨4690516001340910610390069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12508042670242428294373517 4690516001340910610390069)
                ·
                  refine ⟨439735875125710369724069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4690516001340910610390069 439735875125710369724069)
                  ·
                    rfl

theorem cell23_7707443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 5].length) (baseStart_7707443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707443 prefixEnd_7707443 := by exact prefixLift 7707443
  have htrace : WordTrace (prefixWord ++ tailWord_7707443) baseStart_7707443 baseEnd_7707443 := by
    simpa [prefixWord, tailWord_7707443, baseEnd_7707443] using wordTrace_append hprefix tailTrace_7707443
  have hstable : (prefixWord ++ tailWord_7707443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707443).length < 2 ^ (prefixWord ++ tailWord_7707443).sum := by decide
  have hdescent : baseEnd_7707443 < baseStart_7707443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707460 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 7]
def baseStart_7707460 : Nat := 118140960795 + 7707460 * 2 ^ 59
def prefixEnd_7707460 : Nat := 4983230072969 + 3 ^ 40 * 7707460 * 2
def baseEnd_7707460 : Nat := 439736845033613306778227

theorem tailTrace_7707460 : CollatzResearch.WordTrace tailWord_7707460 prefixEnd_7707460 439736845033613306778227 := by
  unfold tailWord_7707460
  simp only [CollatzResearch.WordTrace]
  refine ⟨140557080328598112107387917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187409440438130816143183889 140557080328598112107387917)
  ·
    refine ⟨52708905123224292040270469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140557080328598112107387917 52708905123224292040270469)
    ·
      refine ⟨9882919710604554757550713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52708905123224292040270469 9882919710604554757550713)
      ·
        refine ⟨7412189782953416068163035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9882919710604554757550713 7412189782953416068163035)
        ·
          refine ⟨11118284674430124102244553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7412189782953416068163035 11118284674430124102244553)
          ·
            refine ⟨8338713505822593076683415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11118284674430124102244553 8338713505822593076683415)
            ·
              refine ⟨12508070258733889615025123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8338713505822593076683415 12508070258733889615025123)
              ·
                refine ⟨18762105388100834422537685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12508070258733889615025123 18762105388100834422537685)
                ·
                  refine ⟨439736845033613306778227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18762105388100834422537685 439736845033613306778227)
                  ·
                    rfl

theorem cell23_7707460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_7707460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707460 prefixEnd_7707460 := by exact prefixLift 7707460
  have htrace : WordTrace (prefixWord ++ tailWord_7707460) baseStart_7707460 baseEnd_7707460 := by
    simpa [prefixWord, tailWord_7707460, baseEnd_7707460] using wordTrace_append hprefix tailTrace_7707460
  have hstable : (prefixWord ++ tailWord_7707460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707460).length < 2 ^ (prefixWord ++ tailWord_7707460).sum := by decide
  have hdescent : baseEnd_7707460 < baseStart_7707460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707543 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 3, 1, 3]
def baseStart_7707543 : Nat := 118140960795 + 7707543 * 2 ^ 59
def prefixEnd_7707543 : Nat := 4983230072969 + 3 ^ 40 * 7707543 * 2
def baseEnd_7707543 : Nat := 3957674224196842936266161

theorem tailTrace_7707543 : CollatzResearch.WordTrace tailWord_7707543 prefixEnd_7707543 3957674224196842936266161 := by
  unfold tailWord_7707543
  simp only [CollatzResearch.WordTrace]
  refine ⟨281117187915895529390047283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187411458610597019593364855 281117187915895529390047283)
  ·
    refine ⟨421675781873843294085070925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281117187915895529390047283 421675781873843294085070925)
    ·
      refine ⟨158128418202691235281901597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421675781873843294085070925 158128418202691235281901597)
      ·
        refine ⟨59298156826009213230713099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158128418202691235281901597 59298156826009213230713099)
        ·
          refine ⟨88947235239013819846069649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59298156826009213230713099 88947235239013819846069649)
          ·
            refine ⟨66710426429260364884552237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88947235239013819846069649 66710426429260364884552237)
            ·
              refine ⟨25016409910972636831707089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66710426429260364884552237 25016409910972636831707089)
              ·
                refine ⟨18762307433229477623780317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25016409910972636831707089 18762307433229477623780317)
                ·
                  refine ⟨7035865287461054108917619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18762307433229477623780317 7035865287461054108917619)
                  ·
                    refine ⟨10553797931191581163376429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7035865287461054108917619 10553797931191581163376429)
                    ·
                      refine ⟨3957674224196842936266161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10553797931191581163376429 3957674224196842936266161)
                      ·
                        rfl

theorem cell23_7707543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_7707543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707543 prefixEnd_7707543 := by exact prefixLift 7707543
  have htrace : WordTrace (prefixWord ++ tailWord_7707543) baseStart_7707543 baseEnd_7707543 := by
    simpa [prefixWord, tailWord_7707543, baseEnd_7707543] using wordTrace_append hprefix tailTrace_7707543
  have hstable : (prefixWord ++ tailWord_7707543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707543).length < 2 ^ (prefixWord ++ tailWord_7707543).sum := by decide
  have hdescent : baseEnd_7707543 < baseStart_7707543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707596 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_7707596 : Nat := 118140960795 + 7707596 * 2 ^ 59
def prefixEnd_7707596 : Nat := 4983230072969 + 3 ^ 40 * 7707596 * 2
def baseEnd_7707596 : Nat := 3957701438671531228903417

theorem tailTrace_7707596 : CollatzResearch.WordTrace tailWord_7707596 prefixEnd_7707596 3957701438671531228903417 := by
  unfold tailWord_7707596
  simp only [CollatzResearch.WordTrace]
  refine ⟨140559560492351759720863321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187412747323135679627817761 140559560492351759720863321)
  ·
    refine ⟨105419670369263819790647491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140559560492351759720863321 105419670369263819790647491)
    ·
      refine ⟨158129505553895729685971237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105419670369263819790647491 158129505553895729685971237)
      ·
        refine ⟨29649282291355449316119607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158129505553895729685971237 29649282291355449316119607)
        ·
          refine ⟨44473923437033173974179411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29649282291355449316119607 44473923437033173974179411)
          ·
            refine ⟨66710885155549760961269117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44473923437033173974179411 66710885155549760961269117)
            ·
              refine ⟨25016581933331160360475919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66710885155549760961269117 25016581933331160360475919)
              ·
                refine ⟨37524872899996740540713879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25016581933331160360475919 37524872899996740540713879)
                ·
                  refine ⟨56287309349995110811070819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37524872899996740540713879 56287309349995110811070819)
                  ·
                    refine ⟨84430964024992666216606229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56287309349995110811070819 84430964024992666216606229)
                    ·
                      refine ⟨3957701438671531228903417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84430964024992666216606229 3957701438671531228903417)
                      ·
                        rfl

theorem cell23_7707596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_7707596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707596 prefixEnd_7707596 := by exact prefixLift 7707596
  have htrace : WordTrace (prefixWord ++ tailWord_7707596) baseStart_7707596 baseEnd_7707596 := by
    simpa [prefixWord, tailWord_7707596, baseEnd_7707596] using wordTrace_append hprefix tailTrace_7707596
  have hstable : (prefixWord ++ tailWord_7707596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707596).length < 2 ^ (prefixWord ++ tailWord_7707596).sum := by decide
  have hdescent : baseEnd_7707596 < baseStart_7707596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707643 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 3, 3, 2]
def baseStart_7707643 : Nat := 118140960795 + 7707643 * 2 ^ 59
def prefixEnd_7707643 : Nat := 4983230072969 + 3 ^ 40 * 7707643 * 2
def baseEnd_7707643 : Nat := 3957725572262292545015701

theorem tailTrace_7707643 : CollatzResearch.WordTrace tailWord_7707643 prefixEnd_7707643 3957725572262292545015701 := by
  unfold tailWord_7707643
  simp only [CollatzResearch.WordTrace]
  refine ⟨281120835215533246468687583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187413890143688830979125055 281120835215533246468687583)
  ·
    refine ⟨421681252823299869703031375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281120835215533246468687583 421681252823299869703031375)
    ·
      refine ⟨632521879234949804554547063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421681252823299869703031375 632521879234949804554547063)
      ·
        refine ⟨948782818852424706831820595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632521879234949804554547063 948782818852424706831820595)
        ·
          refine ⟨1423174228278637060247730893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948782818852424706831820595 1423174228278637060247730893)
          ·
            refine ⟨533690335604488897592899085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1423174228278637060247730893 533690335604488897592899085)
            ·
              refine ⟨200133875851683336597337157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 533690335604488897592899085 200133875851683336597337157)
              ·
                refine ⟨37525101722190625612000717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200133875851683336597337157 37525101722190625612000717)
                ·
                  refine ⟨14071913145821484604500269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37525101722190625612000717 14071913145821484604500269)
                  ·
                    refine ⟨5276967429683056726687601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14071913145821484604500269 5276967429683056726687601)
                    ·
                      refine ⟨3957725572262292545015701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5276967429683056726687601 3957725572262292545015701)
                      ·
                        rfl

theorem cell23_7707643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 3, 2].length) (baseStart_7707643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707643 prefixEnd_7707643 := by exact prefixLift 7707643
  have htrace : WordTrace (prefixWord ++ tailWord_7707643) baseStart_7707643 baseEnd_7707643 := by
    simpa [prefixWord, tailWord_7707643, baseEnd_7707643] using wordTrace_append hprefix tailTrace_7707643
  have hstable : (prefixWord ++ tailWord_7707643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707643).length < 2 ^ (prefixWord ++ tailWord_7707643).sum := by decide
  have hdescent : baseEnd_7707643 < baseStart_7707643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707660 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 3, 3, 2]
def baseStart_7707660 : Nat := 118140960795 + 7707660 * 2 ^ 59
def prefixEnd_7707660 : Nat := 4983230072969 + 3 ^ 40 * 7707660 * 2
def baseEnd_7707660 : Nat := 3957734301433418978503123

theorem tailTrace_7707660 : CollatzResearch.WordTrace tailWord_7707660 prefixEnd_7707660 3957734301433418978503123 := by
  unfold tailWord_7707660
  simp only [CollatzResearch.WordTrace]
  refine ⟨140560727628235829186028217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187414303504314438914704289 140560727628235829186028217)
  ·
    refine ⟨105420545721176871889521163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140560727628235829186028217 105420545721176871889521163)
    ·
      refine ⟨158130818581765307834281745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105420545721176871889521163 158130818581765307834281745)
      ·
        refine ⟨118598113936323980875711309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158130818581765307834281745 118598113936323980875711309)
        ·
          refine ⟨44474292726121492828391741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118598113936323980875711309 44474292726121492828391741)
          ·
            refine ⟨16677859772295559810646903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44474292726121492828391741 16677859772295559810646903)
            ·
              refine ⟨25016789658443339715970355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16677859772295559810646903 25016789658443339715970355)
              ·
                refine ⟨37525184487665009573955533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25016789658443339715970355 37525184487665009573955533)
                ·
                  refine ⟨14071944182874378590233325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37525184487665009573955533 14071944182874378590233325)
                  ·
                    refine ⟨5276979068577891971337497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14071944182874378590233325 5276979068577891971337497)
                    ·
                      refine ⟨3957734301433418978503123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5276979068577891971337497 3957734301433418978503123)
                      ·
                        rfl

theorem cell23_7707660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_7707660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707660 prefixEnd_7707660 := by exact prefixLift 7707660
  have htrace : WordTrace (prefixWord ++ tailWord_7707660) baseStart_7707660 baseEnd_7707660 := by
    simpa [prefixWord, tailWord_7707660, baseEnd_7707660] using wordTrace_append hprefix tailTrace_7707660
  have hstable : (prefixWord ++ tailWord_7707660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707660).length < 2 ^ (prefixWord ++ tailWord_7707660).sum := by decide
  have hdescent : baseEnd_7707660 < baseStart_7707660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707673 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 3, 4, 2]
def baseStart_7707673 : Nat := 118140960795 + 7707673 * 2 ^ 59
def prefixEnd_7707673 : Nat := 4983230072969 + 3 ^ 40 * 7707673 * 2
def baseEnd_7707673 : Nat := 3957740976681927427640563

theorem tailTrace_7707673 : CollatzResearch.WordTrace tailWord_7707673 prefixEnd_7707673 3957740976681927427640563 := by
  unfold tailWord_7707673
  simp only [CollatzResearch.WordTrace]
  refine ⟨281121929405424561592279673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187414619603616374394853115 281121929405424561592279673)
  ·
    refine ⟨210841447054068421194209755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281121929405424561592279673 210841447054068421194209755)
    ·
      refine ⟨316262170581102631791314633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210841447054068421194209755 316262170581102631791314633)
      ·
        refine ⟨237196627935826973843485975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316262170581102631791314633 237196627935826973843485975)
        ·
          refine ⟨355794941903740460765228963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237196627935826973843485975 355794941903740460765228963)
          ·
            refine ⟨533692412855610691147843445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355794941903740460765228963 533692412855610691147843445)
            ·
              refine ⟨50033663705213502295110323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 533692412855610691147843445 50033663705213502295110323)
              ·
                refine ⟨75050495557820253442665485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50033663705213502295110323 75050495557820253442665485)
                ·
                  refine ⟨28143935834182595040999557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75050495557820253442665485 28143935834182595040999557)
                  ·
                    refine ⟨5276987968909236570187417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28143935834182595040999557 5276987968909236570187417)
                    ·
                      refine ⟨3957740976681927427640563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5276987968909236570187417 3957740976681927427640563)
                      ·
                        rfl

theorem cell23_7707673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 4, 2].length) (baseStart_7707673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707673 prefixEnd_7707673 := by exact prefixLift 7707673
  have htrace : WordTrace (prefixWord ++ tailWord_7707673) baseStart_7707673 baseEnd_7707673 := by
    simpa [prefixWord, tailWord_7707673, baseEnd_7707673] using wordTrace_append hprefix tailTrace_7707673
  have hstable : (prefixWord ++ tailWord_7707673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707673).length < 2 ^ (prefixWord ++ tailWord_7707673).sum := by decide
  have hdescent : baseEnd_7707673 < baseStart_7707673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707696 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 7]
def baseStart_7707696 : Nat := 118140960795 + 7707696 * 2 ^ 59
def prefixEnd_7707696 : Nat := 4983230072969 + 3 ^ 40 * 7707696 * 2
def baseEnd_7707696 : Nat := 439750309637442315294773

theorem tailTrace_7707696 : CollatzResearch.WordTrace tailWord_7707696 prefixEnd_7707696 439750309637442315294773 := by
  unfold tailWord_7707696
  simp only [CollatzResearch.WordTrace]
  refine ⟨140561384142170618260183471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187415178856227491013577961 140561384142170618260183471)
  ·
    refine ⟨210842076213255927390275207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140561384142170618260183471 210842076213255927390275207)
    ·
      refine ⟨316263114319883891085412811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210842076213255927390275207 316263114319883891085412811)
      ·
        refine ⟨474394671479825836628119217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316263114319883891085412811 474394671479825836628119217)
        ·
          refine ⟨355796003609869377471089413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474394671479825836628119217 355796003609869377471089413)
          ·
            refine ⟨66711750676850508275829265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355796003609869377471089413 66711750676850508275829265)
            ·
              refine ⟨50033813007637881206871949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66711750676850508275829265 50033813007637881206871949)
              ·
                refine ⟨18762679877864205452576981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50033813007637881206871949 18762679877864205452576981)
                ·
                  refine ⟨439750309637442315294773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18762679877864205452576981 439750309637442315294773)
                  ·
                    rfl

theorem cell23_7707696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 7].length) (baseStart_7707696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707696 prefixEnd_7707696 := by exact prefixLift 7707696
  have htrace : WordTrace (prefixWord ++ tailWord_7707696) baseStart_7707696 baseEnd_7707696 := by
    simpa [prefixWord, tailWord_7707696, baseEnd_7707696] using wordTrace_append hprefix tailTrace_7707696
  have hstable : (prefixWord ++ tailWord_7707696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707696).length < 2 ^ (prefixWord ++ tailWord_7707696).sum := by decide
  have hdescent : baseEnd_7707696 < baseStart_7707696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707700 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_7707700 : Nat := 118140960795 + 7707700 * 2 ^ 59
def prefixEnd_7707700 : Nat := 4983230072969 + 3 ^ 40 * 7707700 * 2
def baseEnd_7707700 : Nat := 1319251613553199607334313

theorem tailTrace_7707700 : CollatzResearch.WordTrace tailWord_7707700 prefixEnd_7707700 1319251613553199607334313 := by
  unfold tailWord_7707700
  simp only [CollatzResearch.WordTrace]
  refine ⟨140561457088163372601756277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187415276117551163469008369 140561457088163372601756277)
  ·
    refine ⟨13177636602015316181414651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140561457088163372601756277 13177636602015316181414651)
    ·
      refine ⟨19766454903022974272121977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13177636602015316181414651 19766454903022974272121977)
      ·
        refine ⟨14824841177267230704091483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19766454903022974272121977 14824841177267230704091483)
        ·
          refine ⟨22237261765900846056137225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14824841177267230704091483 22237261765900846056137225)
          ·
            refine ⟨16677946324425634542102919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22237261765900846056137225 16677946324425634542102919)
            ·
              refine ⟨25016919486638451813154379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16677946324425634542102919 25016919486638451813154379)
              ·
                refine ⟨37525379229957677719731569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25016919486638451813154379 37525379229957677719731569)
                ·
                  refine ⟨28144034422468258289798677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37525379229957677719731569 28144034422468258289798677)
                  ·
                    refine ⟨1319251613553199607334313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28144034422468258289798677 1319251613553199607334313)
                    ·
                      rfl

theorem cell23_7707700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_7707700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707700 prefixEnd_7707700 := by exact prefixLift 7707700
  have htrace : WordTrace (prefixWord ++ tailWord_7707700) baseStart_7707700 baseEnd_7707700 := by
    simpa [prefixWord, tailWord_7707700, baseEnd_7707700] using wordTrace_append hprefix tailTrace_7707700
  have hstable : (prefixWord ++ tailWord_7707700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707700).length < 2 ^ (prefixWord ++ tailWord_7707700).sum := by decide
  have hdescent : baseEnd_7707700 < baseStart_7707700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707730 : List Nat := [3, 2, 2, 1, 3, 1, 1, 5, 5]
def baseStart_7707730 : Nat := 118140960795 + 7707730 * 2 ^ 59
def prefixEnd_7707730 : Nat := 4983230072969 + 3 ^ 40 * 7707730 * 2
def baseEnd_7707730 : Nat := 439752249453248189403089

theorem tailTrace_7707730 : CollatzResearch.WordTrace tailWord_7707730 prefixEnd_7707730 439752249453248189403089 := by
  unfold tailWord_7707730
  simp only [CollatzResearch.WordTrace]
  refine ⟨70281002091554515081776161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187416005577478706884736429 70281002091554515081776161)
  ·
    refine ⟨52710751568665886311332121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70281002091554515081776161 52710751568665886311332121)
    ·
      refine ⟨39533063676499414733499091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52710751568665886311332121 39533063676499414733499091)
      ·
        refine ⟨59299595514749122100248637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39533063676499414733499091 59299595514749122100248637)
        ·
          refine ⟨22237348318030920787593239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59299595514749122100248637 22237348318030920787593239)
          ·
            refine ⟨33356022477046381181389859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22237348318030920787593239 33356022477046381181389859)
            ·
              refine ⟨50034033715569571772084789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33356022477046381181389859 50034033715569571772084789)
              ·
                refine ⟨4690690660834647353632949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50034033715569571772084789 4690690660834647353632949)
                ·
                  refine ⟨439752249453248189403089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4690690660834647353632949 439752249453248189403089)
                  ·
                    rfl

theorem cell23_7707730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_7707730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707730 prefixEnd_7707730 := by exact prefixLift 7707730
  have htrace : WordTrace (prefixWord ++ tailWord_7707730) baseStart_7707730 baseEnd_7707730 := by
    simpa [prefixWord, tailWord_7707730, baseEnd_7707730] using wordTrace_append hprefix tailTrace_7707730
  have hstable : (prefixWord ++ tailWord_7707730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707730).length < 2 ^ (prefixWord ++ tailWord_7707730).sum := by decide
  have hdescent : baseEnd_7707730 < baseStart_7707730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707800 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 4, 2, 3]
def baseStart_7707800 : Nat := 118140960795 + 7707800 * 2 ^ 59
def prefixEnd_7707800 : Nat := 4983230072969 + 3 ^ 40 * 7707800 * 2
def baseEnd_7707800 : Nat := 3957806188725048430752479

theorem tailTrace_7707800 : CollatzResearch.WordTrace tailWord_7707800 prefixEnd_7707800 3957806188725048430752479 := by
  unfold tailWord_7707800
  simp only [CollatzResearch.WordTrace]
  refine ⟨140563280737982231141076427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187417707650642974854768569 140563280737982231141076427)
  ·
    refine ⟨210844921106973346711614641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140563280737982231141076427 210844921106973346711614641)
    ·
      refine ⟨158133690830230010033710981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210844921106973346711614641 158133690830230010033710981)
      ·
        refine ⟨29650067030668126881320809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158133690830230010033710981 29650067030668126881320809)
        ·
          refine ⟨22237550273001095160990607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29650067030668126881320809 22237550273001095160990607)
          ·
            refine ⟨33356325409501642741485911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22237550273001095160990607 33356325409501642741485911)
            ·
              refine ⟨50034488114252464112228867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33356325409501642741485911 50034488114252464112228867)
              ·
                refine ⟨75051732171378696168343301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50034488114252464112228867 75051732171378696168343301)
                ·
                  refine ⟨14072199782133505531564369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75051732171378696168343301 14072199782133505531564369)
                  ·
                    refine ⟨10554149836600129148673277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14072199782133505531564369 10554149836600129148673277)
                    ·
                      refine ⟨3957806188725048430752479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10554149836600129148673277 3957806188725048430752479)
                      ·
                        rfl

theorem cell23_7707800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_7707800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707800 prefixEnd_7707800 := by exact prefixLift 7707800
  have htrace : WordTrace (prefixWord ++ tailWord_7707800) baseStart_7707800 baseEnd_7707800 := by
    simpa [prefixWord, tailWord_7707800, baseEnd_7707800] using wordTrace_append hprefix tailTrace_7707800
  have hstable : (prefixWord ++ tailWord_7707800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707800).length < 2 ^ (prefixWord ++ tailWord_7707800).sum := by decide
  have hdescent : baseEnd_7707800 < baseStart_7707800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707880 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 1, 6]
def baseStart_7707880 : Nat := 118140960795 + 7707880 * 2 ^ 59
def prefixEnd_7707880 : Nat := 4983230072969 + 3 ^ 40 * 7707880 * 2
def baseEnd_7707880 : Nat := 1319282422392469372584037

theorem tailTrace_7707880 : CollatzResearch.WordTrace tailWord_7707880 prefixEnd_7707880 1319282422392469372584037 := by
  unfold tailWord_7707880
  simp only [CollatzResearch.WordTrace]
  refine ⟨140564739657837317972532547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187419652877116423963376729 140564739657837317972532547)
  ·
    refine ⟨210847109486755976958798821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140564739657837317972532547 210847109486755976958798821)
    ·
      refine ⟨39533833028766745679774779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210847109486755976958798821 39533833028766745679774779)
      ·
        refine ⟨59300749543150118519662169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39533833028766745679774779 59300749543150118519662169)
        ·
          refine ⟨44475562157362588889746627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59300749543150118519662169 44475562157362588889746627)
          ·
            refine ⟨66713343236043883334619941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44475562157362588889746627 66713343236043883334619941)
            ·
              refine ⟨12508751856758228125241239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66713343236043883334619941 12508751856758228125241239)
              ·
                refine ⟨18763127785137342187861859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12508751856758228125241239 18763127785137342187861859)
                ·
                  refine ⟨28144691677706013281792789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18763127785137342187861859 28144691677706013281792789)
                  ·
                    refine ⟨1319282422392469372584037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28144691677706013281792789 1319282422392469372584037)
                    ·
                      rfl

theorem cell23_7707880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_7707880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707880 prefixEnd_7707880 := by exact prefixLift 7707880
  have htrace : WordTrace (prefixWord ++ tailWord_7707880) baseStart_7707880 baseEnd_7707880 := by
    simpa [prefixWord, tailWord_7707880, baseEnd_7707880] using wordTrace_append hprefix tailTrace_7707880
  have hstable : (prefixWord ++ tailWord_7707880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707880).length < 2 ^ (prefixWord ++ tailWord_7707880).sum := by decide
  have hdescent : baseEnd_7707880 < baseStart_7707880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707907 : List Nat := [1, 1, 1, 3, 2, 5, 1, 3, 1, 2, 3]
def baseStart_7707907 : Nat := 118140960795 + 7707907 * 2 ^ 59
def prefixEnd_7707907 : Nat := 4983230072969 + 3 ^ 40 * 7707907 * 2
def baseEnd_7707907 : Nat := 3957861131155079512114487

theorem tailTrace_7707907 : CollatzResearch.WordTrace tailWord_7707907 prefixEnd_7707907 3957861131155079512114487 := by
  unfold tailWord_7707907
  simp only [CollatzResearch.WordTrace]
  refine ⟨281130464086576819556297975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187420309391051213037531983 281130464086576819556297975)
  ·
    refine ⟨421695696129865229334446963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281130464086576819556297975 421695696129865229334446963)
    ·
      refine ⟨632543544194797844001670445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421695696129865229334446963 632543544194797844001670445)
      ·
        refine ⟨237203829073049191500626417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 632543544194797844001670445 237203829073049191500626417)
        ·
          refine ⟨177902871804786893625469813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237203829073049191500626417 177902871804786893625469813)
          ·
            refine ⟨16678394231698771277387795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177902871804786893625469813 16678394231698771277387795)
            ·
              refine ⟨25017591347548156916081693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16678394231698771277387795 25017591347548156916081693)
              ·
                refine ⟨9381596755330558843530635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25017591347548156916081693 9381596755330558843530635)
                ·
                  refine ⟨14072395132995838265295953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9381596755330558843530635 14072395132995838265295953)
                  ·
                    refine ⟨10554296349746878698971965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14072395132995838265295953 10554296349746878698971965)
                    ·
                      refine ⟨3957861131155079512114487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10554296349746878698971965 3957861131155079512114487)
                      ·
                        rfl

theorem cell23_7707907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_7707907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707907 prefixEnd_7707907 := by exact prefixLift 7707907
  have htrace : WordTrace (prefixWord ++ tailWord_7707907) baseStart_7707907 baseEnd_7707907 := by
    simpa [prefixWord, tailWord_7707907, baseEnd_7707907] using wordTrace_append hprefix tailTrace_7707907
  have hstable : (prefixWord ++ tailWord_7707907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707907).length < 2 ^ (prefixWord ++ tailWord_7707907).sum := by decide
  have hdescent : baseEnd_7707907 < baseStart_7707907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707934 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_7707934 : Nat := 118140960795 + 7707934 * 2 ^ 59
def prefixEnd_7707934 : Nat := 4983230072969 + 3 ^ 40 * 7707934 * 2
def baseEnd_7707934 : Nat := 3957874995132750906476863

theorem tailTrace_7707934 : CollatzResearch.WordTrace tailWord_7707934 prefixEnd_7707934 3957874995132750906476863 := by
  unfold tailWord_7707934
  simp only [CollatzResearch.WordTrace]
  refine ⟨35141431107184875395941357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187420965904986002111687237 35141431107184875395941357)
  ·
    refine ⟨13178036665194328273478009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35141431107184875395941357 13178036665194328273478009)
    ·
      refine ⟨9883527498895746205108507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13178036665194328273478009 9883527498895746205108507)
      ·
        refine ⟨14825291248343619307662761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9883527498895746205108507 14825291248343619307662761)
        ·
          refine ⟨11118968436257714480747071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14825291248343619307662761 11118968436257714480747071)
          ·
            refine ⟨16678452654386571721120607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11118968436257714480747071 16678452654386571721120607)
            ·
              refine ⟨25017678981579857581680911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16678452654386571721120607 25017678981579857581680911)
              ·
                refine ⟨37526518472369786372521367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25017678981579857581680911 37526518472369786372521367)
                ·
                  refine ⟨56289777708554679558782051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37526518472369786372521367 56289777708554679558782051)
                  ·
                    refine ⟨84434666562832019338173077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56289777708554679558782051 84434666562832019338173077)
                    ·
                      refine ⟨3957874995132750906476863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84434666562832019338173077 3957874995132750906476863)
                      ·
                        rfl

theorem cell23_7707934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_7707934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707934 prefixEnd_7707934 := by exact prefixLift 7707934
  have htrace : WordTrace (prefixWord ++ tailWord_7707934) baseStart_7707934 baseEnd_7707934 := by
    simpa [prefixWord, tailWord_7707934, baseEnd_7707934] using wordTrace_append hprefix tailTrace_7707934
  have hstable : (prefixWord ++ tailWord_7707934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707934).length < 2 ^ (prefixWord ++ tailWord_7707934).sum := by decide
  have hdescent : baseEnd_7707934 < baseStart_7707934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7707964 : List Nat := [2, 2, 2, 2, 1, 3, 2, 3, 1, 3, 2]
def baseStart_7707964 : Nat := 118140960795 + 7707964 * 2 ^ 59
def prefixEnd_7707964 : Nat := 4983230072969 + 3 ^ 40 * 7707964 * 2
def baseEnd_7707964 : Nat := 3957890399552385789101725

theorem tailTrace_7707964 : CollatzResearch.WordTrace tailWord_7707964 prefixEnd_7707964 3957890399552385789101725 := by
  unfold tailWord_7707964
  simp only [CollatzResearch.WordTrace]
  refine ⟨140566271523685159145561473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187421695364913545527415297 140566271523685159145561473)
  ·
    refine ⟨105424703642763869359171105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140566271523685159145561473 105424703642763869359171105)
    ·
      refine ⟨79068527732072902019378329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105424703642763869359171105 79068527732072902019378329)
      ·
        refine ⟨59301395799054676514533747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79068527732072902019378329 59301395799054676514533747)
        ·
          refine ⟨88952093698582014771800621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59301395799054676514533747 88952093698582014771800621)
          ·
            refine ⟨33357035136968255539425233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88952093698582014771800621 33357035136968255539425233)
            ·
              refine ⟨25017776352726191654568925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33357035136968255539425233 25017776352726191654568925)
              ·
                refine ⟨9381666132272321870463347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25017776352726191654568925 9381666132272321870463347)
                ·
                  refine ⟨14072499198408482805695021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9381666132272321870463347 14072499198408482805695021)
                  ·
                    refine ⟨5277187199403181052135633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14072499198408482805695021 5277187199403181052135633)
                    ·
                      refine ⟨3957890399552385789101725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5277187199403181052135633 3957890399552385789101725)
                      ·
                        rfl

theorem cell23_7707964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_7707964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7707964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7707964 prefixEnd_7707964 := by exact prefixLift 7707964
  have htrace : WordTrace (prefixWord ++ tailWord_7707964) baseStart_7707964 baseEnd_7707964 := by
    simpa [prefixWord, tailWord_7707964, baseEnd_7707964] using wordTrace_append hprefix tailTrace_7707964
  have hstable : (prefixWord ++ tailWord_7707964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7707964).length < 2 ^ (prefixWord ++ tailWord_7707964).sum := by decide
  have hdescent : baseEnd_7707964 < baseStart_7707964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7707964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708037 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 2, 5, 2]
def baseStart_7708037 : Nat := 118140960795 + 7708037 * 2 ^ 59
def prefixEnd_7708037 : Nat := 4983230072969 + 3 ^ 40 * 7708037 * 2
def baseEnd_7708037 : Nat := 3957927883640164003488889

theorem tailTrace_7708037 : CollatzResearch.WordTrace tailWord_7708037 prefixEnd_7708037 3957927883640164003488889 := by
  unfold tailWord_7708037
  simp only [CollatzResearch.WordTrace]
  refine ⟨281135205576105851758530365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187423470384070567839020243 281135205576105851758530365)
  ·
    refine ⟨105425702091039694409448887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281135205576105851758530365 105425702091039694409448887)
    ·
      refine ⟨158138553136559541614173331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105425702091039694409448887 158138553136559541614173331)
      ·
        refine ⟨237207829704839312421259997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158138553136559541614173331 237207829704839312421259997)
        ·
          refine ⟨88952936139314742157972499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237207829704839312421259997 88952936139314742157972499)
          ·
            refine ⟨133429404208972113236958749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88952936139314742157972499 133429404208972113236958749)
            ·
              refine ⟨50036026578364542463859531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133429404208972113236958749 50036026578364542463859531)
              ·
                refine ⟨75054039867546813695789297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50036026578364542463859531 75054039867546813695789297)
                ·
                  refine ⟨56290529900660110271841973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75054039867546813695789297 56290529900660110271841973)
                  ·
                    refine ⟨5277237178186885337985185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56290529900660110271841973 5277237178186885337985185)
                    ·
                      refine ⟨3957927883640164003488889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5277237178186885337985185 3957927883640164003488889)
                      ·
                        rfl

theorem cell23_7708037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 5, 2].length) (baseStart_7708037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708037 prefixEnd_7708037 := by exact prefixLift 7708037
  have htrace : WordTrace (prefixWord ++ tailWord_7708037) baseStart_7708037 baseEnd_7708037 := by
    simpa [prefixWord, tailWord_7708037, baseEnd_7708037] using wordTrace_append hprefix tailTrace_7708037
  have hstable : (prefixWord ++ tailWord_7708037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708037).length < 2 ^ (prefixWord ++ tailWord_7708037).sum := by decide
  have hdescent : baseEnd_7708037 < baseStart_7708037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708067 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 1, 6, 2]
def baseStart_7708067 : Nat := 118140960795 + 7708067 * 2 ^ 59
def prefixEnd_7708067 : Nat := 4983230072969 + 3 ^ 40 * 7708067 * 2
def baseEnd_7708067 : Nat := 3957943288059798886113751

theorem tailTrace_7708067 : CollatzResearch.WordTrace tailWord_7708067 prefixEnd_7708067 3957943288059798886113751 := by
  unfold tailWord_7708067
  simp only [CollatzResearch.WordTrace]
  refine ⟨281136299765997166882122455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187424199843998111254748303 281136299765997166882122455)
  ·
    refine ⟨421704449648995750323183683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281136299765997166882122455 421704449648995750323183683)
    ·
      refine ⟨632556674473493625484775525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421704449648995750323183683 632556674473493625484775525)
      ·
        refine ⟨118604376463780054778395411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 632556674473493625484775525 118604376463780054778395411)
        ·
          refine ⟨177906564695670082167593117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118604376463780054778395411 177906564695670082167593117)
          ·
            refine ⟨66714961760876280812847419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177906564695670082167593117 66714961760876280812847419)
            ·
              refine ⟨100072442641314421219271129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66714961760876280812847419 100072442641314421219271129)
              ·
                refine ⟨75054331980985815914453347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100072442641314421219271129 75054331980985815914453347)
                ·
                  refine ⟨112581497971478723871680021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75054331980985815914453347 112581497971478723871680021)
                  ·
                    refine ⟨5277257717413065181485001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112581497971478723871680021 5277257717413065181485001)
                    ·
                      refine ⟨3957943288059798886113751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5277257717413065181485001 3957943288059798886113751)
                      ·
                        rfl

theorem cell23_7708067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_7708067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708067 prefixEnd_7708067 := by exact prefixLift 7708067
  have htrace : WordTrace (prefixWord ++ tailWord_7708067) baseStart_7708067 baseEnd_7708067 := by
    simpa [prefixWord, tailWord_7708067, baseEnd_7708067] using wordTrace_append hprefix tailTrace_7708067
  have hstable : (prefixWord ++ tailWord_7708067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708067).length < 2 ^ (prefixWord ++ tailWord_7708067).sum := by decide
  have hdescent : baseEnd_7708067 < baseStart_7708067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708087 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 3]
def baseStart_7708087 : Nat := 118140960795 + 7708087 * 2 ^ 59
def prefixEnd_7708087 : Nat := 4983230072969 + 3 ^ 40 * 7708087 * 2
def baseEnd_7708087 : Nat := 3957953557672888807863659

theorem tailTrace_7708087 : CollatzResearch.WordTrace tailWord_7708087 prefixEnd_7708087 3957953557672888807863659 := by
  unfold tailWord_7708087
  simp only [CollatzResearch.WordTrace]
  refine ⟨281137029225924710297850515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187424686150616473531900343 281137029225924710297850515)
  ·
    refine ⟨421705543838887065446775773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281137029225924710297850515 421705543838887065446775773)
    ·
      refine ⟨158139578939582649542540915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421705543838887065446775773 158139578939582649542540915)
      ·
        refine ⟨237209368409373974313811373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158139578939582649542540915 237209368409373974313811373)
        ·
          refine ⟨88953513153515240367679265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237209368409373974313811373 88953513153515240367679265)
          ·
            refine ⟨66715134865136430275759449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88953513153515240367679265 66715134865136430275759449)
            ·
              refine ⟨50036351148852322706819587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66715134865136430275759449 50036351148852322706819587)
              ·
                refine ⟨75054526723278484060229381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50036351148852322706819587 75054526723278484060229381)
                ·
                  refine ⟨14072723760614715761293009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75054526723278484060229381 14072723760614715761293009)
                  ·
                    refine ⟨10554542820461036820969757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14072723760614715761293009 10554542820461036820969757)
                    ·
                      refine ⟨3957953557672888807863659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10554542820461036820969757 3957953557672888807863659)
                      ·
                        rfl

theorem cell23_7708087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_7708087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708087 prefixEnd_7708087 := by exact prefixLift 7708087
  have htrace : WordTrace (prefixWord ++ tailWord_7708087) baseStart_7708087 baseEnd_7708087 := by
    simpa [prefixWord, tailWord_7708087, baseEnd_7708087] using wordTrace_append hprefix tailTrace_7708087
  have hstable : (prefixWord ++ tailWord_7708087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708087).length < 2 ^ (prefixWord ++ tailWord_7708087).sum := by decide
  have hdescent : baseEnd_7708087 < baseStart_7708087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708117 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_7708117 : Nat := 118140960795 + 7708117 * 2 ^ 59
def prefixEnd_7708117 : Nat := 4983230072969 + 3 ^ 40 * 7708117 * 2
def baseEnd_7708117 : Nat := 3957968962092523690488521

theorem tailTrace_7708117 : CollatzResearch.WordTrace tailWord_7708117 prefixEnd_7708117 3957968962092523690488521 := by
  unfold tailWord_7708117
  simp only [CollatzResearch.WordTrace]
  refine ⟨281138123415816025421442605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187425415610544016947628403 281138123415816025421442605)
  ·
    refine ⟨105426796280931009533040977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281138123415816025421442605 105426796280931009533040977)
    ·
      refine ⟨79070097210698257149780733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105426796280931009533040977 79070097210698257149780733)
      ·
        refine ⟨29651286454011846431167775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79070097210698257149780733 29651286454011846431167775)
        ·
          refine ⟨44476929681017769646751663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29651286454011846431167775 44476929681017769646751663)
          ·
            refine ⟨66715394521526654470127495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44476929681017769646751663 66715394521526654470127495)
            ·
              refine ⟨100073091782289981705191243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66715394521526654470127495 100073091782289981705191243)
              ·
                refine ⟨150109637673434972557786865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100073091782289981705191243 150109637673434972557786865)
                ·
                  refine ⟨112582228255076229418340149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150109637673434972557786865 112582228255076229418340149)
                  ·
                    refine ⟨10554583898913396507969389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112582228255076229418340149 10554583898913396507969389)
                    ·
                      refine ⟨3957968962092523690488521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10554583898913396507969389 3957968962092523690488521)
                      ·
                        rfl

theorem cell23_7708117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_7708117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708117 prefixEnd_7708117 := by exact prefixLift 7708117
  have htrace : WordTrace (prefixWord ++ tailWord_7708117) baseStart_7708117 baseEnd_7708117 := by
    simpa [prefixWord, tailWord_7708117, baseEnd_7708117] using wordTrace_append hprefix tailTrace_7708117
  have hstable : (prefixWord ++ tailWord_7708117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708117).length < 2 ^ (prefixWord ++ tailWord_7708117).sum := by decide
  have hdescent : baseEnd_7708117 < baseStart_7708117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708144 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 4, 3, 2]
def baseStart_7708144 : Nat := 118140960795 + 7708144 * 2 ^ 59
def prefixEnd_7708144 : Nat := 4983230072969 + 3 ^ 40 * 7708144 * 2
def baseEnd_7708144 : Nat := 3957982826070195084850897

theorem tailTrace_7708144 : CollatzResearch.WordTrace tailWord_7708144 prefixEnd_7708144 3957982826070195084850897 := by
  unfold tailWord_7708144
  simp only [CollatzResearch.WordTrace]
  refine ⟨140569554093359104516337743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187426072124478806021783657 140569554093359104516337743)
  ·
    refine ⟨210854331140038656774506615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140569554093359104516337743 210854331140038656774506615)
    ·
      refine ⟨316281496710057985161759923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210854331140038656774506615 316281496710057985161759923)
      ·
        refine ⟨474422245065086977742639885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316281496710057985161759923 474422245065086977742639885)
        ·
          refine ⟨177908341899407616653489957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474422245065086977742639885 177908341899407616653489957)
          ·
            refine ⟨33357814106138928122529367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177908341899407616653489957 33357814106138928122529367)
            ·
              refine ⟨50036721159208392183794051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33357814106138928122529367 50036721159208392183794051)
              ·
                refine ⟨75055081738812588275691077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50036721159208392183794051 75055081738812588275691077)
                ·
                  refine ⟨14072827826027360301692077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75055081738812588275691077 14072827826027360301692077)
                  ·
                    refine ⟨5277310434760260113134529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14072827826027360301692077 5277310434760260113134529)
                    ·
                      refine ⟨3957982826070195084850897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5277310434760260113134529 3957982826070195084850897)
                      ·
                        rfl

theorem cell23_7708144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4, 3, 2].length) (baseStart_7708144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708144 prefixEnd_7708144 := by exact prefixLift 7708144
  have htrace : WordTrace (prefixWord ++ tailWord_7708144) baseStart_7708144 baseEnd_7708144 := by
    simpa [prefixWord, tailWord_7708144, baseEnd_7708144] using wordTrace_append hprefix tailTrace_7708144
  have hstable : (prefixWord ++ tailWord_7708144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708144).length < 2 ^ (prefixWord ++ tailWord_7708144).sum := by decide
  have hdescent : baseEnd_7708144 < baseStart_7708144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708171 : List Nat := [1, 1, 1, 1, 8, 2, 1, 2, 1, 5]
def baseStart_7708171 : Nat := 118140960795 + 7708171 * 2 ^ 59
def prefixEnd_7708171 : Nat := 4983230072969 + 3 ^ 40 * 7708171 * 2
def baseEnd_7708171 : Nat := 1319332230015955493071091

theorem tailTrace_7708171 : CollatzResearch.WordTrace tailWord_7708171 prefixEnd_7708171 1319332230015955493071091 := by
  unfold tailWord_7708171
  simp only [CollatzResearch.WordTrace]
  refine ⟨281140092957620392643908367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187426728638413595095938911 281140092957620392643908367)
  ·
    refine ⟨421710139436430588965862551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281140092957620392643908367 421710139436430588965862551)
    ·
      refine ⟨632565209154645883448793827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421710139436430588965862551 632565209154645883448793827)
      ·
        refine ⟨948847813731968825173190741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632565209154645883448793827 948847813731968825173190741)
        ·
          refine ⟨11119310317171509669998329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 948847813731968825173190741 11119310317171509669998329)
          ·
            refine ⟨8339482737878632252498747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11119310317171509669998329 8339482737878632252498747)
            ·
              refine ⟨12509224106817948378748121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8339482737878632252498747 12509224106817948378748121)
              ·
                refine ⟨9381918080113461284061091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12509224106817948378748121 9381918080113461284061091)
                ·
                  refine ⟨14072877120170191926091637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9381918080113461284061091 14072877120170191926091637)
                  ·
                    refine ⟨1319332230015955493071091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14072877120170191926091637 1319332230015955493071091)
                    ·
                      rfl

theorem cell23_7708171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 5].length) (baseStart_7708171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708171 prefixEnd_7708171 := by exact prefixLift 7708171
  have htrace : WordTrace (prefixWord ++ tailWord_7708171) baseStart_7708171 baseEnd_7708171 := by
    simpa [prefixWord, tailWord_7708171, baseEnd_7708171] using wordTrace_append hprefix tailTrace_7708171
  have hstable : (prefixWord ++ tailWord_7708171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708171).length < 2 ^ (prefixWord ++ tailWord_7708171).sum := by decide
  have hdescent : baseEnd_7708171 < baseStart_7708171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708184 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 1, 6]
def baseStart_7708184 : Nat := 118140960795 + 7708184 * 2 ^ 59
def prefixEnd_7708184 : Nat := 4983230072969 + 3 ^ 40 * 7708184 * 2
def baseEnd_7708184 : Nat := 1319334455098791642783571

theorem tailTrace_7708184 : CollatzResearch.WordTrace tailWord_7708184 prefixEnd_7708184 1319334455098791642783571 := by
  unfold tailWord_7708184
  simp only [CollatzResearch.WordTrace]
  refine ⟨140570283553286647932065803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187427044737715530576087737 140570283553286647932065803)
  ·
    refine ⟨210855425329929971898098705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140570283553286647932065803 210855425329929971898098705)
    ·
      refine ⟨158141568997447478923574029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210855425329929971898098705 158141568997447478923574029)
      ·
        refine ⟨59303088374042804596340261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158141568997447478923574029 59303088374042804596340261)
        ·
          refine ⟨11119329070133025861813799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59303088374042804596340261 11119329070133025861813799)
          ·
            refine ⟨16678993605199538792720699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11119329070133025861813799 16678993605199538792720699)
            ·
              refine ⟨25018490407799308189081049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16678993605199538792720699 25018490407799308189081049)
              ·
                refine ⟨18763867805849481141810787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25018490407799308189081049 18763867805849481141810787)
                ·
                  refine ⟨28145801708774221712716181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18763867805849481141810787 28145801708774221712716181)
                  ·
                    refine ⟨1319334455098791642783571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28145801708774221712716181 1319334455098791642783571)
                    ·
                      rfl

theorem cell23_7708184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_7708184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708184 prefixEnd_7708184 := by exact prefixLift 7708184
  have htrace : WordTrace (prefixWord ++ tailWord_7708184) baseStart_7708184 baseEnd_7708184 := by
    simpa [prefixWord, tailWord_7708184, baseEnd_7708184] using wordTrace_append hprefix tailTrace_7708184
  have hstable : (prefixWord ++ tailWord_7708184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708184).length < 2 ^ (prefixWord ++ tailWord_7708184).sum := by decide
  have hdescent : baseEnd_7708184 < baseStart_7708184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708194 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_7708194 : Nat := 118140960795 + 7708194 * 2 ^ 59
def prefixEnd_7708194 : Nat := 4983230072969 + 3 ^ 40 * 7708194 * 2
def baseEnd_7708194 : Nat := 3958008500102919889225667

theorem tailTrace_7708194 : CollatzResearch.WordTrace tailWord_7708194 prefixEnd_7708194 3958008500102919889225667 := by
  unfold tailWord_7708194
  simp only [CollatzResearch.WordTrace]
  refine ⟨70285232959134266892998909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187427287891024711714663757 70285232959134266892998909)
  ·
    refine ⟨26356962359675350084874591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70285232959134266892998909 26356962359675350084874591)
    ·
      refine ⟨39535443539513025127311887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26356962359675350084874591 39535443539513025127311887)
      ·
        refine ⟨59303165309269537690967831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39535443539513025127311887 59303165309269537690967831)
        ·
          refine ⟨88954747963904306536451747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59303165309269537690967831 88954747963904306536451747)
          ·
            refine ⟨133432121945856459804677621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88954747963904306536451747 133432121945856459804677621)
            ·
              refine ⟨12509261432424043106688527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133432121945856459804677621 12509261432424043106688527)
              ·
                refine ⟨18763892148636064660032791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12509261432424043106688527 18763892148636064660032791)
                ·
                  refine ⟨28145838222954096990049187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18763892148636064660032791 28145838222954096990049187)
                  ·
                    refine ⟨42218757334431145485073781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28145838222954096990049187 42218757334431145485073781)
                    ·
                      refine ⟨3958008500102919889225667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42218757334431145485073781 3958008500102919889225667)
                      ·
                        rfl

theorem cell23_7708194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_7708194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708194 prefixEnd_7708194 := by exact prefixLift 7708194
  have htrace : WordTrace (prefixWord ++ tailWord_7708194) baseStart_7708194 baseEnd_7708194 := by
    simpa [prefixWord, tailWord_7708194, baseEnd_7708194] using wordTrace_append hprefix tailTrace_7708194
  have hstable : (prefixWord ++ tailWord_7708194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708194).length < 2 ^ (prefixWord ++ tailWord_7708194).sum := by decide
  have hdescent : baseEnd_7708194 < baseStart_7708194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708221 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_7708221 : Nat := 118140960795 + 7708221 * 2 ^ 59
def prefixEnd_7708221 : Nat := 4983230072969 + 3 ^ 40 * 7708221 * 2
def baseEnd_7708221 : Nat := 3958022364080591283588043

theorem tailTrace_7708221 : CollatzResearch.WordTrace tailWord_7708221 prefixEnd_7708221 3958022364080591283588043 := by
  unfold tailWord_7708221
  simp only [CollatzResearch.WordTrace]
  refine ⟨281141916607439251183228517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187427944404959500788819011 281141916607439251183228517)
  ·
    refine ⟨52714109363894859596855347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281141916607439251183228517 52714109363894859596855347)
    ·
      refine ⟨79071164045842289395283021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52714109363894859596855347 79071164045842289395283021)
      ·
        refine ⟨29651686517190858523231133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79071164045842289395283021 29651686517190858523231133)
        ·
          refine ⟨11119382443946571946211675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29651686517190858523231133 11119382443946571946211675)
          ·
            refine ⟨16679073665919857919317513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11119382443946571946211675 16679073665919857919317513)
            ·
              refine ⟨12509305249439893439488135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16679073665919857919317513 12509305249439893439488135)
              ·
                refine ⟨18763957874159840159232203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12509305249439893439488135 18763957874159840159232203)
                ·
                  refine ⟨28145936811239760238848305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18763957874159840159232203 28145936811239760238848305)
                  ·
                    refine ⟨21109452608429820179136229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28145936811239760238848305 21109452608429820179136229)
                    ·
                      refine ⟨3958022364080591283588043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21109452608429820179136229 3958022364080591283588043)
                      ·
                        rfl

theorem cell23_7708221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_7708221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708221 prefixEnd_7708221 := by exact prefixLift 7708221
  have htrace : WordTrace (prefixWord ++ tailWord_7708221) baseStart_7708221 baseEnd_7708221 := by
    simpa [prefixWord, tailWord_7708221, baseEnd_7708221] using wordTrace_append hprefix tailTrace_7708221
  have hstable : (prefixWord ++ tailWord_7708221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708221).length < 2 ^ (prefixWord ++ tailWord_7708221).sum := by decide
  have hdescent : baseEnd_7708221 < baseStart_7708221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708224 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 6, 1, 3]
def baseStart_7708224 : Nat := 118140960795 + 7708224 * 2 ^ 59
def prefixEnd_7708224 : Nat := 4983230072969 + 3 ^ 40 * 7708224 * 2
def baseEnd_7708224 : Nat := 3958023904522554771850529

theorem tailTrace_7708224 : CollatzResearch.WordTrace tailWord_7708224 prefixEnd_7708224 3958023904522554771850529 := by
  unfold tailWord_7708224
  simp only [CollatzResearch.WordTrace]
  refine ⟨140571013013214191347793863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187428017350952255130391817 140571013013214191347793863)
  ·
    refine ⟨210856519519821287021690795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140571013013214191347793863 210856519519821287021690795)
    ·
      refine ⟨316284779279731930532536193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210856519519821287021690795 316284779279731930532536193)
      ·
        refine ⟨237213584459798947899402145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316284779279731930532536193 237213584459798947899402145)
        ·
          refine ⟨177910188344849210924551609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237213584459798947899402145 177910188344849210924551609)
          ·
            refine ⟨133432641258636908193413707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177910188344849210924551609 133432641258636908193413707)
            ·
              refine ⟨200148961887955362290120561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133432641258636908193413707 200148961887955362290120561)
              ·
                refine ⟨150111721415966521717590421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200148961887955362290120561 150111721415966521717590421)
                ·
                  refine ⟨7036486941373430705512051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150111721415966521717590421 7036486941373430705512051)
                  ·
                    refine ⟨10554730412060146058268077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7036486941373430705512051 10554730412060146058268077)
                    ·
                      refine ⟨3958023904522554771850529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10554730412060146058268077 3958023904522554771850529)
                      ·
                        rfl

theorem cell23_7708224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_7708224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708224 prefixEnd_7708224 := by exact prefixLift 7708224
  have htrace : WordTrace (prefixWord ++ tailWord_7708224) baseStart_7708224 baseEnd_7708224 := by
    simpa [prefixWord, tailWord_7708224, baseEnd_7708224] using wordTrace_append hprefix tailTrace_7708224
  have hstable : (prefixWord ++ tailWord_7708224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708224).length < 2 ^ (prefixWord ++ tailWord_7708224).sum := by decide
  have hdescent : baseEnd_7708224 < baseStart_7708224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708257 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 4, 6]
def baseStart_7708257 : Nat := 118140960795 + 7708257 * 2 ^ 59
def prefixEnd_7708257 : Nat := 4983230072969 + 3 ^ 40 * 7708257 * 2
def baseEnd_7708257 : Nat := 1319346949794717714245959

theorem tailTrace_7708257 : CollatzResearch.WordTrace tailWord_7708257 prefixEnd_7708257 1319346949794717714245959 := by
  unfold tailWord_7708257
  simp only [CollatzResearch.WordTrace]
  refine ⟨281143229635308829331539025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187428819756872552887692683 281143229635308829331539025)
  ·
    refine ⟨210857422226481621998654269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281143229635308829331539025 210857422226481621998654269)
    ·
      refine ⟨79071533334930608249495351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210857422226481621998654269 79071533334930608249495351)
      ·
        refine ⟨118607300002395912374243027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79071533334930608249495351 118607300002395912374243027)
        ·
          refine ⟨177910950003593868561364541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118607300002395912374243027 177910950003593868561364541)
          ·
            refine ⟨66716606251347700710511703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177910950003593868561364541 66716606251347700710511703)
            ·
              refine ⟨100074909377021551065767555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66716606251347700710511703 100074909377021551065767555)
              ·
                refine ⟨150112364065532326598651333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100074909377021551065767555 150112364065532326598651333)
                ·
                  refine ⟨28146068262287311237247125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150112364065532326598651333 28146068262287311237247125)
                  ·
                    refine ⟨1319346949794717714245959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28146068262287311237247125 1319346949794717714245959)
                    ·
                      rfl

theorem cell23_7708257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_7708257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708257 prefixEnd_7708257 := by exact prefixLift 7708257
  have htrace : WordTrace (prefixWord ++ tailWord_7708257) baseStart_7708257 baseEnd_7708257 := by
    simpa [prefixWord, tailWord_7708257, baseEnd_7708257] using wordTrace_append hprefix tailTrace_7708257
  have hstable : (prefixWord ++ tailWord_7708257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708257).length < 2 ^ (prefixWord ++ tailWord_7708257).sum := by decide
  have hdescent : baseEnd_7708257 < baseStart_7708257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708274 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_7708274 : Nat := 118140960795 + 7708274 * 2 ^ 59
def prefixEnd_7708274 : Nat := 4983230072969 + 3 ^ 40 * 7708274 * 2
def baseEnd_7708274 : Nat := 1319349859518426525408433

theorem tailTrace_7708274 : CollatzResearch.WordTrace tailWord_7708274 prefixEnd_7708274 1319349859518426525408433 := by
  unfold tailWord_7708274
  simp only [CollatzResearch.WordTrace]
  refine ⟨70285962419061810308726969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187429233117498160823271917 70285962419061810308726969)
  ·
    refine ⟨52714471814296357731545227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70285962419061810308726969 52714471814296357731545227)
    ·
      refine ⟨79071707721444536597317841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52714471814296357731545227 79071707721444536597317841)
      ·
        refine ⟨59303780791083402447988381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79071707721444536597317841 59303780791083402447988381)
        ·
          refine ⟨22238917796656275917995643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59303780791083402447988381 22238917796656275917995643)
          ·
            refine ⟨33358376694984413876993465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22238917796656275917995643 33358376694984413876993465)
            ·
              refine ⟨25018782521238310407745099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33358376694984413876993465 25018782521238310407745099)
              ·
                refine ⟨37528173781857465611617649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25018782521238310407745099 37528173781857465611617649)
                ·
                  refine ⟨28146130336393099208713237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37528173781857465611617649 28146130336393099208713237)
                  ·
                    refine ⟨1319349859518426525408433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28146130336393099208713237 1319349859518426525408433)
                    ·
                      rfl

theorem cell23_7708274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_7708274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708274 prefixEnd_7708274 := by exact prefixLift 7708274
  have htrace : WordTrace (prefixWord ++ tailWord_7708274) baseStart_7708274 baseEnd_7708274 := by
    simpa [prefixWord, tailWord_7708274, baseEnd_7708274] using wordTrace_append hprefix tailTrace_7708274
  have hstable : (prefixWord ++ tailWord_7708274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708274).length < 2 ^ (prefixWord ++ tailWord_7708274).sum := by decide
  have hdescent : baseEnd_7708274 < baseStart_7708274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708298 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 4, 2, 2]
def baseStart_7708298 : Nat := 118140960795 + 7708298 * 2 ^ 59
def prefixEnd_7708298 : Nat := 4983230072969 + 3 ^ 40 * 7708298 * 2
def baseEnd_7708298 : Nat := 3958061902090987482325189

theorem tailTrace_7708298 : CollatzResearch.WordTrace tailWord_7708298 prefixEnd_7708298 3958061902090987482325189 := by
  unfold tailWord_7708298
  simp only [CollatzResearch.WordTrace]
  refine ⟨70286181257040073333445387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187429816685440195555854365 70286181257040073333445387)
  ·
    refine ⟨105429271885560110000168081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70286181257040073333445387 105429271885560110000168081)
    ·
      refine ⟨79071953914170082500126061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105429271885560110000168081 79071953914170082500126061)
      ·
        refine ⟨29651982717813780937547273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79071953914170082500126061 29651982717813780937547273)
        ·
          refine ⟨22238987038360335703160455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29651982717813780937547273 22238987038360335703160455)
          ·
            refine ⟨33358480557540503554740683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22238987038360335703160455 33358480557540503554740683)
            ·
              refine ⟨50037720836310755332111025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33358480557540503554740683 50037720836310755332111025)
              ·
                refine ⟨37528290627233066499083269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50037720836310755332111025 37528290627233066499083269)
                ·
                  refine ⟨7036554492606199968578113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37528290627233066499083269 7036554492606199968578113)
                  ·
                    refine ⟨5277415869454649976433585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7036554492606199968578113 5277415869454649976433585)
                    ·
                      refine ⟨3958061902090987482325189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5277415869454649976433585 3958061902090987482325189)
                      ·
                        rfl

theorem cell23_7708298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_7708298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708298 prefixEnd_7708298 := by exact prefixLift 7708298
  have htrace : WordTrace (prefixWord ++ tailWord_7708298) baseStart_7708298 baseEnd_7708298 := by
    simpa [prefixWord, tailWord_7708298, baseEnd_7708298] using wordTrace_append hprefix tailTrace_7708298
  have hstable : (prefixWord ++ tailWord_7708298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708298).length < 2 ^ (prefixWord ++ tailWord_7708298).sum := by decide
  have hdescent : baseEnd_7708298 < baseStart_7708298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708321 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 7]
def baseStart_7708321 : Nat := 118140960795 + 7708321 * 2 ^ 59
def prefixEnd_7708321 : Nat := 4983230072969 + 3 ^ 40 * 7708321 * 2
def baseEnd_7708321 : Nat := 439785968016226765815287

theorem tailTrace_7708321 : CollatzResearch.WordTrace tailWord_7708321 prefixEnd_7708321 439785968016226765815287 := by
  unfold tailWord_7708321
  simp only [CollatzResearch.WordTrace]
  refine ⟨281145563907076968261868817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187430375938051312174579211 281145563907076968261868817)
  ·
    refine ⟨210859172930307726196401613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281145563907076968261868817 210859172930307726196401613)
    ·
      refine ⟨79072189848865397323650605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210859172930307726196401613 79072189848865397323650605)
      ·
        refine ⟨29652071193324523996368977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79072189848865397323650605 29652071193324523996368977)
        ·
          refine ⟨22239053394993392997276733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29652071193324523996368977 22239053394993392997276733)
          ·
            refine ⟨8339645023122522373978775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22239053394993392997276733 8339645023122522373978775)
            ·
              refine ⟨12509467534683783560968163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8339645023122522373978775 12509467534683783560968163)
              ·
                refine ⟨18764201302025675341452245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12509467534683783560968163 18764201302025675341452245)
                ·
                  refine ⟨439785968016226765815287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18764201302025675341452245 439785968016226765815287)
                  ·
                    rfl

theorem cell23_7708321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 7].length) (baseStart_7708321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708321 prefixEnd_7708321 := by exact prefixLift 7708321
  have htrace : WordTrace (prefixWord ++ tailWord_7708321) baseStart_7708321 baseEnd_7708321 := by
    simpa [prefixWord, tailWord_7708321, baseEnd_7708321] using wordTrace_append hprefix tailTrace_7708321
  have hstable : (prefixWord ++ tailWord_7708321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708321).length < 2 ^ (prefixWord ++ tailWord_7708321).sum := by decide
  have hdescent : baseEnd_7708321 < baseStart_7708321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708347 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 2, 8]
def baseStart_7708347 : Nat := 118140960795 + 7708347 * 2 ^ 59
def prefixEnd_7708347 : Nat := 4983230072969 + 3 ^ 40 * 7708347 * 2
def baseEnd_7708347 : Nat := 1319362354214352596870821

theorem tailTrace_7708347 : CollatzResearch.WordTrace tailWord_7708347 prefixEnd_7708347 1319362354214352596870821 := by
  unfold tailWord_7708347
  simp only [CollatzResearch.WordTrace]
  refine ⟨281146512204982774702315295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187431008136655183134876863 281146512204982774702315295)
  ·
    refine ⟨421719768307474162053472943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281146512204982774702315295 421719768307474162053472943)
    ·
      refine ⟨632579652461211243080209415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421719768307474162053472943 632579652461211243080209415)
      ·
        refine ⟨948869478691816864620314123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632579652461211243080209415 948869478691816864620314123)
        ·
          refine ⟨1423304218037725296930471185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948869478691816864620314123 1423304218037725296930471185)
          ·
            refine ⟨1067478163528293972697853389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423304218037725296930471185 1067478163528293972697853389)
            ·
              refine ⟨400304311323110239761695021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1067478163528293972697853389 400304311323110239761695021)
              ·
                refine ⟨150114116746166339910635633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400304311323110239761695021 150114116746166339910635633)
                ·
                  refine ⟨112585587559624754932976725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150114116746166339910635633 112585587559624754932976725)
                  ·
                    refine ⟨1319362354214352596870821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112585587559624754932976725 1319362354214352596870821)
                    ·
                      rfl

theorem cell23_7708347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 8].length) (baseStart_7708347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708347 prefixEnd_7708347 := by exact prefixLift 7708347
  have htrace : WordTrace (prefixWord ++ tailWord_7708347) baseStart_7708347 baseEnd_7708347 := by
    simpa [prefixWord, tailWord_7708347, baseEnd_7708347] using wordTrace_append hprefix tailTrace_7708347
  have hstable : (prefixWord ++ tailWord_7708347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708347).length < 2 ^ (prefixWord ++ tailWord_7708347).sum := by decide
  have hdescent : baseEnd_7708347 < baseStart_7708347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708472 : List Nat := [2, 1, 2, 1, 3, 5, 1, 3, 1, 1, 3]
def baseStart_7708472 : Nat := 118140960795 + 7708472 * 2 ^ 59
def prefixEnd_7708472 : Nat := 4983230072969 + 3 ^ 40 * 7708472 * 2
def baseEnd_7708472 : Nat := 3958151247724869801549389

theorem tailTrace_7708472 : CollatzResearch.WordTrace tailWord_7708472 prefixEnd_7708472 3958151247724869801549389 := by
  unfold tailWord_7708472
  simp only [CollatzResearch.WordTrace]
  refine ⟨140575535664764960525307835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187434047553019947367077113 140575535664764960525307835)
  ·
    refine ⟨210863303497147440787961753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140575535664764960525307835 210863303497147440787961753)
    ·
      refine ⟨158147477622860580590971315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210863303497147440787961753 158147477622860580590971315)
      ·
        refine ⟨237221216434290870886456973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158147477622860580590971315 237221216434290870886456973)
        ·
          refine ⟨88957956162859076582421365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237221216434290870886456973 88957956162859076582421365)
          ·
            refine ⟨8339808390268038429602003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88957956162859076582421365 8339808390268038429602003)
            ·
              refine ⟨12509712585402057644403005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8339808390268038429602003 12509712585402057644403005)
              ·
                refine ⟨4691142219525771616651127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12509712585402057644403005 4691142219525771616651127)
                ·
                  refine ⟨7036713329288657424976691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4691142219525771616651127 7036713329288657424976691)
                  ·
                    refine ⟨10555069993932986137465037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7036713329288657424976691 10555069993932986137465037)
                    ·
                      refine ⟨3958151247724869801549389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10555069993932986137465037 3958151247724869801549389)
                      ·
                        rfl

theorem cell23_7708472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 1, 1, 3].length) (baseStart_7708472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708472 prefixEnd_7708472 := by exact prefixLift 7708472
  have htrace : WordTrace (prefixWord ++ tailWord_7708472) baseStart_7708472 baseEnd_7708472 := by
    simpa [prefixWord, tailWord_7708472, baseEnd_7708472] using wordTrace_append hprefix tailTrace_7708472
  have hstable : (prefixWord ++ tailWord_7708472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708472).length < 2 ^ (prefixWord ++ tailWord_7708472).sum := by decide
  have hdescent : baseEnd_7708472 < baseStart_7708472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708501 : List Nat := [1, 3, 2, 2, 2, 3, 2, 8]
def baseStart_7708501 : Nat := 118140960795 + 7708501 * 2 ^ 59
def prefixEnd_7708501 : Nat := 4983230072969 + 3 ^ 40 * 7708501 * 2
def baseEnd_7708501 : Nat := 146598745876438895855065

theorem tailTrace_7708501 : CollatzResearch.WordTrace tailWord_7708501 prefixEnd_7708501 146598745876438895855065 := by
  unfold tailWord_7708501
  simp only [CollatzResearch.WordTrace]
  refine ⟨281152129046424859003421357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187434752697616572668947571 281152129046424859003421357)
  ·
    refine ⟨105432048392409322126283009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281152129046424859003421357 105432048392409322126283009)
    ·
      refine ⟨79074036294306991594712257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105432048392409322126283009 79074036294306991594712257)
      ·
        refine ⟨59305527220730243696034193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79074036294306991594712257 59305527220730243696034193)
        ·
          refine ⟨44479145415547682772025645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59305527220730243696034193 44479145415547682772025645)
          ·
            refine ⟨16679679530830381039509617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44479145415547682772025645 16679679530830381039509617)
            ·
              refine ⟨12509759648122785779632213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16679679530830381039509617 12509759648122785779632213)
              ·
                refine ⟨146598745876438895855065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12509759648122785779632213 146598745876438895855065)
                ·
                  rfl

theorem cell23_7708501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 8].length) (baseStart_7708501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708501 prefixEnd_7708501 := by exact prefixLift 7708501
  have htrace : WordTrace (prefixWord ++ tailWord_7708501) baseStart_7708501 baseEnd_7708501 := by
    simpa [prefixWord, tailWord_7708501, baseEnd_7708501] using wordTrace_append hprefix tailTrace_7708501
  have hstable : (prefixWord ++ tailWord_7708501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708501).length < 2 ^ (prefixWord ++ tailWord_7708501).sum := by decide
  have hdescent : baseEnd_7708501 < baseStart_7708501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708562 : List Nat := [3, 2, 3, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_7708562 : Nat := 118140960795 + 7708562 * 2 ^ 59
def prefixEnd_7708562 : Nat := 4983230072969 + 3 ^ 40 * 7708562 * 2
def baseEnd_7708562 : Nat := 3958197460983774449423975

theorem tailTrace_7708562 : CollatzResearch.WordTrace tailWord_7708562 prefixEnd_7708562 3958197460983774449423975 := by
  unfold tailWord_7708562
  simp only [CollatzResearch.WordTrace]
  refine ⟨70288588474800966605347985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187436235932802577614261293 70288588474800966605347985)
  ·
    refine ⟨52716441356100724954010989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70288588474800966605347985 52716441356100724954010989)
    ·
      refine ⟨19768665508537771857754121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52716441356100724954010989 19768665508537771857754121)
      ·
        refine ⟨14826499131403328893315591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19768665508537771857754121 14826499131403328893315591)
        ·
          refine ⟨22239748697104993339973387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14826499131403328893315591 22239748697104993339973387)
          ·
            refine ⟨33359623045657490009960081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22239748697104993339973387 33359623045657490009960081)
            ·
              refine ⟨25019717284243117507470061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33359623045657490009960081 25019717284243117507470061)
              ·
                refine ⟨9382393981591169065301273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25019717284243117507470061 9382393981591169065301273)
                ·
                  refine ⟨7036795486193376798975955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9382393981591169065301273 7036795486193376798975955)
                  ·
                    refine ⟨10555193229290065198463933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7036795486193376798975955 10555193229290065198463933)
                    ·
                      refine ⟨3958197460983774449423975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10555193229290065198463933 3958197460983774449423975)
                      ·
                        rfl

theorem cell23_7708562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_7708562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708562 prefixEnd_7708562 := by exact prefixLift 7708562
  have htrace : WordTrace (prefixWord ++ tailWord_7708562) baseStart_7708562 baseEnd_7708562 := by
    simpa [prefixWord, tailWord_7708562, baseEnd_7708562] using wordTrace_append hprefix tailTrace_7708562
  have hstable : (prefixWord ++ tailWord_7708562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708562).length < 2 ^ (prefixWord ++ tailWord_7708562).sum := by decide
  have hdescent : baseEnd_7708562 < baseStart_7708562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708596 : List Nat := [2, 5, 2, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_7708596 : Nat := 118140960795 + 7708596 * 2 ^ 59
def prefixEnd_7708596 : Nat := 4983230072969 + 3 ^ 40 * 7708596 * 2
def baseEnd_7708596 : Nat := 3958214919326027316398819

theorem tailTrace_7708596 : CollatzResearch.WordTrace tailWord_7708596 prefixEnd_7708596 3958214919326027316398819 := by
  unfold tailWord_7708596
  simp only [CollatzResearch.WordTrace]
  refine ⟨140577796990540345114064821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187437062654053793485419761 140577796990540345114064821)
  ·
    refine ⟨13179168467863157354443577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140577796990540345114064821 13179168467863157354443577)
    ·
      refine ⟨9884376350897368015832683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13179168467863157354443577 9884376350897368015832683)
      ·
        refine ⟨14826564526346052023749025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9884376350897368015832683 14826564526346052023749025)
        ·
          refine ⟨11119923394759539017811769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14826564526346052023749025 11119923394759539017811769)
          ·
            refine ⟨8339942546069654263358827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11119923394759539017811769 8339942546069654263358827)
            ·
              refine ⟨12509913819104481395038241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8339942546069654263358827 12509913819104481395038241)
              ·
                refine ⟨9382435364328361046278681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12509913819104481395038241 9382435364328361046278681)
                ·
                  refine ⟨7036826523246270784709011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9382435364328361046278681 7036826523246270784709011)
                  ·
                    refine ⟨10555239784869406177063517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7036826523246270784709011 10555239784869406177063517)
                    ·
                      refine ⟨3958214919326027316398819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10555239784869406177063517 3958214919326027316398819)
                      ·
                        rfl

theorem cell23_7708596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_7708596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708596 prefixEnd_7708596 := by exact prefixLift 7708596
  have htrace : WordTrace (prefixWord ++ tailWord_7708596) baseStart_7708596 baseEnd_7708596 := by
    simpa [prefixWord, tailWord_7708596, baseEnd_7708596] using wordTrace_append hprefix tailTrace_7708596
  have hstable : (prefixWord ++ tailWord_7708596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708596).length < 2 ^ (prefixWord ++ tailWord_7708596).sum := by decide
  have hdescent : baseEnd_7708596 < baseStart_7708596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708608 : List Nat := [2, 1, 1, 2, 3, 2, 1, 6, 5]
def baseStart_7708608 : Nat := 118140960795 + 7708608 * 2 ^ 59
def prefixEnd_7708608 : Nat := 4983230072969 + 3 ^ 40 * 7708608 * 2
def baseEnd_7708608 : Nat := 439802342343764585494307

theorem tailTrace_7708608 : CollatzResearch.WordTrace tailWord_7708608 prefixEnd_7708608 439802342343764585494307 := by
  unfold tailWord_7708608
  simp only [CollatzResearch.WordTrace]
  refine ⟨140578015828518608138783239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187437354438024810851710985 140578015828518608138783239)
  ·
    refine ⟨210867023742777912208174859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140578015828518608138783239 210867023742777912208174859)
    ·
      refine ⟨316300535614166868312262289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210867023742777912208174859 316300535614166868312262289)
      ·
        refine ⟨237225401710625151234196717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316300535614166868312262289 237225401710625151234196717)
        ·
          refine ⟨88959525641484431712823769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237225401710625151234196717 88959525641484431712823769)
          ·
            refine ⟨66719644231113323784617827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88959525641484431712823769 66719644231113323784617827)
            ·
              refine ⟨100079466346669985676926741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66719644231113323784617827 100079466346669985676926741)
              ·
                refine ⟨4691224985000155578605941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100079466346669985676926741 4691224985000155578605941)
                ·
                  refine ⟨439802342343764585494307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4691224985000155578605941 439802342343764585494307)
                  ·
                    rfl

theorem cell23_7708608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 5].length) (baseStart_7708608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708608 prefixEnd_7708608 := by exact prefixLift 7708608
  have htrace : WordTrace (prefixWord ++ tailWord_7708608) baseStart_7708608 baseEnd_7708608 := by
    simpa [prefixWord, tailWord_7708608, baseEnd_7708608] using wordTrace_append hprefix tailTrace_7708608
  have hstable : (prefixWord ++ tailWord_7708608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708608).length < 2 ^ (prefixWord ++ tailWord_7708608).sum := by decide
  have hdescent : baseEnd_7708608 < baseStart_7708608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708618 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_7708618 : Nat := 118140960795 + 7708618 * 2 ^ 59
def prefixEnd_7708618 : Nat := 4983230072969 + 3 ^ 40 * 7708618 * 2
def baseEnd_7708618 : Nat := 3958226215900426230323717

theorem tailTrace_7708618 : CollatzResearch.WordTrace tailWord_7708618 prefixEnd_7708618 3958226215900426230323717 := by
  unfold tailWord_7708618
  simp only [CollatzResearch.WordTrace]
  refine ⟨70289099096750246996357627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187437597591333991990287005 70289099096750246996357627)
  ·
    refine ⟨105433648645125370494536441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70289099096750246996357627 105433648645125370494536441)
    ·
      refine ⟨79075236483844027870902331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105433648645125370494536441 79075236483844027870902331)
      ·
        refine ⟨118612854725766041806353497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79075236483844027870902331 118612854725766041806353497)
        ·
          refine ⟨88959641044324531354765123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118612854725766041806353497 88959641044324531354765123)
          ·
            refine ⟨133439461566486797032147685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88959641044324531354765123 133439461566486797032147685)
            ·
              refine ⟨25019899043716274443527691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133439461566486797032147685 25019899043716274443527691)
              ·
                refine ⟨37529848565574411665291537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25019899043716274443527691 37529848565574411665291537)
                ·
                  refine ⟨28147386424180808748968653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37529848565574411665291537 28147386424180808748968653)
                  ·
                    refine ⟨10555269909067803280863245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28147386424180808748968653 10555269909067803280863245)
                    ·
                      refine ⟨3958226215900426230323717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10555269909067803280863245 3958226215900426230323717)
                      ·
                        rfl

theorem cell23_7708618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_7708618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708618 prefixEnd_7708618 := by exact prefixLift 7708618
  have htrace : WordTrace (prefixWord ++ tailWord_7708618) baseStart_7708618 baseEnd_7708618 := by
    simpa [prefixWord, tailWord_7708618, baseEnd_7708618] using wordTrace_append hprefix tailTrace_7708618
  have hstable : (prefixWord ++ tailWord_7708618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708618).length < 2 ^ (prefixWord ++ tailWord_7708618).sum := by decide
  have hdescent : baseEnd_7708618 < baseStart_7708618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708671 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 6]
def baseStart_7708671 : Nat := 118140960795 + 7708671 * 2 ^ 59
def prefixEnd_7708671 : Nat := 4983230072969 + 3 ^ 40 * 7708671 * 2
def baseEnd_7708671 : Nat := 3958253430375114522960973

theorem tailTrace_7708671 : CollatzResearch.WordTrace tailWord_7708671 prefixEnd_7708671 3958253430375114522960973 := by
  unfold tailWord_7708671
  simp only [CollatzResearch.WordTrace]
  refine ⟨281158329455808978037109867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187438886303872652024739911 281158329455808978037109867)
  ·
    refine ⟨421737494183713467055664801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281158329455808978037109867 421737494183713467055664801)
    ·
      refine ⟨316303120637785100291748601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421737494183713467055664801 316303120637785100291748601)
      ·
        refine ⟨237227340478338825218811451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316303120637785100291748601 237227340478338825218811451)
        ·
          refine ⟨355841010717508237828217177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237227340478338825218811451 355841010717508237828217177)
          ·
            refine ⟨266880758038131178371162883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355841010717508237828217177 266880758038131178371162883)
            ·
              refine ⟨400321137057196767556744325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266880758038131178371162883 400321137057196767556744325)
              ·
                refine ⟨75060213198224393916889561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400321137057196767556744325 75060213198224393916889561)
                ·
                  refine ⟨56295159898668295437667171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75060213198224393916889561 56295159898668295437667171)
                  ·
                    refine ⟨84442739848002443156500757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56295159898668295437667171 84442739848002443156500757)
                    ·
                      refine ⟨3958253430375114522960973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84442739848002443156500757 3958253430375114522960973)
                      ·
                        rfl

theorem cell23_7708671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_7708671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708671 prefixEnd_7708671 := by exact prefixLift 7708671
  have htrace : WordTrace (prefixWord ++ tailWord_7708671) baseStart_7708671 baseEnd_7708671 := by
    simpa [prefixWord, tailWord_7708671, baseEnd_7708671] using wordTrace_append hprefix tailTrace_7708671
  have hstable : (prefixWord ++ tailWord_7708671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708671).length < 2 ^ (prefixWord ++ tailWord_7708671).sum := by decide
  have hdescent : baseEnd_7708671 < baseStart_7708671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708735 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 4, 3, 2]
def baseStart_7708735 : Nat := 118140960795 + 7708735 * 2 ^ 59
def prefixEnd_7708735 : Nat := 4983230072969 + 3 ^ 40 * 7708735 * 2
def baseEnd_7708735 : Nat := 3958286293137002272560679

theorem tailTrace_7708735 : CollatzResearch.WordTrace tailWord_7708735 prefixEnd_7708735 3958286293137002272560679 := by
  unfold tailWord_7708735
  simp only [CollatzResearch.WordTrace]
  refine ⟨281160663727577116967439659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187440442485051411311626439 281160663727577116967439659)
  ·
    refine ⟨421740995591365675451159489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281160663727577116967439659 421740995591365675451159489)
    ·
      refine ⟨316305746693524256588369617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421740995591365675451159489 316305746693524256588369617)
      ·
        refine ⟨237229310020143192441277213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316305746693524256588369617 237229310020143192441277213)
        ·
          refine ⟨88960991257553697165478955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237229310020143192441277213 88960991257553697165478955)
          ·
            refine ⟨133441486886330545748218433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88960991257553697165478955 133441486886330545748218433)
            ·
              refine ⟨100081115164747909311163825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133441486886330545748218433 100081115164747909311163825)
              ·
                refine ⟨75060836373560931983372869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100081115164747909311163825 75060836373560931983372869)
                ·
                  refine ⟨14073906820042674746882413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75060836373560931983372869 14073906820042674746882413)
                  ·
                    refine ⟨5277715057516003030080905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14073906820042674746882413 5277715057516003030080905)
                    ·
                      refine ⟨3958286293137002272560679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5277715057516003030080905 3958286293137002272560679)
                      ·
                        rfl

theorem cell23_7708735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 3, 2].length) (baseStart_7708735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708735 prefixEnd_7708735 := by exact prefixLift 7708735
  have htrace : WordTrace (prefixWord ++ tailWord_7708735) baseStart_7708735 baseEnd_7708735 := by
    simpa [prefixWord, tailWord_7708735, baseEnd_7708735] using wordTrace_append hprefix tailTrace_7708735
  have hstable : (prefixWord ++ tailWord_7708735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708735).length < 2 ^ (prefixWord ++ tailWord_7708735).sum := by decide
  have hdescent : baseEnd_7708735 < baseStart_7708735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708766 : List Nat := [4, 4, 1, 1, 2, 2, 1, 2, 6]
def baseStart_7708766 : Nat := 118140960795 + 7708766 * 2 ^ 59
def prefixEnd_7708766 : Nat := 4983230072969 + 3 ^ 40 * 7708766 * 2
def baseEnd_7708766 : Nat := 439811356781921294585893

theorem tailTrace_7708766 : CollatzResearch.WordTrace tailWord_7708766 prefixEnd_7708766 439811356781921294585893 := by
  unfold tailWord_7708766
  simp only [CollatzResearch.WordTrace]
  refine ⟨35145224298808101157727269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187441196260309872841212101 35145224298808101157727269)
  ·
    refine ⟨6589729556026518967073863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35145224298808101157727269 6589729556026518967073863)
    ·
      refine ⟨9884594334039778450610795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6589729556026518967073863 9884594334039778450610795)
      ·
        refine ⟨14826891501059667675916193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9884594334039778450610795 14826891501059667675916193)
        ·
          refine ⟨11120168625794750756937145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14826891501059667675916193 11120168625794750756937145)
          ·
            refine ⟨8340126469346063067702859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11120168625794750756937145 8340126469346063067702859)
            ·
              refine ⟨12510189704019094601554289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8340126469346063067702859 12510189704019094601554289)
              ·
                refine ⟨9382642278014320951165717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12510189704019094601554289 9382642278014320951165717)
                ·
                  refine ⟨439811356781921294585893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9382642278014320951165717 439811356781921294585893)
                  ·
                    rfl

theorem cell23_7708766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_7708766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708766 prefixEnd_7708766 := by exact prefixLift 7708766
  have htrace : WordTrace (prefixWord ++ tailWord_7708766) baseStart_7708766 baseEnd_7708766 := by
    simpa [prefixWord, tailWord_7708766, baseEnd_7708766] using wordTrace_append hprefix tailTrace_7708766
  have hstable : (prefixWord ++ tailWord_7708766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708766).length < 2 ^ (prefixWord ++ tailWord_7708766).sum := by decide
  have hdescent : baseEnd_7708766 < baseStart_7708766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708775 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 4, 4]
def baseStart_7708775 : Nat := 118140960795 + 7708775 * 2 ^ 59
def prefixEnd_7708775 : Nat := 4983230072969 + 3 ^ 40 * 7708775 * 2
def baseEnd_7708775 : Nat := 1319435610787727372020165

theorem tailTrace_7708775 : CollatzResearch.WordTrace tailWord_7708775 prefixEnd_7708775 1319435610787727372020165 := by
  unfold tailWord_7708775
  simp only [CollatzResearch.WordTrace]
  refine ⟨281162122647432203798895779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187441415098288135865930519 281162122647432203798895779)
  ·
    refine ⟨421743183971148305698343669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281162122647432203798895779 421743183971148305698343669)
    ·
      refine ⟨39538423497295153659219719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 421743183971148305698343669 39538423497295153659219719)
      ·
        refine ⟨59307635245942730488829579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39538423497295153659219719 59307635245942730488829579)
        ·
          refine ⟨88961452868914095733244369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59307635245942730488829579 88961452868914095733244369)
          ·
            refine ⟨66721089651685571799933277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88961452868914095733244369 66721089651685571799933277)
            ·
              refine ⟨25020408619382089424974979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66721089651685571799933277 25020408619382089424974979)
              ·
                refine ⟨37530612929073134137462469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25020408619382089424974979 37530612929073134137462469)
                ·
                  refine ⟨7036989924201212650774213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37530612929073134137462469 7036989924201212650774213)
                  ·
                    refine ⟨1319435610787727372020165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7036989924201212650774213 1319435610787727372020165)
                    ·
                      rfl

theorem cell23_7708775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_7708775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708775 prefixEnd_7708775 := by exact prefixLift 7708775
  have htrace : WordTrace (prefixWord ++ tailWord_7708775) baseStart_7708775 baseEnd_7708775 := by
    simpa [prefixWord, tailWord_7708775, baseEnd_7708775] using wordTrace_append hprefix tailTrace_7708775
  have hstable : (prefixWord ++ tailWord_7708775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708775).length < 2 ^ (prefixWord ++ tailWord_7708775).sum := by decide
  have hdescent : baseEnd_7708775 < baseStart_7708775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708805 : List Nat := [1, 3, 1, 1, 5, 1, 4, 7]
def baseStart_7708805 : Nat := 118140960795 + 7708805 * 2 ^ 59
def prefixEnd_7708805 : Nat := 4983230072969 + 3 ^ 40 * 7708805 * 2
def baseEnd_7708805 : Nat := 146604527288252481432791

theorem tailTrace_7708805 : CollatzResearch.WordTrace tailWord_7708805 prefixEnd_7708805 146604527288252481432791 := by
  unfold tailWord_7708805
  simp only [CollatzResearch.WordTrace]
  refine ⟨281163216837323518922487869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187442144558215679281658579 281163216837323518922487869)
  ·
    refine ⟨105436206313996319595932951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281163216837323518922487869 105436206313996319595932951)
    ·
      refine ⟨158154309470994479393899427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105436206313996319595932951 158154309470994479393899427)
      ·
        refine ⟨237231464206491719090849141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158154309470994479393899427 237231464206491719090849141)
        ·
          refine ⟨22240449769358598664767107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237231464206491719090849141 22240449769358598664767107)
          ·
            refine ⟨33360674654037897997150661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22240449769358598664767107 33360674654037897997150661)
            ·
              refine ⟨6255126497632105874465749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33360674654037897997150661 6255126497632105874465749)
              ·
                refine ⟨146604527288252481432791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6255126497632105874465749 146604527288252481432791)
                ·
                  rfl

theorem cell23_7708805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 7].length) (baseStart_7708805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708805 prefixEnd_7708805 := by exact prefixLift 7708805
  have htrace : WordTrace (prefixWord ++ tailWord_7708805) baseStart_7708805 baseEnd_7708805 := by
    simpa [prefixWord, tailWord_7708805, baseEnd_7708805] using wordTrace_append hprefix tailTrace_7708805
  have hstable : (prefixWord ++ tailWord_7708805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708805).length < 2 ^ (prefixWord ++ tailWord_7708805).sum := by decide
  have hdescent : baseEnd_7708805 < baseStart_7708805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708832 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 4, 1, 3]
def baseStart_7708832 : Nat := 118140960795 + 7708832 * 2 ^ 59
def prefixEnd_7708832 : Nat := 4983230072969 + 3 ^ 40 * 7708832 * 2
def baseEnd_7708832 : Nat := 3958336100760488393047733

theorem tailTrace_7708832 : CollatzResearch.WordTrace tailWord_7708832 prefixEnd_7708832 3958336100760488393047733 := by
  unfold tailWord_7708832
  simp only [CollatzResearch.WordTrace]
  refine ⟨140582100804112851266860375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187442801072150468355813833 140582100804112851266860375)
  ·
    refine ⟨210873151206169276900290563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140582100804112851266860375 210873151206169276900290563)
    ·
      refine ⟨316309726809253915350435845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210873151206169276900290563 316309726809253915350435845)
      ·
        refine ⟨59308073776735109128206721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316309726809253915350435845 59308073776735109128206721)
        ·
          refine ⟨44481055332551331846155041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59308073776735109128206721 44481055332551331846155041)
          ·
            refine ⟨33360791499413498884616281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44481055332551331846155041 33360791499413498884616281)
            ·
              refine ⟨25020593624560124163462211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33360791499413498884616281 25020593624560124163462211)
              ·
                refine ⟨37530890436840186245193317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25020593624560124163462211 37530890436840186245193317)
                ·
                  refine ⟨7037041956907534920973747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37530890436840186245193317 7037041956907534920973747)
                  ·
                    refine ⟨10555562935361302381460621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7037041956907534920973747 10555562935361302381460621)
                    ·
                      refine ⟨3958336100760488393047733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10555562935361302381460621 3958336100760488393047733)
                      ·
                        rfl

theorem cell23_7708832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_7708832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708832 prefixEnd_7708832 := by exact prefixLift 7708832
  have htrace : WordTrace (prefixWord ++ tailWord_7708832) baseStart_7708832 baseEnd_7708832 := by
    simpa [prefixWord, tailWord_7708832, baseEnd_7708832] using wordTrace_append hprefix tailTrace_7708832
  have hstable : (prefixWord ++ tailWord_7708832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708832).length < 2 ^ (prefixWord ++ tailWord_7708832).sum := by decide
  have hdescent : baseEnd_7708832 < baseStart_7708832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708833 : List Nat := [1, 2, 3, 3, 1, 3, 3, 2, 1, 2, 2]
def baseStart_7708833 : Nat := 118140960795 + 7708833 * 2 ^ 59
def prefixEnd_7708833 : Nat := 4983230072969 + 3 ^ 40 * 7708833 * 2
def baseEnd_7708833 : Nat := 3958336614241142889135229

theorem tailTrace_7708833 : CollatzResearch.WordTrace tailWord_7708833 prefixEnd_7708833 3958336614241142889135229 := by
  unfold tailWord_7708833
  simp only [CollatzResearch.WordTrace]
  refine ⟨281164238081222079704507153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187442825387481386469671435 281164238081222079704507153)
  ·
    refine ⟨210873178560916559778380365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281164238081222079704507153 210873178560916559778380365)
    ·
      refine ⟨79077441960343709916892637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210873178560916559778380365 79077441960343709916892637)
      ·
        refine ⟨29654040735128891218834739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79077441960343709916892637 29654040735128891218834739)
        ·
          refine ⟨44481061102693336828252109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29654040735128891218834739 44481061102693336828252109)
          ·
            refine ⟨16680397913510001310594541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44481061102693336828252109 16680397913510001310594541)
            ·
              refine ⟨6255149217566250491472953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16680397913510001310594541 6255149217566250491472953)
              ·
                refine ⟨4691361913174687868604715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6255149217566250491472953 4691361913174687868604715)
                ·
                  refine ⟨7037042869762031802907073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4691361913174687868604715 7037042869762031802907073)
                  ·
                    refine ⟨5277782152321523852180305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7037042869762031802907073 5277782152321523852180305)
                    ·
                      refine ⟨3958336614241142889135229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5277782152321523852180305 3958336614241142889135229)
                      ·
                        rfl

theorem cell23_7708833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_7708833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708833 prefixEnd_7708833 := by exact prefixLift 7708833
  have htrace : WordTrace (prefixWord ++ tailWord_7708833) baseStart_7708833 baseEnd_7708833 := by
    simpa [prefixWord, tailWord_7708833, baseEnd_7708833] using wordTrace_append hprefix tailTrace_7708833
  have hstable : (prefixWord ++ tailWord_7708833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708833).length < 2 ^ (prefixWord ++ tailWord_7708833).sum := by decide
  have hdescent : baseEnd_7708833 < baseStart_7708833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708853 : List Nat := [1, 3, 3, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_7708853 : Nat := 118140960795 + 7708853 * 2 ^ 59
def prefixEnd_7708853 : Nat := 4983230072969 + 3 ^ 40 * 7708853 * 2
def baseEnd_7708853 : Nat := 3958346883854232810885137

theorem tailTrace_7708853 : CollatzResearch.WordTrace tailWord_7708853 prefixEnd_7708853 3958346883854232810885137 := by
  unfold tailWord_7708853
  simp only [CollatzResearch.WordTrace]
  refine ⟨281164967541149623120235213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187443311694099748746823475 281164967541149623120235213)
  ·
    refine ⟨105436862827931108670088205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281164967541149623120235213 105436862827931108670088205)
    ·
      refine ⟨39538823560474165751283077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105436862827931108670088205 39538823560474165751283077)
      ·
        refine ⟨7413529417588906078365577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39538823560474165751283077 7413529417588906078365577)
        ·
          refine ⟨5560147063191679558774183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7413529417588906078365577 5560147063191679558774183)
          ·
            refine ⟨8340220594787519338161275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5560147063191679558774183 8340220594787519338161275)
            ·
              refine ⟨12510330892181279007241913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8340220594787519338161275 12510330892181279007241913)
              ·
                refine ⟨9382748169135959255431435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12510330892181279007241913 9382748169135959255431435)
                ·
                  refine ⟨14074122253703938883147153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9382748169135959255431435 14074122253703938883147153)
                  ·
                    refine ⟨10555591690277954162360365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14074122253703938883147153 10555591690277954162360365)
                    ·
                      refine ⟨3958346883854232810885137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10555591690277954162360365 3958346883854232810885137)
                      ·
                        rfl

theorem cell23_7708853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_7708853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708853 prefixEnd_7708853 := by exact prefixLift 7708853
  have htrace : WordTrace (prefixWord ++ tailWord_7708853) baseStart_7708853 baseEnd_7708853 := by
    simpa [prefixWord, tailWord_7708853, baseEnd_7708853] using wordTrace_append hprefix tailTrace_7708853
  have hstable : (prefixWord ++ tailWord_7708853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708853).length < 2 ^ (prefixWord ++ tailWord_7708853).sum := by decide
  have hdescent : baseEnd_7708853 < baseStart_7708853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708866 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_7708866 : Nat := 118140960795 + 7708866 * 2 ^ 59
def prefixEnd_7708866 : Nat := 4983230072969 + 3 ^ 40 * 7708866 * 2
def baseEnd_7708866 : Nat := 3958353559102741260022577

theorem tailTrace_7708866 : CollatzResearch.WordTrace tailWord_7708866 prefixEnd_7708866 3958353559102741260022577 := by
  unfold tailWord_7708866
  simp only [CollatzResearch.WordTrace]
  refine ⟨70291360422525631585114613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187443627793401684226972301 70291360422525631585114613)
  ·
    refine ⟨6589815039611777961104495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70291360422525631585114613 6589815039611777961104495)
    ·
      refine ⟨9884722559417666941656743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6589815039611777961104495 9884722559417666941656743)
      ·
        refine ⟨14827083839126500412485115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9884722559417666941656743 14827083839126500412485115)
        ·
          refine ⟨22240625758689750618727673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14827083839126500412485115 22240625758689750618727673)
          ·
            refine ⟨16680469319017312964045755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22240625758689750618727673 16680469319017312964045755)
            ·
              refine ⟨25020703978525969446068633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16680469319017312964045755 25020703978525969446068633)
              ·
                refine ⟨18765527983894477084551475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25020703978525969446068633 18765527983894477084551475)
                ·
                  refine ⟨28148291975841715626827213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18765527983894477084551475 28148291975841715626827213)
                  ·
                    refine ⟨10555609490940643360060205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28148291975841715626827213 10555609490940643360060205)
                    ·
                      refine ⟨3958353559102741260022577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10555609490940643360060205 3958353559102741260022577)
                      ·
                        rfl

theorem cell23_7708866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_7708866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708866 prefixEnd_7708866 := by exact prefixLift 7708866
  have htrace : WordTrace (prefixWord ++ tailWord_7708866) baseStart_7708866 baseEnd_7708866 := by
    simpa [prefixWord, tailWord_7708866, baseEnd_7708866] using wordTrace_append hprefix tailTrace_7708866
  have hstable : (prefixWord ++ tailWord_7708866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708866).length < 2 ^ (prefixWord ++ tailWord_7708866).sum := by decide
  have hdescent : baseEnd_7708866 < baseStart_7708866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708889 : List Nat := [1, 2, 1, 2, 3, 1, 3, 4, 2, 2, 2]
def baseStart_7708889 : Nat := 118140960795 + 7708889 * 2 ^ 59
def prefixEnd_7708889 : Nat := 4983230072969 + 3 ^ 40 * 7708889 * 2
def baseEnd_7708889 : Nat := 3958365369157794670034971

theorem tailTrace_7708889 : CollatzResearch.WordTrace tailWord_7708889 prefixEnd_7708889 3958365369157794670034971 := by
  unfold tailWord_7708889
  simp only [CollatzResearch.WordTrace]
  refine ⟨281166280569019201268545721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187444187046012800845697147 281166280569019201268545721)
  ·
    refine ⟨210874710426764400951409291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281166280569019201268545721 210874710426764400951409291)
    ·
      refine ⟨316312065640146601427113937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210874710426764400951409291 316312065640146601427113937)
      ·
        refine ⟨237234049230109951070335453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316312065640146601427113937 237234049230109951070335453)
        ·
          refine ⟨88962768461291231651375795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237234049230109951070335453 88962768461291231651375795)
          ·
            refine ⟨133444152691936847477063693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88962768461291231651375795 133444152691936847477063693)
            ·
              refine ⟨50041557259476317803898885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133444152691936847477063693 50041557259476317803898885)
              ·
                refine ⟨9382791986151809588231041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50041557259476317803898885 9382791986151809588231041)
                ·
                  refine ⟨7037093989613857191173281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9382791986151809588231041 7037093989613857191173281)
                  ·
                    refine ⟨5277820492210392893379961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7037093989613857191173281 5277820492210392893379961)
                    ·
                      refine ⟨3958365369157794670034971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5277820492210392893379961 3958365369157794670034971)
                      ·
                        rfl

theorem cell23_7708889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 2, 2].length) (baseStart_7708889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708889 prefixEnd_7708889 := by exact prefixLift 7708889
  have htrace : WordTrace (prefixWord ++ tailWord_7708889) baseStart_7708889 baseEnd_7708889 := by
    simpa [prefixWord, tailWord_7708889, baseEnd_7708889] using wordTrace_append hprefix tailTrace_7708889
  have hstable : (prefixWord ++ tailWord_7708889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708889).length < 2 ^ (prefixWord ++ tailWord_7708889).sum := by decide
  have hdescent : baseEnd_7708889 < baseStart_7708889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708905 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 2, 3, 3]
def baseStart_7708905 : Nat := 118140960795 + 7708905 * 2 ^ 59
def prefixEnd_7708905 : Nat := 4983230072969 + 3 ^ 40 * 7708905 * 2
def baseEnd_7708905 : Nat := 3958373584848266607434897

theorem tailTrace_7708905 : CollatzResearch.WordTrace tailWord_7708905 prefixEnd_7708905 3958373584848266607434897 := by
  unfold tailWord_7708905
  simp only [CollatzResearch.WordTrace]
  refine ⟨281166864136961236001128169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187444576091307490667418779 281166864136961236001128169)
  ·
    refine ⟨210875148102720927000846127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281166864136961236001128169 210875148102720927000846127)
    ·
      refine ⟨316312722154081390501269191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210875148102720927000846127 316312722154081390501269191)
      ·
        refine ⟨474469083231122085751903787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316312722154081390501269191 474469083231122085751903787)
        ·
          refine ⟨711703624846683128627855681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474469083231122085751903787 711703624846683128627855681)
          ·
            refine ⟨533777718635012346470891761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711703624846683128627855681 533777718635012346470891761)
            ·
              refine ⟨400333288976259259853168821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533777718635012346470891761 400333288976259259853168821)
              ·
                refine ⟨37531245841524305611234577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 400333288976259259853168821 37531245841524305611234577)
                ·
                  refine ⟨28148434381143229208425933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37531245841524305611234577 28148434381143229208425933)
                  ·
                    refine ⟨10555662892928710953159725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28148434381143229208425933 10555662892928710953159725)
                    ·
                      refine ⟨3958373584848266607434897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10555662892928710953159725 3958373584848266607434897)
                      ·
                        rfl

theorem cell23_7708905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 3, 3].length) (baseStart_7708905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708905 prefixEnd_7708905 := by exact prefixLift 7708905
  have htrace : WordTrace (prefixWord ++ tailWord_7708905) baseStart_7708905 baseEnd_7708905 := by
    simpa [prefixWord, tailWord_7708905, baseEnd_7708905] using wordTrace_append hprefix tailTrace_7708905
  have hstable : (prefixWord ++ tailWord_7708905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708905).length < 2 ^ (prefixWord ++ tailWord_7708905).sum := by decide
  have hdescent : baseEnd_7708905 < baseStart_7708905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708962 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_7708962 : Nat := 118140960795 + 7708962 * 2 ^ 59
def prefixEnd_7708962 : Nat := 4983230072969 + 3 ^ 40 * 7708962 * 2
def baseEnd_7708962 : Nat := 3958402853245572884422135

theorem tailTrace_7708962 : CollatzResearch.WordTrace tailWord_7708962 prefixEnd_7708962 3958402853245572884422135 := by
  unfold tailWord_7708962
  simp only [CollatzResearch.WordTrace]
  refine ⟨70292235774438683683988285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187445962065169823157302093 70292235774438683683988285)
  ·
    refine ⟨26359588415414506381495607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70292235774438683683988285 26359588415414506381495607)
    ·
      refine ⟨39539382623121759572243411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26359588415414506381495607 39539382623121759572243411)
      ·
        refine ⟨59309073934682639358365117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39539382623121759572243411 59309073934682639358365117)
        ·
          refine ⟨22240902725505989759386919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59309073934682639358365117 22240902725505989759386919)
          ·
            refine ⟨33361354088258984639080379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22240902725505989759386919 33361354088258984639080379)
            ·
              refine ⟨50042031132388476958620569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33361354088258984639080379 50042031132388476958620569)
              ·
                refine ⟨37531523349291357718965427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50042031132388476958620569 37531523349291357718965427)
                ·
                  refine ⟨56297285023937036578448141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37531523349291357718965427 56297285023937036578448141)
                  ·
                    refine ⟨21111481883976388716918053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56297285023937036578448141 21111481883976388716918053)
                    ·
                      refine ⟨3958402853245572884422135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21111481883976388716918053 3958402853245572884422135)
                      ·
                        rfl

theorem cell23_7708962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_7708962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708962 prefixEnd_7708962 := by exact prefixLift 7708962
  have htrace : WordTrace (prefixWord ++ tailWord_7708962) baseStart_7708962 baseEnd_7708962 := by
    simpa [prefixWord, tailWord_7708962, baseEnd_7708962] using wordTrace_append hprefix tailTrace_7708962
  have hstable : (prefixWord ++ tailWord_7708962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708962).length < 2 ^ (prefixWord ++ tailWord_7708962).sum := by decide
  have hdescent : baseEnd_7708962 < baseStart_7708962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708972 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 3, 4]
def baseStart_7708972 : Nat := 118140960795 + 7708972 * 2 ^ 59
def prefixEnd_7708972 : Nat := 4983230072969 + 3 ^ 40 * 7708972 * 2
def baseEnd_7708972 : Nat := 1319469329350705948432363

theorem tailTrace_7708972 : CollatzResearch.WordTrace tailWord_7708972 prefixEnd_7708972 1319469329350705948432363 := by
  unfold tailWord_7708972
  simp only [CollatzResearch.WordTrace]
  refine ⟨140584653913859253221908585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187446205218479004295878113 140584653913859253221908585)
  ·
    refine ⟨105438490435394439916431439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140584653913859253221908585 105438490435394439916431439)
    ·
      refine ⟨158157735653091659874647159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105438490435394439916431439 158157735653091659874647159)
      ·
        refine ⟨237236603479637489811970739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158157735653091659874647159 237236603479637489811970739)
        ·
          refine ⟨355854905219456234717956109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237236603479637489811970739 355854905219456234717956109)
          ·
            refine ⟨133445589457296088019233541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355854905219456234717956109 133445589457296088019233541)
            ·
              refine ⟨25021048023243016503606289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133445589457296088019233541 25021048023243016503606289)
              ·
                refine ⟨18765786017432262377704717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25021048023243016503606289 18765786017432262377704717)
                ·
                  refine ⟨7037169756537098391639269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18765786017432262377704717 7037169756537098391639269)
                  ·
                    refine ⟨1319469329350705948432363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7037169756537098391639269 1319469329350705948432363)
                    ·
                      rfl

theorem cell23_7708972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_7708972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708972 prefixEnd_7708972 := by exact prefixLift 7708972
  have htrace : WordTrace (prefixWord ++ tailWord_7708972) baseStart_7708972 baseEnd_7708972 := by
    simpa [prefixWord, tailWord_7708972, baseEnd_7708972] using wordTrace_append hprefix tailTrace_7708972
  have hstable : (prefixWord ++ tailWord_7708972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708972).length < 2 ^ (prefixWord ++ tailWord_7708972).sum := by decide
  have hdescent : baseEnd_7708972 < baseStart_7708972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7708996 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_7708996 : Nat := 118140960795 + 7708996 * 2 ^ 59
def prefixEnd_7708996 : Nat := 4983230072969 + 3 ^ 40 * 7708996 * 2
def baseEnd_7708996 : Nat := 3958420311587825751396979

theorem tailTrace_7708996 : CollatzResearch.WordTrace tailWord_7708996 prefixEnd_7708996 3958420311587825751396979 := by
  unfold tailWord_7708996
  simp only [CollatzResearch.WordTrace]
  refine ⟨140585091589815779271345421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187446788786421039028460561 140585091589815779271345421)
  ·
    refine ⟨52719409346180917226754533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140585091589815779271345421 52719409346180917226754533)
    ·
      refine ⟨9884889252408921980016475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52719409346180917226754533 9884889252408921980016475)
      ·
        refine ⟨14827333878613382970024713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9884889252408921980016475 14827333878613382970024713)
        ·
          refine ⟨11120500408960037227518535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14827333878613382970024713 11120500408960037227518535)
          ·
            refine ⟨16680750613440055841277803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11120500408960037227518535 16680750613440055841277803)
            ·
              refine ⟨25021125920160083761916705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16680750613440055841277803 25021125920160083761916705)
              ·
                refine ⟨18765844440120062821437529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25021125920160083761916705 18765844440120062821437529)
                ·
                  refine ⟨14074383330090047116078147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18765844440120062821437529 14074383330090047116078147)
                  ·
                    refine ⟨21111574995135070674117221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14074383330090047116078147 21111574995135070674117221)
                    ·
                      refine ⟨3958420311587825751396979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21111574995135070674117221 3958420311587825751396979)
                      ·
                        rfl

theorem cell23_7708996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_7708996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7708996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7708996 prefixEnd_7708996 := by exact prefixLift 7708996
  have htrace : WordTrace (prefixWord ++ tailWord_7708996) baseStart_7708996 baseEnd_7708996 := by
    simpa [prefixWord, tailWord_7708996, baseEnd_7708996] using wordTrace_append hprefix tailTrace_7708996
  have hstable : (prefixWord ++ tailWord_7708996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7708996).length < 2 ^ (prefixWord ++ tailWord_7708996).sum := by decide
  have hdescent : baseEnd_7708996 < baseStart_7708996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7708996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709035 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 4]
def baseStart_7709035 : Nat := 118140960795 + 7709035 * 2 ^ 59
def prefixEnd_7709035 : Nat := 4983230072969 + 3 ^ 40 * 7709035 * 2
def baseEnd_7709035 : Nat := 3958440337333351098809299

theorem tailTrace_7709035 : CollatzResearch.WordTrace tailWord_7709035 prefixEnd_7709035 3958440337333351098809299 := by
  unfold tailWord_7709035
  simp only [CollatzResearch.WordTrace]
  refine ⟨281171605626490268203360559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187447737084326845468907039 281171605626490268203360559)
  ·
    refine ⟨421757408439735402305040839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281171605626490268203360559 421757408439735402305040839)
    ·
      refine ⟨632636112659603103457561259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421757408439735402305040839 632636112659603103457561259)
      ·
        refine ⟨948954168989404655186341889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632636112659603103457561259 948954168989404655186341889)
        ·
          refine ⟨711715626742053491389756417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 948954168989404655186341889 711715626742053491389756417)
          ·
            refine ⟨533786720056540118542317313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711715626742053491389756417 533786720056540118542317313)
            ·
              refine ⟨400340040042405088906737985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533786720056540118542317313 400340040042405088906737985)
              ·
                refine ⟨300255030031803816680053489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400340040042405088906737985 300255030031803816680053489)
                ·
                  refine ⟨225191272523852862510040117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300255030031803816680053489 225191272523852862510040117)
                  ·
                    refine ⟨21111681799111205860316261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 225191272523852862510040117 21111681799111205860316261)
                    ·
                      refine ⟨3958440337333351098809299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21111681799111205860316261 3958440337333351098809299)
                      ·
                        rfl

theorem cell23_7709035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 4].length) (baseStart_7709035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709035 prefixEnd_7709035 := by exact prefixLift 7709035
  have htrace : WordTrace (prefixWord ++ tailWord_7709035) baseStart_7709035 baseEnd_7709035 := by
    simpa [prefixWord, tailWord_7709035, baseEnd_7709035] using wordTrace_append hprefix tailTrace_7709035
  have hstable : (prefixWord ++ tailWord_7709035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709035).length < 2 ^ (prefixWord ++ tailWord_7709035).sum := by decide
  have hdescent : baseEnd_7709035 < baseStart_7709035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709079 : List Nat := [1, 1, 3, 3, 1, 1, 4, 3, 2, 4]
def baseStart_7709079 : Nat := 118140960795 + 7709079 * 2 ^ 59
def prefixEnd_7709079 : Nat := 4983230072969 + 3 ^ 40 * 7709079 * 2
def baseEnd_7709079 : Nat := 1319487643494049642219699

theorem tailTrace_7709079 : CollatzResearch.WordTrace tailWord_7709079 prefixEnd_7709079 1319487643494049642219699 := by
  unfold tailWord_7709079
  simp only [CollatzResearch.WordTrace]
  refine ⟨281173210438330863717962291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187448806958887242478641527 281173210438330863717962291)
  ·
    refine ⟨421759815657496295576943437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281173210438330863717962291 421759815657496295576943437)
    ·
      refine ⟨158159930871561110841353789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421759815657496295576943437 158159930871561110841353789)
      ·
        refine ⟨59309974076835416565507671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158159930871561110841353789 59309974076835416565507671)
        ·
          refine ⟨88964961115253124848261507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59309974076835416565507671 88964961115253124848261507)
          ·
            refine ⟨133447441672879687272392261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88964961115253124848261507 133447441672879687272392261)
            ·
              refine ⟨25021395313664941363573549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133447441672879687272392261 25021395313664941363573549)
              ·
                refine ⟨9383023242624353011340081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25021395313664941363573549 9383023242624353011340081)
                ·
                  refine ⟨7037267431968264758505061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9383023242624353011340081 7037267431968264758505061)
                  ·
                    refine ⟨1319487643494049642219699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7037267431968264758505061 1319487643494049642219699)
                    ·
                      rfl

theorem cell23_7709079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_7709079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709079 prefixEnd_7709079 := by exact prefixLift 7709079
  have htrace : WordTrace (prefixWord ++ tailWord_7709079) baseStart_7709079 baseEnd_7709079 := by
    simpa [prefixWord, tailWord_7709079, baseEnd_7709079] using wordTrace_append hprefix tailTrace_7709079
  have hstable : (prefixWord ++ tailWord_7709079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709079).length < 2 ^ (prefixWord ++ tailWord_7709079).sum := by decide
  have hdescent : baseEnd_7709079 < baseStart_7709079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709086 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7709086 : Nat := 118140960795 + 7709086 * 2 ^ 59
def prefixEnd_7709086 : Nat := 4983230072969 + 3 ^ 40 * 7709086 * 2
def baseEnd_7709086 : Nat := 3958466524846730399271565

theorem tailTrace_7709086 : CollatzResearch.WordTrace tailWord_7709086 prefixEnd_7709086 3958466524846730399271565 := by
  unfold tailWord_7709086
  simp only [CollatzResearch.WordTrace]
  refine ⟨35146683218663187989183389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187448977166203669275644741 35146683218663187989183389)
  ·
    refine ⟨13180006206998695495943771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35146683218663187989183389 13180006206998695495943771)
    ·
      refine ⟨19770009310498043243915657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13180006206998695495943771 19770009310498043243915657)
      ·
        refine ⟨14827506982873532432936743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19770009310498043243915657 14827506982873532432936743)
        ·
          refine ⟨22241260474310298649405115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14827506982873532432936743 22241260474310298649405115)
          ·
            refine ⟨33361890711465447974107673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22241260474310298649405115 33361890711465447974107673)
            ·
              refine ⟨25021418033599085980580755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33361890711465447974107673 25021418033599085980580755)
              ·
                refine ⟨37532127050398628970871133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25021418033599085980580755 37532127050398628970871133)
                ·
                  refine ⟨14074547643899485864076675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37532127050398628970871133 14074547643899485864076675)
                  ·
                    refine ⟨21111821465849228796115013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14074547643899485864076675 21111821465849228796115013)
                    ·
                      refine ⟨3958466524846730399271565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21111821465849228796115013 3958466524846730399271565)
                      ·
                        rfl

theorem cell23_7709086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7709086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709086 prefixEnd_7709086 := by exact prefixLift 7709086
  have htrace : WordTrace (prefixWord ++ tailWord_7709086) baseStart_7709086 baseEnd_7709086 := by
    simpa [prefixWord, tailWord_7709086, baseEnd_7709086] using wordTrace_append hprefix tailTrace_7709086
  have hstable : (prefixWord ++ tailWord_7709086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709086).length < 2 ^ (prefixWord ++ tailWord_7709086).sum := by decide
  have hdescent : baseEnd_7709086 < baseStart_7709086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709129 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 5, 3, 2]
def baseStart_7709129 : Nat := 118140960795 + 7709129 * 2 ^ 59
def prefixEnd_7709129 : Nat := 4983230072969 + 3 ^ 40 * 7709129 * 2
def baseEnd_7709129 : Nat := 3958488604514873731033867

theorem tailTrace_7709129 : CollatzResearch.WordTrace tailWord_7709129 prefixEnd_7709129 3958488604514873731033867 := by
  unfold tailWord_7709129
  simp only [CollatzResearch.WordTrace]
  refine ⟨281175034088149722257282441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187450022725433148171521627 281175034088149722257282441)
  ·
    refine ⟨210881275566112291692961831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281175034088149722257282441 210881275566112291692961831)
    ·
      refine ⟨316321913349168437539442747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210881275566112291692961831 316321913349168437539442747)
      ·
        refine ⟨474482870023752656309164121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316321913349168437539442747 474482870023752656309164121)
        ·
          refine ⟨355862152517814492231873091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474482870023752656309164121 355862152517814492231873091)
          ·
            refine ⟨533793228776721738347809637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355862152517814492231873091 533793228776721738347809637)
            ·
              refine ⟨100086230395635325940214307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 533793228776721738347809637 100086230395635325940214307)
              ·
                refine ⟨150129345593452988910321461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100086230395635325940214307 150129345593452988910321461)
                ·
                  refine ⟨14074626149386217710342637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150129345593452988910321461 14074626149386217710342637)
                  ·
                    refine ⟨5277984806019831641378489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14074626149386217710342637 5277984806019831641378489)
                    ·
                      refine ⟨3958488604514873731033867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5277984806019831641378489 3958488604514873731033867)
                      ·
                        rfl

theorem cell23_7709129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 3, 2].length) (baseStart_7709129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709129 prefixEnd_7709129 := by exact prefixLift 7709129
  have htrace : WordTrace (prefixWord ++ tailWord_7709129) baseStart_7709129 baseEnd_7709129 := by
    simpa [prefixWord, tailWord_7709129, baseEnd_7709129] using wordTrace_append hprefix tailTrace_7709129
  have hstable : (prefixWord ++ tailWord_7709129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709129).length < 2 ^ (prefixWord ++ tailWord_7709129).sum := by decide
  have hdescent : baseEnd_7709129 < baseStart_7709129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709176 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 4, 2, 2]
def baseStart_7709176 : Nat := 118140960795 + 7709176 * 2 ^ 59
def prefixEnd_7709176 : Nat := 4983230072969 + 3 ^ 40 * 7709176 * 2
def baseEnd_7709176 : Nat := 3958512738105635047146151

theorem tailTrace_7709176 : CollatzResearch.WordTrace tailWord_7709176 prefixEnd_7709176 3958512738105635047146151 := by
  unfold tailWord_7709176
  simp only [CollatzResearch.WordTrace]
  refine ⟨140588374159489724642121691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187451165545986299522828921 140588374159489724642121691)
  ·
    refine ⟨210882561239234586963182537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140588374159489724642121691 210882561239234586963182537)
    ·
      refine ⟨158161920929425940222386903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210882561239234586963182537 158161920929425940222386903)
      ·
        refine ⟨237242881394138910333580355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158161920929425940222386903 237242881394138910333580355)
        ·
          refine ⟨355864322091208365500370533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237242881394138910333580355 355864322091208365500370533)
          ·
            refine ⟨66724560392101568531319475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355864322091208365500370533 66724560392101568531319475)
            ·
              refine ⟨100086840588152352796979213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66724560392101568531319475 100086840588152352796979213)
              ·
                refine ⟨37532565220557132298867205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100086840588152352796979213 37532565220557132298867205)
                ·
                  refine ⟨7037355978854462306037601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37532565220557132298867205 7037355978854462306037601)
                  ·
                    refine ⟨5278016984140846729528201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7037355978854462306037601 5278016984140846729528201)
                    ·
                      refine ⟨3958512738105635047146151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278016984140846729528201 3958512738105635047146151)
                      ·
                        rfl

theorem cell23_7709176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 4, 2, 2].length) (baseStart_7709176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709176 prefixEnd_7709176 := by exact prefixLift 7709176
  have htrace : WordTrace (prefixWord ++ tailWord_7709176) baseStart_7709176 baseEnd_7709176 := by
    simpa [prefixWord, tailWord_7709176, baseEnd_7709176] using wordTrace_append hprefix tailTrace_7709176
  have hstable : (prefixWord ++ tailWord_7709176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709176).length < 2 ^ (prefixWord ++ tailWord_7709176).sum := by decide
  have hdescent : baseEnd_7709176 < baseStart_7709176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709197 : List Nat := [1, 7, 1, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_7709197 : Nat := 118140960795 + 7709197 * 2 ^ 59
def prefixEnd_7709197 : Nat := 4983230072969 + 3 ^ 40 * 7709197 * 2
def baseEnd_7709197 : Nat := 3958523521199379464983555

theorem tailTrace_7709197 : CollatzResearch.WordTrace tailWord_7709197 prefixEnd_7709197 3958523521199379464983555 := by
  unfold tailWord_7709197
  simp only [CollatzResearch.WordTrace]
  refine ⟨281177514251903369870757845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187451676167935579913838563 281177514251903369870757845)
  ·
    refine ⟨6590097990278985231345887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 281177514251903369870757845 6590097990278985231345887)
    ·
      refine ⟨9885146985418477847018831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6590097990278985231345887 9885146985418477847018831)
      ·
        refine ⟨14827720478127716770528247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9885146985418477847018831 14827720478127716770528247)
        ·
          refine ⟨22241580717191575155792371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14827720478127716770528247 22241580717191575155792371)
          ·
            refine ⟨33362371075787362733688557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22241580717191575155792371 33362371075787362733688557)
            ·
              refine ⟨12510889153420261025133209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33362371075787362733688557 12510889153420261025133209)
              ·
                refine ⟨9383166865065195768849907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12510889153420261025133209 9383166865065195768849907)
                ·
                  refine ⟨14074750297597793653274861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9383166865065195768849907 14074750297597793653274861)
                  ·
                    refine ⟨5278031361599172619978073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14074750297597793653274861 5278031361599172619978073)
                    ·
                      refine ⟨3958523521199379464983555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278031361599172619978073 3958523521199379464983555)
                      ·
                        rfl

theorem cell23_7709197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_7709197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709197 prefixEnd_7709197 := by exact prefixLift 7709197
  have htrace : WordTrace (prefixWord ++ tailWord_7709197) baseStart_7709197 baseEnd_7709197 := by
    simpa [prefixWord, tailWord_7709197, baseEnd_7709197] using wordTrace_append hprefix tailTrace_7709197
  have hstable : (prefixWord ++ tailWord_7709197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709197).length < 2 ^ (prefixWord ++ tailWord_7709197).sum := by decide
  have hdescent : baseEnd_7709197 < baseStart_7709197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709259 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 5, 4]
def baseStart_7709259 : Nat := 118140960795 + 7709259 * 2 ^ 59
def prefixEnd_7709259 : Nat := 4983230072969 + 3 ^ 40 * 7709259 * 2
def baseEnd_7709259 : Nat := 1319518452333319407469423

theorem tailTrace_7709259 : CollatzResearch.WordTrace tailWord_7709259 prefixEnd_7709259 1319518452333319407469423 := by
  unfold tailWord_7709259
  simp only [CollatzResearch.WordTrace]
  refine ⟨281179775577678754459514831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187453183718452502973009887 281179775577678754459514831)
  ·
    refine ⟨421769663366518131689272247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281179775577678754459514831 421769663366518131689272247)
    ·
      refine ⟨632654495049777197533908371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421769663366518131689272247 632654495049777197533908371)
      ·
        refine ⟨948981742574665796300862557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632654495049777197533908371 948981742574665796300862557)
        ·
          refine ⟨355868153465499673612823459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 948981742574665796300862557 355868153465499673612823459)
          ·
            refine ⟨533802230198249510419235189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355868153465499673612823459 533802230198249510419235189)
            ·
              refine ⟨50043959081085891601803299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 533802230198249510419235189 50043959081085891601803299)
              ·
                refine ⟨75065938621628837402704949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50043959081085891601803299 75065938621628837402704949)
                ·
                  refine ⟨7037431745777703506503589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75065938621628837402704949 7037431745777703506503589)
                  ·
                    refine ⟨1319518452333319407469423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7037431745777703506503589 1319518452333319407469423)
                    ·
                      rfl

theorem cell23_7709259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 4].length) (baseStart_7709259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709259 prefixEnd_7709259 := by exact prefixLift 7709259
  have htrace : WordTrace (prefixWord ++ tailWord_7709259) baseStart_7709259 baseEnd_7709259 := by
    simpa [prefixWord, tailWord_7709259, baseEnd_7709259] using wordTrace_append hprefix tailTrace_7709259
  have hstable : (prefixWord ++ tailWord_7709259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709259).length < 2 ^ (prefixWord ++ tailWord_7709259).sum := by decide
  have hdescent : baseEnd_7709259 < baseStart_7709259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709266 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_7709266 : Nat := 118140960795 + 7709266 * 2 ^ 59
def prefixEnd_7709266 : Nat := 4983230072969 + 3 ^ 40 * 7709266 * 2
def baseEnd_7709266 : Nat := 3958558951364539695020737

theorem tailTrace_7709266 : CollatzResearch.WordTrace tailWord_7709266 prefixEnd_7709266 3958558951364539695020737 := by
  unfold tailWord_7709266
  simp only [CollatzResearch.WordTrace]
  refine ⟨70295007722163348663754913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187453353925768929770013101 70295007722163348663754913)
  ·
    refine ⟨52721255791622511497816185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70295007722163348663754913 52721255791622511497816185)
    ·
      refine ⟨39540941843716883623362139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52721255791622511497816185 39540941843716883623362139)
      ·
        refine ⟨59311412765575325435043209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39540941843716883623362139 59311412765575325435043209)
        ·
          refine ⟨44483559574181494076282407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59311412765575325435043209 44483559574181494076282407)
          ·
            refine ⟨66725339361272241114423611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44483559574181494076282407 66725339361272241114423611)
            ·
              refine ⟨100088009041908361671635417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66725339361272241114423611 100088009041908361671635417)
              ·
                refine ⟨75066006781431271253726563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100088009041908361671635417 75066006781431271253726563)
                ·
                  refine ⟨112599010172146906880589845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75066006781431271253726563 112599010172146906880589845)
                  ·
                    refine ⟨5278078601819386260027649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112599010172146906880589845 5278078601819386260027649)
                    ·
                      refine ⟨3958558951364539695020737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278078601819386260027649 3958558951364539695020737)
                      ·
                        rfl

theorem cell23_7709266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_7709266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709266 prefixEnd_7709266 := by exact prefixLift 7709266
  have htrace : WordTrace (prefixWord ++ tailWord_7709266) baseStart_7709266 baseEnd_7709266 := by
    simpa [prefixWord, tailWord_7709266, baseEnd_7709266] using wordTrace_append hprefix tailTrace_7709266
  have hstable : (prefixWord ++ tailWord_7709266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709266).length < 2 ^ (prefixWord ++ tailWord_7709266).sum := by decide
  have hdescent : baseEnd_7709266 < baseStart_7709266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709278 : List Nat := [4, 4, 1, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_7709278 : Nat := 118140960795 + 7709278 * 2 ^ 59
def prefixEnd_7709278 : Nat := 4983230072969 + 3 ^ 40 * 7709278 * 2
def baseEnd_7709278 : Nat := 3958565113132393648070683

theorem tailTrace_7709278 : CollatzResearch.WordTrace tailWord_7709278 prefixEnd_7709278 3958565113132393648070683 := by
  unfold tailWord_7709278
  simp only [CollatzResearch.WordTrace]
  refine ⟨35147558570576240088057061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187453645709739947136304325 35147558570576240088057061)
  ·
    refine ⟨6590167231983045016510699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35147558570576240088057061 6590167231983045016510699)
    ·
      refine ⟨9885250847974567524766049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6590167231983045016510699 9885250847974567524766049)
      ·
        refine ⟨7413938135980925643574537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9885250847974567524766049 7413938135980925643574537)
        ·
          refine ⟨5560453601985694232680903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7413938135980925643574537 5560453601985694232680903)
          ·
            refine ⟨8340680402978541349021355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5560453601985694232680903 8340680402978541349021355)
            ·
              refine ⟨12511020604467812023532033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8340680402978541349021355 12511020604467812023532033)
              ·
                refine ⟨9383265453350859017649025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12511020604467812023532033 9383265453350859017649025)
                ·
                  refine ⟨7037449090013144263236769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9383265453350859017649025 7037449090013144263236769)
                  ·
                    refine ⟨5278086817509858197427577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7037449090013144263236769 5278086817509858197427577)
                    ·
                      refine ⟨3958565113132393648070683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278086817509858197427577 3958565113132393648070683)
                      ·
                        rfl

theorem cell23_7709278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_7709278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709278 prefixEnd_7709278 := by exact prefixLift 7709278
  have htrace : WordTrace (prefixWord ++ tailWord_7709278) baseStart_7709278 baseEnd_7709278 := by
    simpa [prefixWord, tailWord_7709278, baseEnd_7709278] using wordTrace_append hprefix tailTrace_7709278
  have hstable : (prefixWord ++ tailWord_7709278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709278).length < 2 ^ (prefixWord ++ tailWord_7709278).sum := by decide
  have hdescent : baseEnd_7709278 < baseStart_7709278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709293 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_7709293 : Nat := 118140960795 + 7709293 * 2 ^ 59
def prefixEnd_7709293 : Nat := 4983230072969 + 3 ^ 40 * 7709293 * 2
def baseEnd_7709293 : Nat := 1319524271780737029794371

theorem tailTrace_7709293 : CollatzResearch.WordTrace tailWord_7709293 prefixEnd_7709293 1319524271780737029794371 := by
  unfold tailWord_7709293
  simp only [CollatzResearch.WordTrace]
  refine ⟨281181015659555578266252533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187454010439703718844168355 281181015659555578266252533)
  ·
    refine ⟨26360720218083335462461175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281181015659555578266252533 26360720218083335462461175)
    ·
      refine ⟨39541080327125003193691763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26360720218083335462461175 39541080327125003193691763)
      ·
        refine ⟨59311620490687504790537645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39541080327125003193691763 59311620490687504790537645)
        ·
          refine ⟨22241857684007814296451617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59311620490687504790537645 22241857684007814296451617)
          ·
            refine ⟨16681393263005860722338713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22241857684007814296451617 16681393263005860722338713)
            ·
              refine ⟨12511044947254395541754035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16681393263005860722338713 12511044947254395541754035)
              ·
                refine ⟨18766567420881593312631053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12511044947254395541754035 18766567420881593312631053)
                ·
                  refine ⟨7037462782830597492236645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18766567420881593312631053 7037462782830597492236645)
                  ·
                    refine ⟨1319524271780737029794371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7037462782830597492236645 1319524271780737029794371)
                    ·
                      rfl

theorem cell23_7709293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_7709293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709293 prefixEnd_7709293 := by exact prefixLift 7709293
  have htrace : WordTrace (prefixWord ++ tailWord_7709293) baseStart_7709293 baseEnd_7709293 := by
    simpa [prefixWord, tailWord_7709293, baseEnd_7709293] using wordTrace_append hprefix tailTrace_7709293
  have hstable : (prefixWord ++ tailWord_7709293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709293).length < 2 ^ (prefixWord ++ tailWord_7709293).sum := by decide
  have hdescent : baseEnd_7709293 < baseStart_7709293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709336 : List Nat := [2, 1, 2, 4, 1, 1, 1, 5, 1, 5]
def baseStart_7709336 : Nat := 118140960795 + 7709336 * 2 ^ 59
def prefixEnd_7709336 : Nat := 4983230072969 + 3 ^ 40 * 7709336 * 2
def baseEnd_7709336 : Nat := 1319531631670118140381805

theorem tailTrace_7709336 : CollatzResearch.WordTrace tailWord_7709336 prefixEnd_7709336 1319531631670118140381805 := by
  unfold tailWord_7709336
  simp only [CollatzResearch.WordTrace]
  refine ⟨140591291999199898305033931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187455055998933197740045241 140591291999199898305033931)
  ·
    refine ⟨210886937998799847457550897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140591291999199898305033931 210886937998799847457550897)
    ·
      refine ⟨158165203499099885593163173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210886937998799847457550897 158165203499099885593163173)
      ·
        refine ⟨29655975656081228548718095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158165203499099885593163173 29655975656081228548718095)
        ·
          refine ⟨44483963484121842823077143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29655975656081228548718095 44483963484121842823077143)
          ·
            refine ⟨66725945226182764234615715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44483963484121842823077143 66725945226182764234615715)
            ·
              refine ⟨100088917839274146351923573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66725945226182764234615715 100088917839274146351923573)
              ·
                refine ⟨9383336047431951220492835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100088917839274146351923573 9383336047431951220492835)
                ·
                  refine ⟨14075004071147926830739253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9383336047431951220492835 14075004071147926830739253)
                  ·
                    refine ⟨1319531631670118140381805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14075004071147926830739253 1319531631670118140381805)
                    ·
                      rfl

theorem cell23_7709336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_7709336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709336 prefixEnd_7709336 := by exact prefixLift 7709336
  have htrace : WordTrace (prefixWord ++ tailWord_7709336) baseStart_7709336 baseEnd_7709336 := by
    simpa [prefixWord, tailWord_7709336, baseEnd_7709336] using wordTrace_append hprefix tailTrace_7709336
  have hstable : (prefixWord ++ tailWord_7709336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709336).length < 2 ^ (prefixWord ++ tailWord_7709336).sum := by decide
  have hdescent : baseEnd_7709336 < baseStart_7709336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709373 : List Nat := [1, 4, 1, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_7709373 : Nat := 118140960795 + 7709373 * 2 ^ 59
def prefixEnd_7709373 : Nat := 4983230072969 + 3 ^ 40 * 7709373 * 2
def baseEnd_7709373 : Nat := 3958613893794570776382745

theorem tailTrace_7709373 : CollatzResearch.WordTrace tailWord_7709373 prefixEnd_7709373 3958613893794570776382745 := by
  unfold tailWord_7709373
  simp only [CollatzResearch.WordTrace]
  refine ⟨281183933499265751929164773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187455955666177167952776515 281183933499265751929164773)
  ·
    refine ⟨52721987531112328486718395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281183933499265751929164773 52721987531112328486718395)
    ·
      refine ⟨79082981296668492730077593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52721987531112328486718395 79082981296668492730077593)
      ·
        refine ⟨59312235972501369547558195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79082981296668492730077593 59312235972501369547558195)
        ·
          refine ⟨88968353958752054321337293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59312235972501369547558195 88968353958752054321337293)
          ·
            refine ⟨33363132734532020370501485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88968353958752054321337293 33363132734532020370501485)
            ·
              refine ⟨12511174775449507638938057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33363132734532020370501485 12511174775449507638938057)
              ·
                refine ⟨9383381081587130729203543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12511174775449507638938057 9383381081587130729203543)
                ·
                  refine ⟨14075071622380696093805315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9383381081587130729203543 14075071622380696093805315)
                  ·
                    refine ⟨21112607433571044140707973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14075071622380696093805315 21112607433571044140707973)
                    ·
                      refine ⟨3958613893794570776382745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21112607433571044140707973 3958613893794570776382745)
                      ·
                        rfl

theorem cell23_7709373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_7709373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709373 prefixEnd_7709373 := by exact prefixLift 7709373
  have htrace : WordTrace (prefixWord ++ tailWord_7709373) baseStart_7709373 baseEnd_7709373 := by
    simpa [prefixWord, tailWord_7709373, baseEnd_7709373] using wordTrace_append hprefix tailTrace_7709373
  have hstable : (prefixWord ++ tailWord_7709373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709373).length < 2 ^ (prefixWord ++ tailWord_7709373).sum := by decide
  have hdescent : baseEnd_7709373 < baseStart_7709373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709386 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_7709386 : Nat := 118140960795 + 7709386 * 2 ^ 59
def prefixEnd_7709386 : Nat := 4983230072969 + 3 ^ 40 * 7709386 * 2
def baseEnd_7709386 : Nat := 3958620569043079225520185

theorem tailTrace_7709386 : CollatzResearch.WordTrace tailWord_7709386 prefixEnd_7709386 3958620569043079225520185 := by
  unfold tailWord_7709386
  simp only [CollatzResearch.WordTrace]
  refine ⟨70296101912054663787347003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187456271765479103432925341 70296101912054663787347003)
  ·
    refine ⟨105444152868081995681020505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70296101912054663787347003 105444152868081995681020505)
    ·
      refine ⟨79083114651061496760765379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105444152868081995681020505 79083114651061496760765379)
      ·
        refine ⟨118624671976592245141148069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79083114651061496760765379 118624671976592245141148069)
        ·
          refine ⟨22242125995611045963965263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118624671976592245141148069 22242125995611045963965263)
          ·
            refine ⟨33363188993416568945947895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22242125995611045963965263 33363188993416568945947895)
            ·
              refine ⟨50044783490124853418921843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33363188993416568945947895 50044783490124853418921843)
              ·
                refine ⟨75067175235187280128382765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50044783490124853418921843 75067175235187280128382765)
                ·
                  refine ⟨28150190713195230048143537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75067175235187280128382765 28150190713195230048143537)
                  ·
                    refine ⟨21112643034896422536107653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28150190713195230048143537 21112643034896422536107653)
                    ·
                      refine ⟨3958620569043079225520185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21112643034896422536107653 3958620569043079225520185)
                      ·
                        rfl

theorem cell23_7709386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_7709386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709386 prefixEnd_7709386 := by exact prefixLift 7709386
  have htrace : WordTrace (prefixWord ++ tailWord_7709386) baseStart_7709386 baseEnd_7709386 := by
    simpa [prefixWord, tailWord_7709386, baseEnd_7709386] using wordTrace_append hprefix tailTrace_7709386
  have hstable : (prefixWord ++ tailWord_7709386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709386).length < 2 ^ (prefixWord ++ tailWord_7709386).sum := by decide
  have hdescent : baseEnd_7709386 < baseStart_7709386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709390 : List Nat := [4, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4]
def baseStart_7709390 : Nat := 118140960795 + 7709390 * 2 ^ 59
def prefixEnd_7709390 : Nat := 4983230072969 + 3 ^ 40 * 7709390 * 2
def baseEnd_7709390 : Nat := 3958622622965697209870167

theorem tailTrace_7709390 : CollatzResearch.WordTrace tailWord_7709390 prefixEnd_7709390 3958622622965697209870167 := by
  unfold tailWord_7709390
  simp only [CollatzResearch.WordTrace]
  refine ⟨35148069192525520479066703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187456369026802775888355749 35148069192525520479066703)
  ·
    refine ⟨52722103788788280718600055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35148069192525520479066703 52722103788788280718600055)
    ·
      refine ⟨79083155683182421077900083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52722103788788280718600055 79083155683182421077900083)
      ·
        refine ⟨118624733524773631616850125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79083155683182421077900083 118624733524773631616850125)
        ·
          refine ⟨44484275071790111856318797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118624733524773631616850125 44484275071790111856318797)
          ·
            refine ⟨16681603151921291946119549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44484275071790111856318797 16681603151921291946119549)
            ·
              refine ⟨6255601181970484479794831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16681603151921291946119549 6255601181970484479794831)
              ·
                refine ⟨9383401772955726719692247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6255601181970484479794831 9383401772955726719692247)
                ·
                  refine ⟨14075102659433590079538371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9383401772955726719692247 14075102659433590079538371)
                  ·
                    refine ⟨21112653989150385119307557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14075102659433590079538371 21112653989150385119307557)
                    ·
                      refine ⟨3958622622965697209870167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21112653989150385119307557 3958622622965697209870167)
                      ·
                        rfl

theorem cell23_7709390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_7709390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709390 prefixEnd_7709390 := by exact prefixLift 7709390
  have htrace : WordTrace (prefixWord ++ tailWord_7709390) baseStart_7709390 baseEnd_7709390 := by
    simpa [prefixWord, tailWord_7709390, baseEnd_7709390] using wordTrace_append hprefix tailTrace_7709390
  have hstable : (prefixWord ++ tailWord_7709390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709390).length < 2 ^ (prefixWord ++ tailWord_7709390).sum := by decide
  have hdescent : baseEnd_7709390 < baseStart_7709390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709396 : List Nat := [2, 4, 1, 3, 2, 11]
def baseStart_7709396 : Nat := 118140960795 + 7709396 * 2 ^ 59
def prefixEnd_7709396 : Nat := 4983230072969 + 3 ^ 40 * 7709396 * 2
def baseEnd_7709396 : Nat := 16290640756582815581873

theorem tailTrace_7709396 : CollatzResearch.WordTrace tailWord_7709396 prefixEnd_7709396 16290640756582815581873 := by
  unfold tailWord_7709396
  simp only [CollatzResearch.WordTrace]
  refine ⟨140592386189091213428626021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187456514918788284571501361 140592386189091213428626021)
  ·
    refine ⟨26361072410454602517867379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140592386189091213428626021 26361072410454602517867379)
    ·
      refine ⟨39541608615681903776801069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26361072410454602517867379 39541608615681903776801069)
      ·
        refine ⟨14828103230880713916300401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39541608615681903776801069 14828103230880713916300401)
        ·
          refine ⟨11121077423160535437225301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14828103230880713916300401 11121077423160535437225301)
          ·
            refine ⟨16290640756582815581873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11121077423160535437225301 16290640756582815581873)
            ·
              rfl

theorem cell23_7709396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 11].length) (baseStart_7709396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709396 prefixEnd_7709396 := by exact prefixLift 7709396
  have htrace : WordTrace (prefixWord ++ tailWord_7709396) baseStart_7709396 baseEnd_7709396 := by
    simpa [prefixWord, tailWord_7709396, baseEnd_7709396] using wordTrace_append hprefix tailTrace_7709396
  have hstable : (prefixWord ++ tailWord_7709396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709396).length < 2 ^ (prefixWord ++ tailWord_7709396).sum := by decide
  have hdescent : baseEnd_7709396 < baseStart_7709396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709407 : List Nat := [1, 1, 2, 3, 2, 4, 1, 4, 1, 2, 2]
def baseStart_7709407 : Nat := 118140960795 + 7709407 * 2 ^ 59
def prefixEnd_7709407 : Nat := 4983230072969 + 3 ^ 40 * 7709407 * 2
def baseEnd_7709407 : Nat := 3958631352136823643357589

theorem tailTrace_7709407 : CollatzResearch.WordTrace tailWord_7709407 prefixEnd_7709407 3958631352136823643357589 := by
  unfold tailWord_7709407
  simp only [CollatzResearch.WordTrace]
  refine ⟨281185173581142575735902475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187456782387428383823934983 281185173581142575735902475)
  ·
    refine ⟨421777760371713863603853713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281185173581142575735902475 421777760371713863603853713)
    ·
      refine ⟨316333320278785397702890285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421777760371713863603853713 316333320278785397702890285)
      ·
        refine ⟨118624995104544524138583857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316333320278785397702890285 118624995104544524138583857)
        ·
          refine ⟨88968746328408393103937893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118624995104544524138583857 88968746328408393103937893)
          ·
            refine ⟨16681639936576573706988355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88968746328408393103937893 16681639936576573706988355)
            ·
              refine ⟨25022459904864860560482533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16681639936576573706988355 25022459904864860560482533)
              ·
                refine ⟨4691711232162161355090475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25022459904864860560482533 4691711232162161355090475)
                ·
                  refine ⟨7037566848243242032635713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4691711232162161355090475 7037566848243242032635713)
                  ·
                    refine ⟨5278175136182431524476785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7037566848243242032635713 5278175136182431524476785)
                    ·
                      refine ⟨3958631352136823643357589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278175136182431524476785 3958631352136823643357589)
                      ·
                        rfl

theorem cell23_7709407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_7709407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709407 prefixEnd_7709407 := by exact prefixLift 7709407
  have htrace : WordTrace (prefixWord ++ tailWord_7709407) baseStart_7709407 baseEnd_7709407 := by
    simpa [prefixWord, tailWord_7709407, baseEnd_7709407] using wordTrace_append hprefix tailTrace_7709407
  have hstable : (prefixWord ++ tailWord_7709407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709407).length < 2 ^ (prefixWord ++ tailWord_7709407).sum := by decide
  have hdescent : baseEnd_7709407 < baseStart_7709407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709419 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 5]
def baseStart_7709419 : Nat := 118140960795 + 7709419 * 2 ^ 59
def prefixEnd_7709419 : Nat := 4983230072969 + 3 ^ 40 * 7709419 * 2
def baseEnd_7709419 : Nat := 3958637513904677596407533

theorem tailTrace_7709419 : CollatzResearch.WordTrace tailWord_7709419 prefixEnd_7709419 3958637513904677596407533 := by
  unfold tailWord_7709419
  simp only [CollatzResearch.WordTrace]
  refine ⟨281185611257099101785339311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187457074171399401190226207 281185611257099101785339311)
  ·
    refine ⟨421778416885648652678008967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281185611257099101785339311 421778416885648652678008967)
    ·
      refine ⟨632667625328472979017013451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421778416885648652678008967 632667625328472979017013451)
      ·
        refine ⟨949001437992709468525520177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632667625328472979017013451 949001437992709468525520177)
        ·
          refine ⟨711751078494532101394140133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 949001437992709468525520177 711751078494532101394140133)
          ·
            refine ⟨133453327217724769011401275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 711751078494532101394140133 133453327217724769011401275)
            ·
              refine ⟨200179990826587153517101913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133453327217724769011401275 200179990826587153517101913)
              ·
                refine ⟨150134993119940365137826435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200179990826587153517101913 150134993119940365137826435)
                ·
                  refine ⟨225202489679910547706739653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150134993119940365137826435 225202489679910547706739653)
                  ·
                    refine ⟨42225466814983227695013685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 225202489679910547706739653 42225466814983227695013685)
                    ·
                      refine ⟨3958637513904677596407533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42225466814983227695013685 3958637513904677596407533)
                      ·
                        rfl

theorem cell23_7709419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 5].length) (baseStart_7709419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709419 prefixEnd_7709419 := by exact prefixLift 7709419
  have htrace : WordTrace (prefixWord ++ tailWord_7709419) baseStart_7709419 baseEnd_7709419 := by
    simpa [prefixWord, tailWord_7709419, baseEnd_7709419] using wordTrace_append hprefix tailTrace_7709419
  have hstable : (prefixWord ++ tailWord_7709419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709419).length < 2 ^ (prefixWord ++ tailWord_7709419).sum := by decide
  have hdescent : baseEnd_7709419 < baseStart_7709419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709423 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 3]
def baseStart_7709423 : Nat := 118140960795 + 7709423 * 2 ^ 59
def prefixEnd_7709423 : Nat := 4983230072969 + 3 ^ 40 * 7709423 * 2
def baseEnd_7709423 : Nat := 3958639567827295580757515

theorem tailTrace_7709423 : CollatzResearch.WordTrace tailWord_7709423 prefixEnd_7709423 3958639567827295580757515 := by
  unfold tailWord_7709423
  simp only [CollatzResearch.WordTrace]
  refine ⟨281185757149084610468484923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187457171432723073645656615 281185757149084610468484923)
  ·
    refine ⟨421778635723626915702727385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281185757149084610468484923 421778635723626915702727385)
    ·
      refine ⟨316333976792720186777045539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421778635723626915702727385 316333976792720186777045539)
      ·
        refine ⟨474500965189080280165568309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316333976792720186777045539 474500965189080280165568309)
        ·
          refine ⟨44484465486476276265522029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 474500965189080280165568309 44484465486476276265522029)
          ·
            refine ⟨16681674557428603599570761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44484465486476276265522029 16681674557428603599570761)
            ·
              refine ⟨12511255918071452699678071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16681674557428603599570761 12511255918071452699678071)
              ·
                refine ⟨18766883877107179049517107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12511255918071452699678071 18766883877107179049517107)
                ·
                  refine ⟨28150325815660768574275661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18766883877107179049517107 28150325815660768574275661)
                  ·
                    refine ⟨10556372180872788215353373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28150325815660768574275661 10556372180872788215353373)
                    ·
                      refine ⟨3958639567827295580757515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10556372180872788215353373 3958639567827295580757515)
                      ·
                        rfl

theorem cell23_7709423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 3].length) (baseStart_7709423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709423 prefixEnd_7709423 := by exact prefixLift 7709423
  have htrace : WordTrace (prefixWord ++ tailWord_7709423) baseStart_7709423 baseEnd_7709423 := by
    simpa [prefixWord, tailWord_7709423, baseEnd_7709423] using wordTrace_append hprefix tailTrace_7709423
  have hstable : (prefixWord ++ tailWord_7709423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709423).length < 2 ^ (prefixWord ++ tailWord_7709423).sum := by decide
  have hdescent : baseEnd_7709423 < baseStart_7709423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709439 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 3, 8]
def baseStart_7709439 : Nat := 118140960795 + 7709439 * 2 ^ 59
def prefixEnd_7709439 : Nat := 4983230072969 + 3 ^ 40 * 7709439 * 2
def baseEnd_7709439 : Nat := 1319549261172589172719147

theorem tailTrace_7709439 : CollatzResearch.WordTrace tailWord_7709439 prefixEnd_7709439 1319549261172589172719147 := by
  unfold tailWord_7709439
  simp only [CollatzResearch.WordTrace]
  refine ⟨281186340717026645201067371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187457560478017763467378247 281186340717026645201067371)
  ·
    refine ⟨421779511075539967801601057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281186340717026645201067371 421779511075539967801601057)
    ·
      refine ⟨316334633306654975851200793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421779511075539967801601057 316334633306654975851200793)
      ·
        refine ⟨237250974979991231888400595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316334633306654975851200793 237250974979991231888400595)
        ·
          refine ⟨355876462469986847832600893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237250974979991231888400595 355876462469986847832600893)
          ·
            refine ⟨133453673426245067937225335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355876462469986847832600893 133453673426245067937225335)
            ·
              refine ⟨200180510139367601905838003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133453673426245067937225335 200180510139367601905838003)
              ·
                refine ⟨300270765209051402858757005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200180510139367601905838003 300270765209051402858757005)
                ·
                  refine ⟨112601536953394276072033877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300270765209051402858757005 112601536953394276072033877)
                  ·
                    refine ⟨1319549261172589172719147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112601536953394276072033877 1319549261172589172719147)
                    ·
                      rfl

theorem cell23_7709439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_7709439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709439 prefixEnd_7709439 := by exact prefixLift 7709439
  have htrace : WordTrace (prefixWord ++ tailWord_7709439) baseStart_7709439 baseEnd_7709439 := by
    simpa [prefixWord, tailWord_7709439, baseEnd_7709439] using wordTrace_append hprefix tailTrace_7709439
  have hstable : (prefixWord ++ tailWord_7709439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709439).length < 2 ^ (prefixWord ++ tailWord_7709439).sum := by decide
  have hdescent : baseEnd_7709439 < baseStart_7709439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709450 : List Nat := [3, 1, 2, 2, 1, 2, 3, 3, 1, 3, 2]
def baseStart_7709450 : Nat := 118140960795 + 7709450 * 2 ^ 59
def prefixEnd_7709450 : Nat := 4983230072969 + 3 ^ 40 * 7709450 * 2
def baseEnd_7709450 : Nat := 3958653431804966975119891

theorem tailTrace_7709450 : CollatzResearch.WordTrace tailWord_7709450 prefixEnd_7709450 3958653431804966975119891 := by
  unfold tailWord_7709450
  simp only [CollatzResearch.WordTrace]
  refine ⟨70296685479996698519929451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187457827946657862719811869 70296685479996698519929451)
  ·
    refine ⟨105445028219995047779894177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70296685479996698519929451 105445028219995047779894177)
    ·
      refine ⟨79083771164996285834920633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105445028219995047779894177 79083771164996285834920633)
      ·
        refine ⟨59312828373747214376190475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79083771164996285834920633 59312828373747214376190475)
        ·
          refine ⟨88969242560620821564285713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59312828373747214376190475 88969242560620821564285713)
          ·
            refine ⟨66726931920465616173214285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88969242560620821564285713 66726931920465616173214285)
            ·
              refine ⟨25022599470174606064955357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66726931920465616173214285 25022599470174606064955357)
              ·
                refine ⟨9383474801315477274358259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25022599470174606064955357 9383474801315477274358259)
                ·
                  refine ⟨14075212201973215911537389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9383474801315477274358259 14075212201973215911537389)
                  ·
                    refine ⟨5278204575739955966826521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14075212201973215911537389 5278204575739955966826521)
                    ·
                      refine ⟨3958653431804966975119891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278204575739955966826521 3958653431804966975119891)
                      ·
                        rfl

theorem cell23_7709450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_7709450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709450 prefixEnd_7709450 := by exact prefixLift 7709450
  have htrace : WordTrace (prefixWord ++ tailWord_7709450) baseStart_7709450 baseEnd_7709450 := by
    simpa [prefixWord, tailWord_7709450, baseEnd_7709450] using wordTrace_append hprefix tailTrace_7709450
  have hstable : (prefixWord ++ tailWord_7709450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709450).length < 2 ^ (prefixWord ++ tailWord_7709450).sum := by decide
  have hdescent : baseEnd_7709450 < baseStart_7709450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709553 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_7709553 : Nat := 118140960795 + 7709553 * 2 ^ 59
def prefixEnd_7709553 : Nat := 4983230072969 + 3 ^ 40 * 7709553 * 2
def baseEnd_7709553 : Nat := 3958706320312380072131917

theorem tailTrace_7709553 : CollatzResearch.WordTrace tailWord_7709553 prefixEnd_7709553 3958706320312380072131917 := by
  unfold tailWord_7709553
  simp only [CollatzResearch.WordTrace]
  refine ⟨281190498638613642670717313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187460332425742428447144875 281190498638613642670717313)
  ·
    refine ⟨210892873978960232003037985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281190498638613642670717313 210892873978960232003037985)
    ·
      refine ⟨158169655484220174002278489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210892873978960232003037985 158169655484220174002278489)
      ·
        refine ⟨118627241613165130501708867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158169655484220174002278489 118627241613165130501708867)
        ·
          refine ⟨177940862419747695752563301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118627241613165130501708867 177940862419747695752563301)
          ·
            refine ⟨33363911703702692953605619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177940862419747695752563301 33363911703702692953605619)
            ·
              refine ⟨50045867555554039430408429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33363911703702692953605619 50045867555554039430408429)
              ·
                refine ⟨18767200333332764786403161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50045867555554039430408429 18767200333332764786403161)
                ·
                  refine ⟨14075400249999573589802371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18767200333332764786403161 14075400249999573589802371)
                  ·
                    refine ⟨21113100374999360384703557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14075400249999573589802371 21113100374999360384703557)
                    ·
                      refine ⟨3958706320312380072131917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21113100374999360384703557 3958706320312380072131917)
                      ·
                        rfl

theorem cell23_7709553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_7709553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709553 prefixEnd_7709553 := by exact prefixLift 7709553
  have htrace : WordTrace (prefixWord ++ tailWord_7709553) baseStart_7709553 baseEnd_7709553 := by
    simpa [prefixWord, tailWord_7709553, baseEnd_7709553] using wordTrace_append hprefix tailTrace_7709553
  have hstable : (prefixWord ++ tailWord_7709553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709553).length < 2 ^ (prefixWord ++ tailWord_7709553).sum := by decide
  have hdescent : baseEnd_7709553 < baseStart_7709553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709654 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_7709654 : Nat := 118140960795 + 7709654 * 2 ^ 59
def prefixEnd_7709654 : Nat := 4983230072969 + 3 ^ 40 * 7709654 * 2
def baseEnd_7709654 : Nat := 3958758181858484176968953

theorem tailTrace_7709654 : CollatzResearch.WordTrace tailWord_7709654 prefixEnd_7709654 3958758181858484176968953 := by
  unfold tailWord_7709654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17574636400702983557509001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187462788274165157946762677 17574636400702983557509001)
  ·
    refine ⟨13180977300527237668131751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17574636400702983557509001 13180977300527237668131751)
    ·
      refine ⟨19771465950790856502197627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13180977300527237668131751 19771465950790856502197627)
      ·
        refine ⟨29657198926186284753296441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19771465950790856502197627 29657198926186284753296441)
        ·
          refine ⟨22242899194639713564972331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29657198926186284753296441 22242899194639713564972331)
          ·
            refine ⟨33364348791959570347458497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22242899194639713564972331 33364348791959570347458497)
            ·
              refine ⟨25023261593969677760593873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33364348791959570347458497 25023261593969677760593873)
              ·
                refine ⟨18767446195477258320445405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25023261593969677760593873 18767446195477258320445405)
                ·
                  refine ⟨7037792323303971870167027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18767446195477258320445405 7037792323303971870167027)
                  ·
                    refine ⟨10556688484955957805250541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7037792323303971870167027 10556688484955957805250541)
                    ·
                      refine ⟨3958758181858484176968953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10556688484955957805250541 3958758181858484176968953)
                      ·
                        rfl

theorem cell23_7709654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_7709654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709654 prefixEnd_7709654 := by exact prefixLift 7709654
  have htrace : WordTrace (prefixWord ++ tailWord_7709654) baseStart_7709654 baseEnd_7709654 := by
    simpa [prefixWord, tailWord_7709654, baseEnd_7709654] using wordTrace_append hprefix tailTrace_7709654
  have hstable : (prefixWord ++ tailWord_7709654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709654).length < 2 ^ (prefixWord ++ tailWord_7709654).sum := by decide
  have hdescent : baseEnd_7709654 < baseStart_7709654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709671 : List Nat := [1, 1, 5, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_7709671 : Nat := 118140960795 + 7709671 * 2 ^ 59
def prefixEnd_7709671 : Nat := 4983230072969 + 3 ^ 40 * 7709671 * 2
def baseEnd_7709671 : Nat := 3958766911029610610456375

theorem tailTrace_7709671 : CollatzResearch.WordTrace tailWord_7709671 prefixEnd_7709671 3958766911029610610456375 := by
  unfold tailWord_7709671
  simp only [CollatzResearch.WordTrace]
  refine ⟨281194802452186148823512867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187463201634790765882341911 281194802452186148823512867)
  ·
    refine ⟨421792203678279223235269301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281194802452186148823512867 421792203678279223235269301)
    ·
      refine ⟨39543019094838677178306497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 421792203678279223235269301 39543019094838677178306497)
      ·
        refine ⟨29657264321129007883729873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39543019094838677178306497 29657264321129007883729873)
        ·
          refine ⟨22242948240846755912797405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29657264321129007883729873 22242948240846755912797405)
          ·
            refine ⟨8341105590317533467299027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22242948240846755912797405 8341105590317533467299027)
            ·
              refine ⟨12511658385476300200948541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8341105590317533467299027 12511658385476300200948541)
              ·
                refine ⟨4691871894553612575355703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12511658385476300200948541 4691871894553612575355703)
                ·
                  refine ⟨7037807841830418863033555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4691871894553612575355703 7037807841830418863033555)
                  ·
                    refine ⟨10556711762745628294550333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7037807841830418863033555 10556711762745628294550333)
                    ·
                      refine ⟨3958766911029610610456375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10556711762745628294550333 3958766911029610610456375)
                      ·
                        rfl

theorem cell23_7709671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_7709671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709671 prefixEnd_7709671 := by exact prefixLift 7709671
  have htrace : WordTrace (prefixWord ++ tailWord_7709671) baseStart_7709671 baseEnd_7709671 := by
    simpa [prefixWord, tailWord_7709671, baseEnd_7709671] using wordTrace_append hprefix tailTrace_7709671
  have hstable : (prefixWord ++ tailWord_7709671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709671).length < 2 ^ (prefixWord ++ tailWord_7709671).sum := by decide
  have hdescent : baseEnd_7709671 < baseStart_7709671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709703 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_7709703 : Nat := 118140960795 + 7709703 * 2 ^ 59
def prefixEnd_7709703 : Nat := 4983230072969 + 3 ^ 40 * 7709703 * 2
def baseEnd_7709703 : Nat := 3958783342410554485256227

theorem tailTrace_7709703 : CollatzResearch.WordTrace tailWord_7709703 prefixEnd_7709703 3958783342410554485256227 := by
  unfold tailWord_7709703
  simp only [CollatzResearch.WordTrace]
  refine ⟨281195969588070218288677763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187463979725380145525785175 281195969588070218288677763)
  ·
    refine ⟨421793954382105327433016645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281195969588070218288677763 421793954382105327433016645)
    ·
      refine ⟨79086366446644748893690621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421793954382105327433016645 79086366446644748893690621)
      ·
        refine ⟨29657387417491780835133983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79086366446644748893690621 29657387417491780835133983)
        ·
          refine ⟨44486081126237671252700975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29657387417491780835133983 44486081126237671252700975)
          ·
            refine ⟨66729121689356506879051463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44486081126237671252700975 66729121689356506879051463)
            ·
              refine ⟨100093682534034760318577195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66729121689356506879051463 100093682534034760318577195)
              ·
                refine ⟨150140523801052140477865793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100093682534034760318577195 150140523801052140477865793)
                ·
                  refine ⟨112605392850789105358399345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150140523801052140477865793 112605392850789105358399345)
                  ·
                    refine ⟨84454044638091829018799509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112605392850789105358399345 84454044638091829018799509)
                    ·
                      refine ⟨3958783342410554485256227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84454044638091829018799509 3958783342410554485256227)
                      ·
                        rfl

theorem cell23_7709703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_7709703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709703 prefixEnd_7709703 := by exact prefixLift 7709703
  have htrace : WordTrace (prefixWord ++ tailWord_7709703) baseStart_7709703 baseEnd_7709703 := by
    simpa [prefixWord, tailWord_7709703, baseEnd_7709703] using wordTrace_append hprefix tailTrace_7709703
  have hstable : (prefixWord ++ tailWord_7709703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709703).length < 2 ^ (prefixWord ++ tailWord_7709703).sum := by decide
  have hdescent : baseEnd_7709703 < baseStart_7709703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709704 : List Nat := [2, 1, 3, 2, 1, 5, 2, 1, 2, 4]
def baseStart_7709704 : Nat := 118140960795 + 7709704 * 2 ^ 59
def prefixEnd_7709704 : Nat := 4983230072969 + 3 ^ 40 * 7709704 * 2
def baseEnd_7709704 : Nat := 1319594618630402993781241

theorem tailTrace_7709704 : CollatzResearch.WordTrace tailWord_7709704 prefixEnd_7709704 1319594618630402993781241 := by
  unfold tailWord_7709704
  simp only [CollatzResearch.WordTrace]
  refine ⟨140598003030533297729732083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187464004040711063639642777 140598003030533297729732083)
  ·
    refine ⟨210897004545799946594598125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140598003030533297729732083 210897004545799946594598125)
    ·
      refine ⟨79086376704674979972974297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210897004545799946594598125 79086376704674979972974297)
      ·
        refine ⟨59314782528506234979730723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79086376704674979972974297 59314782528506234979730723)
        ·
          refine ⟨88972173792759352469596085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59314782528506234979730723 88972173792759352469596085)
          ·
            refine ⟨8341141293071189294024633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88972173792759352469596085 8341141293071189294024633)
            ·
              refine ⟨6255855969803391970518475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8341141293071189294024633 6255855969803391970518475)
              ·
                refine ⟨9383783954705087955777713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6255855969803391970518475 9383783954705087955777713)
                ·
                  refine ⟨7037837966028815966833285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9383783954705087955777713 7037837966028815966833285)
                  ·
                    refine ⟨1319594618630402993781241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7037837966028815966833285 1319594618630402993781241)
                    ·
                      rfl

theorem cell23_7709704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_7709704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709704 prefixEnd_7709704 := by exact prefixLift 7709704
  have htrace : WordTrace (prefixWord ++ tailWord_7709704) baseStart_7709704 baseEnd_7709704 := by
    simpa [prefixWord, tailWord_7709704, baseEnd_7709704] using wordTrace_append hprefix tailTrace_7709704
  have hstable : (prefixWord ++ tailWord_7709704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709704).length < 2 ^ (prefixWord ++ tailWord_7709704).sum := by decide
  have hdescent : baseEnd_7709704 < baseStart_7709704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709767 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 1, 4, 2]
def baseStart_7709767 : Nat := 118140960795 + 7709767 * 2 ^ 59
def prefixEnd_7709767 : Nat := 4983230072969 + 3 ^ 40 * 7709767 * 2
def baseEnd_7709767 : Nat := 3958816205172442234855933

theorem tailTrace_7709767 : CollatzResearch.WordTrace tailWord_7709767 prefixEnd_7709767 3958816205172442234855933 := by
  unfold tailWord_7709767
  simp only [CollatzResearch.WordTrace]
  refine ⟨281198303859838357219007555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187465535906558904812671703 281198303859838357219007555)
  ·
    refine ⟨421797455789757535828511333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281198303859838357219007555 421797455789757535828511333)
    ·
      refine ⟨79087022960579537967845875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421797455789757535828511333 79087022960579537967845875)
      ·
        refine ⟨118630534440869306951768813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79087022960579537967845875 118630534440869306951768813)
        ·
          refine ⟨44486450415325990106913305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118630534440869306951768813 44486450415325990106913305)
          ·
            refine ⟨33364837811494492580184979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44486450415325990106913305 33364837811494492580184979)
            ·
              refine ⟨50047256717241738870277469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33364837811494492580184979 50047256717241738870277469)
              ·
                refine ⟨18767721268965652076354051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50047256717241738870277469 18767721268965652076354051)
                ·
                  refine ⟨28151581903448478114531077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18767721268965652076354051 28151581903448478114531077)
                  ·
                    refine ⟨5278421606896589646474577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28151581903448478114531077 5278421606896589646474577)
                    ·
                      refine ⟨3958816205172442234855933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278421606896589646474577 3958816205172442234855933)
                      ·
                        rfl

theorem cell23_7709767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_7709767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709767 prefixEnd_7709767 := by exact prefixLift 7709767
  have htrace : WordTrace (prefixWord ++ tailWord_7709767) baseStart_7709767 baseEnd_7709767 := by
    simpa [prefixWord, tailWord_7709767, baseEnd_7709767] using wordTrace_append hprefix tailTrace_7709767
  have hstable : (prefixWord ++ tailWord_7709767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709767).length < 2 ^ (prefixWord ++ tailWord_7709767).sum := by decide
  have hdescent : baseEnd_7709767 < baseStart_7709767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709783 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_7709783 : Nat := 118140960795 + 7709783 * 2 ^ 59
def prefixEnd_7709783 : Nat := 4983230072969 + 3 ^ 40 * 7709783 * 2
def baseEnd_7709783 : Nat := 3958824420862914172255859

theorem tailTrace_7709783 : CollatzResearch.WordTrace tailWord_7709783 prefixEnd_7709783 3958824420862914172255859 := by
  unfold tailWord_7709783
  simp only [CollatzResearch.WordTrace]
  refine ⟨281198887427780391951590003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187465924951853594634393335 281198887427780391951590003)
  ·
    refine ⟨421798331141670587927385005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281198887427780391951590003 421798331141670587927385005)
    ·
      refine ⟨158174374178126470472769377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421798331141670587927385005 158174374178126470472769377)
      ·
        refine ⟨118630780633594852854577033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158174374178126470472769377 118630780633594852854577033)
        ·
          refine ⟨88973085475196139640932775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118630780633594852854577033 88973085475196139640932775)
          ·
            refine ⟨133459628212794209461399163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88973085475196139640932775 133459628212794209461399163)
            ·
              refine ⟨200189442319191314192098745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133459628212794209461399163 200189442319191314192098745)
              ·
                refine ⟨150142081739393485644074059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200189442319191314192098745 150142081739393485644074059)
                ·
                  refine ⟨225213122609090228466111089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150142081739393485644074059 225213122609090228466111089)
                  ·
                    refine ⟨168909841956817671349583317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225213122609090228466111089 168909841956817671349583317)
                    ·
                      refine ⟨3958824420862914172255859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168909841956817671349583317 3958824420862914172255859)
                      ·
                        rfl

theorem cell23_7709783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_7709783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709783 prefixEnd_7709783 := by exact prefixLift 7709783
  have htrace : WordTrace (prefixWord ++ tailWord_7709783) baseStart_7709783 baseEnd_7709783 := by
    simpa [prefixWord, tailWord_7709783, baseEnd_7709783] using wordTrace_append hprefix tailTrace_7709783
  have hstable : (prefixWord ++ tailWord_7709783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709783).length < 2 ^ (prefixWord ++ tailWord_7709783).sum := by decide
  have hdescent : baseEnd_7709783 < baseStart_7709783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709801 : List Nat := [1, 2, 1, 1, 1, 8, 1, 2, 2, 2, 2]
def baseStart_7709801 : Nat := 118140960795 + 7709801 * 2 ^ 59
def prefixEnd_7709801 : Nat := 4983230072969 + 3 ^ 40 * 7709801 * 2
def baseEnd_7709801 : Nat := 3958833663514695101830777

theorem tailTrace_7709801 : CollatzResearch.WordTrace tailWord_7709801 prefixEnd_7709801 3958833663514695101830777 := by
  unfold tailWord_7709801
  simp only [CollatzResearch.WordTrace]
  refine ⟨281199543941715181025745257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187466362627810120683830171 281199543941715181025745257)
  ·
    refine ⟨210899657956286385769308943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281199543941715181025745257 210899657956286385769308943)
    ·
      refine ⟨316349486934429578653963415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210899657956286385769308943 316349486934429578653963415)
      ·
        refine ⟨474524230401644367980945123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316349486934429578653963415 474524230401644367980945123)
        ·
          refine ⟨711786345602466551971417685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474524230401644367980945123 711786345602466551971417685)
          ·
            refine ⟨8341246237528904905915051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 711786345602466551971417685 8341246237528904905915051)
            ·
              refine ⟨12511869356293357358872577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8341246237528904905915051 12511869356293357358872577)
              ·
                refine ⟨9383902017220018019154433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12511869356293357358872577 9383902017220018019154433)
                ·
                  refine ⟨7037926512915013514365825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9383902017220018019154433 7037926512915013514365825)
                  ·
                    refine ⟨5278444884686260135774369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7037926512915013514365825 5278444884686260135774369)
                    ·
                      refine ⟨3958833663514695101830777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278444884686260135774369 3958833663514695101830777)
                      ·
                        rfl

theorem cell23_7709801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 2, 2].length) (baseStart_7709801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709801 prefixEnd_7709801 := by exact prefixLift 7709801
  have htrace : WordTrace (prefixWord ++ tailWord_7709801) baseStart_7709801 baseEnd_7709801 := by
    simpa [prefixWord, tailWord_7709801, baseEnd_7709801] using wordTrace_append hprefix tailTrace_7709801
  have hstable : (prefixWord ++ tailWord_7709801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709801).length < 2 ^ (prefixWord ++ tailWord_7709801).sum := by decide
  have hdescent : baseEnd_7709801 < baseStart_7709801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709854 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_7709854 : Nat := 118140960795 + 7709854 * 2 ^ 59
def prefixEnd_7709854 : Nat := 4983230072969 + 3 ^ 40 * 7709854 * 2
def baseEnd_7709854 : Nat := 1319620292663127798156011

theorem tailTrace_7709854 : CollatzResearch.WordTrace tailWord_7709854 prefixEnd_7709854 1319620292663127798156011 := by
  unfold tailWord_7709854
  simp only [CollatzResearch.WordTrace]
  refine ⟨35150184626315396384678077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187467651340348780718283077 35150184626315396384678077)
  ·
    refine ⟨13181319234868273644254279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35150184626315396384678077 13181319234868273644254279)
    ·
      refine ⟨19771978852302410466381419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13181319234868273644254279 19771978852302410466381419)
      ·
        refine ⟨29657968278453615699572129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19771978852302410466381419 29657968278453615699572129)
        ·
          refine ⟨22243476208840211774679097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29657968278453615699572129 22243476208840211774679097)
          ·
            refine ⟨16682607156630158831009323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22243476208840211774679097 16682607156630158831009323)
            ·
              refine ⟨25023910734945238246513985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16682607156630158831009323 25023910734945238246513985)
              ·
                refine ⟨18767933051208928684885489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25023910734945238246513985 18767933051208928684885489)
                ·
                  refine ⟨14075949788406696513664117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18767933051208928684885489 14075949788406696513664117)
                  ·
                    refine ⟨1319620292663127798156011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14075949788406696513664117 1319620292663127798156011)
                    ·
                      rfl

theorem cell23_7709854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_7709854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709854 prefixEnd_7709854 := by exact prefixLift 7709854
  have htrace : WordTrace (prefixWord ++ tailWord_7709854) baseStart_7709854 baseEnd_7709854 := by
    simpa [prefixWord, tailWord_7709854, baseEnd_7709854] using wordTrace_append hprefix tailTrace_7709854
  have hstable : (prefixWord ++ tailWord_7709854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709854).length < 2 ^ (prefixWord ++ tailWord_7709854).sum := by decide
  have hdescent : baseEnd_7709854 < baseStart_7709854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709857 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7709857 : Nat := 118140960795 + 7709857 * 2 ^ 59
def prefixEnd_7709857 : Nat := 4983230072969 + 3 ^ 40 * 7709857 * 2
def baseEnd_7709857 : Nat := 3958862418431346882730519

theorem tailTrace_7709857 : CollatzResearch.WordTrace tailWord_7709857 prefixEnd_7709857 3958862418431346882730519 := by
  unfold tailWord_7709857
  simp only [CollatzResearch.WordTrace]
  refine ⟨281201586429512302589783825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187467724286341535059855883 281201586429512302589783825)
  ·
    refine ⟨210901189822134226942337869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281201586429512302589783825 210901189822134226942337869)
    ·
      refine ⟨79087946183300335103376701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210901189822134226942337869 79087946183300335103376701)
      ·
        refine ⟨29657979818737625663766263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79087946183300335103376701 29657979818737625663766263)
        ·
          refine ⟨44486969728106438495649395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29657979818737625663766263 44486969728106438495649395)
          ·
            refine ⟨66730454592159657743474093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44486969728106438495649395 66730454592159657743474093)
            ·
              refine ⟨25023920472059871653802785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66730454592159657743474093 25023920472059871653802785)
              ·
                refine ⟨18767940354044903740352089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25023920472059871653802785 18767940354044903740352089)
                ·
                  refine ⟨14075955265533677805264067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18767940354044903740352089 14075955265533677805264067)
                  ·
                    refine ⟨21113932898300516707896101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14075955265533677805264067 21113932898300516707896101)
                    ·
                      refine ⟨3958862418431346882730519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21113932898300516707896101 3958862418431346882730519)
                      ·
                        rfl

theorem cell23_7709857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7709857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709857 prefixEnd_7709857 := by exact prefixLift 7709857
  have htrace : WordTrace (prefixWord ++ tailWord_7709857) baseStart_7709857 baseEnd_7709857 := by
    simpa [prefixWord, tailWord_7709857, baseEnd_7709857] using wordTrace_append hprefix tailTrace_7709857
  have hstable : (prefixWord ++ tailWord_7709857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709857).length < 2 ^ (prefixWord ++ tailWord_7709857).sum := by decide
  have hdescent : baseEnd_7709857 < baseStart_7709857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709907 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 5, 1, 3]
def baseStart_7709907 : Nat := 118140960795 + 7709907 * 2 ^ 59
def prefixEnd_7709907 : Nat := 4983230072969 + 3 ^ 40 * 7709907 * 2
def baseEnd_7709907 : Nat := 3958888092464071687105289

theorem tailTrace_7709907 : CollatzResearch.WordTrace tailWord_7709907 prefixEnd_7709907 3958888092464071687105289 := by
  unfold tailWord_7709907
  simp only [CollatzResearch.WordTrace]
  refine ⟨281203410079331161129103975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187468940052887440752735983 281203410079331161129103975)
  ·
    refine ⟨421805115118996741693655963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281203410079331161129103975 421805115118996741693655963)
    ·
      refine ⟨632707672678495112540483945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421805115118996741693655963 632707672678495112540483945)
      ·
        refine ⟨474530754508871334405362959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632707672678495112540483945 474530754508871334405362959)
        ·
          refine ⟨711796131763307001608044439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474530754508871334405362959 711796131763307001608044439)
          ·
            refine ⟨1067694197644960502412066659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711796131763307001608044439 1067694197644960502412066659)
            ·
              refine ⟨1601541296467440753618099989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067694197644960502412066659 1601541296467440753618099989)
              ·
                refine ⟨75072248271911285325848437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1601541296467440753618099989 75072248271911285325848437)
                ·
                  refine ⟨7038023275491682999298291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75072248271911285325848437 7038023275491682999298291)
                  ·
                    refine ⟨10557034913237524498947437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7038023275491682999298291 10557034913237524498947437)
                    ·
                      refine ⟨3958888092464071687105289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10557034913237524498947437 3958888092464071687105289)
                      ·
                        rfl

theorem cell23_7709907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 1, 3].length) (baseStart_7709907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709907 prefixEnd_7709907 := by exact prefixLift 7709907
  have htrace : WordTrace (prefixWord ++ tailWord_7709907) baseStart_7709907 baseEnd_7709907 := by
    simpa [prefixWord, tailWord_7709907, baseEnd_7709907] using wordTrace_append hprefix tailTrace_7709907
  have hstable : (prefixWord ++ tailWord_7709907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709907).length < 2 ^ (prefixWord ++ tailWord_7709907).sum := by decide
  have hdescent : baseEnd_7709907 < baseStart_7709907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709934 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_7709934 : Nat := 118140960795 + 7709934 * 2 ^ 59
def prefixEnd_7709934 : Nat := 4983230072969 + 3 ^ 40 * 7709934 * 2
def baseEnd_7709934 : Nat := 3958901956441743081467665

theorem tailTrace_7709934 : CollatzResearch.WordTrace tailWord_7709934 prefixEnd_7709934 3958901956441743081467665 := by
  unfold tailWord_7709934
  simp only [CollatzResearch.WordTrace]
  refine ⟨35150549356279168092542107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187469596566822229826891237 35150549356279168092542107)
  ·
    refine ⟨52725824034418752138813161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35150549356279168092542107 52725824034418752138813161)
    ·
      refine ⟨39544368025814064104109871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52725824034418752138813161 39544368025814064104109871)
      ·
        refine ⟨59316552038721096156164807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39544368025814064104109871 59316552038721096156164807)
        ·
          refine ⟨88974828058081644234247211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59316552038721096156164807 88974828058081644234247211)
          ·
            refine ⟨133462242087122466351370817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88974828058081644234247211 133462242087122466351370817)
            ·
              refine ⟨100096681565341849763528113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133462242087122466351370817 100096681565341849763528113)
              ·
                refine ⟨75072511174006387322646085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100096681565341849763528113 75072511174006387322646085)
                ·
                  refine ⟨14076095845126197622996141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75072511174006387322646085 14076095845126197622996141)
                  ·
                    refine ⟨5278535941922324108623553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14076095845126197622996141 5278535941922324108623553)
                    ·
                      refine ⟨3958901956441743081467665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278535941922324108623553 3958901956441743081467665)
                      ·
                        rfl

theorem cell23_7709934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_7709934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709934 prefixEnd_7709934 := by exact prefixLift 7709934
  have htrace : WordTrace (prefixWord ++ tailWord_7709934) baseStart_7709934 baseEnd_7709934 := by
    simpa [prefixWord, tailWord_7709934, baseEnd_7709934] using wordTrace_append hprefix tailTrace_7709934
  have hstable : (prefixWord ++ tailWord_7709934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709934).length < 2 ^ (prefixWord ++ tailWord_7709934).sum := by decide
  have hdescent : baseEnd_7709934 < baseStart_7709934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709951 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 2, 3, 2]
def baseStart_7709951 : Nat := 118140960795 + 7709951 * 2 ^ 59
def prefixEnd_7709951 : Nat := 4983230072969 + 3 ^ 40 * 7709951 * 2
def baseEnd_7709951 : Nat := 3958910685612869514955087

theorem tailTrace_7709951 : CollatzResearch.WordTrace tailWord_7709951 prefixEnd_7709951 3958910685612869514955087 := by
  unfold tailWord_7709951
  simp only [CollatzResearch.WordTrace]
  refine ⟨281205014891171756643705707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187470009927447837762470471 281205014891171756643705707)
  ·
    refine ⟨421807522336757634965558561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281205014891171756643705707 421807522336757634965558561)
    ·
      refine ⟨316355641752568226224168921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421807522336757634965558561 316355641752568226224168921)
      ·
        refine ⟨237266731314426169668126691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316355641752568226224168921 237266731314426169668126691)
        ·
          refine ⟨355900096971639254502190037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237266731314426169668126691 355900096971639254502190037)
          ·
            refine ⟨8341408522772795027395079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 355900096971639254502190037 8341408522772795027395079)
            ·
              refine ⟨12512112784159192541092619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8341408522772795027395079 12512112784159192541092619)
              ·
                refine ⟨18768169176238788811638929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12512112784159192541092619 18768169176238788811638929)
                ·
                  refine ⟨14076126882179091608729197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18768169176238788811638929 14076126882179091608729197)
                  ·
                    refine ⟨5278547580817159353273449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14076126882179091608729197 5278547580817159353273449)
                    ·
                      refine ⟨3958910685612869514955087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278547580817159353273449 3958910685612869514955087)
                      ·
                        rfl

theorem cell23_7709951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 3, 2].length) (baseStart_7709951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709951 prefixEnd_7709951 := by exact prefixLift 7709951
  have htrace : WordTrace (prefixWord ++ tailWord_7709951) baseStart_7709951 baseEnd_7709951 := by
    simpa [prefixWord, tailWord_7709951, baseEnd_7709951] using wordTrace_append hprefix tailTrace_7709951
  have hstable : (prefixWord ++ tailWord_7709951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709951).length < 2 ^ (prefixWord ++ tailWord_7709951).sum := by decide
  have hdescent : baseEnd_7709951 < baseStart_7709951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709957 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 4, 4]
def baseStart_7709957 : Nat := 118140960795 + 7709957 * 2 ^ 59
def prefixEnd_7709957 : Nat := 4983230072969 + 3 ^ 40 * 7709957 * 2
def baseEnd_7709957 : Nat := 1319637922165598830493353

theorem tailTrace_7709957 : CollatzResearch.WordTrace tailWord_7709957 prefixEnd_7709957 1319637922165598830493353 := by
  unfold tailWord_7709957
  simp only [CollatzResearch.WordTrace]
  refine ⟨281205233729150019668424125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187470155819433346445616083 281205233729150019668424125)
  ·
    refine ⟨105451962648431257375659047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281205233729150019668424125 105451962648431257375659047)
    ·
      refine ⟨158177943972646886063488571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105451962648431257375659047 158177943972646886063488571)
      ·
        refine ⟨237266915958970329095232857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158177943972646886063488571 237266915958970329095232857)
        ·
          refine ⟨177950186969227746821424643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237266915958970329095232857 177950186969227746821424643)
          ·
            refine ⟨266925280453841620232136965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177950186969227746821424643 266925280453841620232136965)
            ·
              refine ⟨50048490085095303793525681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266925280453841620232136965 50048490085095303793525681)
              ·
                refine ⟨37536367563821477845144261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50048490085095303793525681 37536367563821477845144261)
                ·
                  refine ⟨7038068918216527095964549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37536367563821477845144261 7038068918216527095964549)
                  ·
                    refine ⟨1319637922165598830493353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7038068918216527095964549 1319637922165598830493353)
                    ·
                      rfl

theorem cell23_7709957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_7709957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709957 prefixEnd_7709957 := by exact prefixLift 7709957
  have htrace : WordTrace (prefixWord ++ tailWord_7709957) baseStart_7709957 baseEnd_7709957 := by
    simpa [prefixWord, tailWord_7709957, baseEnd_7709957] using wordTrace_append hprefix tailTrace_7709957
  have hstable : (prefixWord ++ tailWord_7709957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709957).length < 2 ^ (prefixWord ++ tailWord_7709957).sum := by decide
  have hdescent : baseEnd_7709957 < baseStart_7709957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709964 : List Nat := [2, 2, 1, 2, 2, 4, 1, 3, 1, 1, 4]
def baseStart_7709964 : Nat := 118140960795 + 7709964 * 2 ^ 59
def prefixEnd_7709964 : Nat := 4983230072969 + 3 ^ 40 * 7709964 * 2
def baseEnd_7709964 : Nat := 3958917360861377964092527

theorem tailTrace_7709964 : CollatzResearch.WordTrace tailWord_7709964 prefixEnd_7709964 3958917360861377964092527 := by
  unfold tailWord_7709964
  simp only [CollatzResearch.WordTrace]
  refine ⟨140602744520062329931964473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187470326026749773242619297 140602744520062329931964473)
  ·
    refine ⟨105452058390046747448973355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140602744520062329931964473 105452058390046747448973355)
    ·
      refine ⟨158178087585070121173460033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105452058390046747448973355 158178087585070121173460033)
      ·
        refine ⟨118633565688802590880095025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158178087585070121173460033 118633565688802590880095025)
        ·
          refine ⟨88975174266601943160071269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118633565688802590880095025 88975174266601943160071269)
          ·
            refine ⟨16682845174987864342513363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88975174266601943160071269 16682845174987864342513363)
            ·
              refine ⟨25024267762481796513770045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16682845174987864342513363 25024267762481796513770045)
              ·
                refine ⟨9384100410930673692663767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25024267762481796513770045 9384100410930673692663767)
                ·
                  refine ⟨14076150616396010538995651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9384100410930673692663767 14076150616396010538995651)
                  ·
                    refine ⟨21114225924594015808493477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14076150616396010538995651 21114225924594015808493477)
                    ·
                      refine ⟨3958917360861377964092527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21114225924594015808493477 3958917360861377964092527)
                      ·
                        rfl

theorem cell23_7709964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_7709964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709964 prefixEnd_7709964 := by exact prefixLift 7709964
  have htrace : WordTrace (prefixWord ++ tailWord_7709964) baseStart_7709964 baseEnd_7709964 := by
    simpa [prefixWord, tailWord_7709964, baseEnd_7709964] using wordTrace_append hprefix tailTrace_7709964
  have hstable : (prefixWord ++ tailWord_7709964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709964).length < 2 ^ (prefixWord ++ tailWord_7709964).sum := by decide
  have hdescent : baseEnd_7709964 < baseStart_7709964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709984 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 5]
def baseStart_7709984 : Nat := 118140960795 + 7709984 * 2 ^ 59
def prefixEnd_7709984 : Nat := 4983230072969 + 3 ^ 40 * 7709984 * 2
def baseEnd_7709984 : Nat := 3958927630474467885842435

theorem tailTrace_7709984 : CollatzResearch.WordTrace tailWord_7709984 prefixEnd_7709984 3958927630474467885842435 := by
  unfold tailWord_7709984
  simp only [CollatzResearch.WordTrace]
  refine ⟨140603109250026101639828503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187470812333368135519771337 140603109250026101639828503)
  ·
    refine ⟨210904663875039152459742755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140603109250026101639828503 210904663875039152459742755)
    ·
      refine ⟨316356995812558728689614133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210904663875039152459742755 316356995812558728689614133)
      ·
        refine ⟨29658468357427380814651325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 316356995812558728689614133 29658468357427380814651325)
        ·
          refine ⟨11121925634035267805494247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29658468357427380814651325 11121925634035267805494247)
          ·
            refine ⟨16682888451052901708241371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11121925634035267805494247 16682888451052901708241371)
            ·
              refine ⟨25024332676579352562362057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16682888451052901708241371 25024332676579352562362057)
              ·
                refine ⟨18768249507434514421771543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25024332676579352562362057 18768249507434514421771543)
                ·
                  refine ⟨28152374261151771632657315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18768249507434514421771543 28152374261151771632657315)
                  ·
                    refine ⟨42228561391727657448985973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28152374261151771632657315 42228561391727657448985973)
                    ·
                      refine ⟨3958927630474467885842435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42228561391727657448985973 3958927630474467885842435)
                      ·
                        rfl

theorem cell23_7709984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_7709984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709984 prefixEnd_7709984 := by exact prefixLift 7709984
  have htrace : WordTrace (prefixWord ++ tailWord_7709984) baseStart_7709984 baseEnd_7709984 := by
    simpa [prefixWord, tailWord_7709984, baseEnd_7709984] using wordTrace_append hprefix tailTrace_7709984
  have hstable : (prefixWord ++ tailWord_7709984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709984).length < 2 ^ (prefixWord ++ tailWord_7709984).sum := by decide
  have hdescent : baseEnd_7709984 < baseStart_7709984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7709994 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_7709994 : Nat := 118140960795 + 7709994 * 2 ^ 59
def prefixEnd_7709994 : Nat := 4983230072969 + 3 ^ 40 * 7709994 * 2
def baseEnd_7709994 : Nat := 3958932765281012846717389

theorem tailTrace_7709994 : CollatzResearch.WordTrace tailWord_7709994 prefixEnd_7709994 3958932765281012846717389 := by
  unfold tailWord_7709994
  simp only [CollatzResearch.WordTrace]
  refine ⟨70301645807503993746880259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187471055486677316658347357 70301645807503993746880259)
  ·
    refine ⟨105452468711255990620320389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70301645807503993746880259 105452468711255990620320389)
    ·
      refine ⟨19772337883360498241310073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105452468711255990620320389 19772337883360498241310073)
      ·
        refine ⟨14829253412520373680982555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19772337883360498241310073 14829253412520373680982555)
        ·
          refine ⟨22243880118780560521473833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14829253412520373680982555 22243880118780560521473833)
          ·
            refine ⟨16682910089085420391105375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22243880118780560521473833 16682910089085420391105375)
            ·
              refine ⟨25024365133628130586658063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16682910089085420391105375 25024365133628130586658063)
              ·
                refine ⟨37536547700442195879987095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25024365133628130586658063 37536547700442195879987095)
                ·
                  refine ⟨56304821550663293819980643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37536547700442195879987095 56304821550663293819980643)
                  ·
                    refine ⟨84457232325994940729970965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56304821550663293819980643 84457232325994940729970965)
                    ·
                      refine ⟨3958932765281012846717389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84457232325994940729970965 3958932765281012846717389)
                      ·
                        rfl

theorem cell23_7709994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_7709994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7709994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7709994 prefixEnd_7709994 := by exact prefixLift 7709994
  have htrace : WordTrace (prefixWord ++ tailWord_7709994) baseStart_7709994 baseEnd_7709994 := by
    simpa [prefixWord, tailWord_7709994, baseEnd_7709994] using wordTrace_append hprefix tailTrace_7709994
  have hstable : (prefixWord ++ tailWord_7709994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7709994).length < 2 ^ (prefixWord ++ tailWord_7709994).sum := by decide
  have hdescent : baseEnd_7709994 < baseStart_7709994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7709994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710001 : List Nat := [1, 2, 2, 3, 3, 2, 2, 2, 1, 2, 3]
def baseStart_7710001 : Nat := 118140960795 + 7710001 * 2 ^ 59
def prefixEnd_7710001 : Nat := 4983230072969 + 3 ^ 40 * 7710001 * 2
def baseEnd_7710001 : Nat := 3958936359645594319329857

theorem tailTrace_7710001 : CollatzResearch.WordTrace tailWord_7710001 prefixEnd_7710001 3958936359645594319329857 := by
  unfold tailWord_7710001
  simp only [CollatzResearch.WordTrace]
  refine ⟨281206838540990615183025857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187471225693993743455350571 281206838540990615183025857)
  ·
    refine ⟨210905128905742961387269393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281206838540990615183025857 210905128905742961387269393)
    ·
      refine ⟨158178846679307221040452045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210905128905742961387269393 158178846679307221040452045)
      ·
        refine ⟨59317067504740207890169517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158178846679307221040452045 59317067504740207890169517)
        ·
          refine ⟨22243900314277577958813569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59317067504740207890169517 22243900314277577958813569)
          ·
            refine ⟨16682925235708183469110177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22243900314277577958813569 16682925235708183469110177)
            ·
              refine ⟨12512193926781137601832633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16682925235708183469110177 12512193926781137601832633)
              ·
                refine ⟨9384145445085853201374475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12512193926781137601832633 9384145445085853201374475)
                ·
                  refine ⟨14076218167628779802061713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9384145445085853201374475 14076218167628779802061713)
                  ·
                    refine ⟨10557163625721584851546285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14076218167628779802061713 10557163625721584851546285)
                    ·
                      refine ⟨3958936359645594319329857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10557163625721584851546285 3958936359645594319329857)
                      ·
                        rfl

theorem cell23_7710001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_7710001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710001 prefixEnd_7710001 := by exact prefixLift 7710001
  have htrace : WordTrace (prefixWord ++ tailWord_7710001) baseStart_7710001 baseEnd_7710001 := by
    simpa [prefixWord, tailWord_7710001, baseEnd_7710001] using wordTrace_append hprefix tailTrace_7710001
  have hstable : (prefixWord ++ tailWord_7710001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710001).length < 2 ^ (prefixWord ++ tailWord_7710001).sum := by decide
  have hdescent : baseEnd_7710001 < baseStart_7710001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710014 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_7710014 : Nat := 118140960795 + 7710014 * 2 ^ 59
def prefixEnd_7710014 : Nat := 4983230072969 + 3 ^ 40 * 7710014 * 2
def baseEnd_7710014 : Nat := 3958943034894102768467297

theorem tailTrace_7710014 : CollatzResearch.WordTrace tailWord_7710014 prefixEnd_7710014 3958943034894102768467297 := by
  unfold tailWord_7710014
  simp only [CollatzResearch.WordTrace]
  refine ⟨35150914086242939800406137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187471541793295678935499397 35150914086242939800406137)
  ·
    refine ⟨26363185564682204850304603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35150914086242939800406137 26363185564682204850304603)
    ·
      refine ⟨39544778347023307275456905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26363185564682204850304603 39544778347023307275456905)
      ·
        refine ⟨29658583760267480456592679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39544778347023307275456905 29658583760267480456592679)
        ·
          refine ⟨44487875640401220684889019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29658583760267480456592679 44487875640401220684889019)
          ·
            refine ⟨66731813460601831027333529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44487875640401220684889019 66731813460601831027333529)
            ·
              refine ⟨50048860095451373270500147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66731813460601831027333529 50048860095451373270500147)
              ·
                refine ⟨75073290143177059905750221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50048860095451373270500147 75073290143177059905750221)
                ·
                  refine ⟨28152483803691397464656333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75073290143177059905750221 28152483803691397464656333)
                  ·
                    refine ⟨10557181426384274049246125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28152483803691397464656333 10557181426384274049246125)
                    ·
                      refine ⟨3958943034894102768467297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10557181426384274049246125 3958943034894102768467297)
                      ·
                        rfl

theorem cell23_7710014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_7710014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710014 prefixEnd_7710014 := by exact prefixLift 7710014
  have htrace : WordTrace (prefixWord ++ tailWord_7710014) baseStart_7710014 baseEnd_7710014 := by
    simpa [prefixWord, tailWord_7710014, baseEnd_7710014] using wordTrace_append hprefix tailTrace_7710014
  have hstable : (prefixWord ++ tailWord_7710014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710014).length < 2 ^ (prefixWord ++ tailWord_7710014).sum := by decide
  have hdescent : baseEnd_7710014 < baseStart_7710014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710015 : List Nat := [1, 1, 2, 2, 4, 4, 1, 3, 1, 2, 2]
def baseStart_7710015 : Nat := 118140960795 + 7710015 * 2 ^ 59
def prefixEnd_7710015 : Nat := 4983230072969 + 3 ^ 40 * 7710015 * 2
def baseEnd_7710015 : Nat := 3958943548374757264554793

theorem tailTrace_7710015 : CollatzResearch.WordTrace tailWord_7710015 prefixEnd_7710015 3958943548374757264554793 := by
  unfold tailWord_7710015
  simp only [CollatzResearch.WordTrace]
  refine ⟨281207349162939895574035499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187471566108626597049356999 281207349162939895574035499)
  ·
    refine ⟨421811023744409843361053249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281207349162939895574035499 421811023744409843361053249)
    ·
      refine ⟨316358267808307382520789937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421811023744409843361053249 316358267808307382520789937)
      ·
        refine ⟨237268700856230536890592453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316358267808307382520789937 237268700856230536890592453)
        ·
          refine ⟨44487881410543225666986085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237268700856230536890592453 44487881410543225666986085)
          ·
            refine ⟨8341477764476854812559891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44487881410543225666986085 8341477764476854812559891)
            ·
              refine ⟨12512216646715282218839837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8341477764476854812559891 12512216646715282218839837)
              ·
                refine ⟨4692081242518230832064939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12512216646715282218839837 4692081242518230832064939)
                ·
                  refine ⟨7038121863777346248097409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692081242518230832064939 7038121863777346248097409)
                  ·
                    refine ⟨5278591397833009686073057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7038121863777346248097409 5278591397833009686073057)
                    ·
                      refine ⟨3958943548374757264554793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278591397833009686073057 3958943548374757264554793)
                      ·
                        rfl

theorem cell23_7710015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 1, 2, 2].length) (baseStart_7710015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710015 prefixEnd_7710015 := by exact prefixLift 7710015
  have htrace : WordTrace (prefixWord ++ tailWord_7710015) baseStart_7710015 baseEnd_7710015 := by
    simpa [prefixWord, tailWord_7710015, baseEnd_7710015] using wordTrace_append hprefix tailTrace_7710015
  have hstable : (prefixWord ++ tailWord_7710015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710015).length < 2 ^ (prefixWord ++ tailWord_7710015).sum := by decide
  have hdescent : baseEnd_7710015 < baseStart_7710015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710024 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 5, 3, 2]
def baseStart_7710024 : Nat := 118140960795 + 7710024 * 2 ^ 59
def prefixEnd_7710024 : Nat := 4983230072969 + 3 ^ 40 * 7710024 * 2
def baseEnd_7710024 : Nat := 3958948169700647729342251

theorem tailTrace_7710024 : CollatzResearch.WordTrace tailWord_7710024 prefixEnd_7710024 3958948169700647729342251 := by
  unfold tailWord_7710024
  simp only [CollatzResearch.WordTrace]
  refine ⟨140603838709953645055556563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187471784946604860074075417 140603838709953645055556563)
  ·
    refine ⟨210905758064930467583334845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140603838709953645055556563 210905758064930467583334845)
    ·
      refine ⟨79089659274348925343750567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210905758064930467583334845 79089659274348925343750567)
      ·
        refine ⟨118634488911523388015625851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79089659274348925343750567 118634488911523388015625851)
        ·
          refine ⟨177951733367285082023438777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118634488911523388015625851 177951733367285082023438777)
          ·
            refine ⟨133463800025463811517579083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177951733367285082023438777 133463800025463811517579083)
            ·
              refine ⟨200195700038195717276368625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133463800025463811517579083 200195700038195717276368625)
              ·
                refine ⟨150146775028646787957276469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200195700038195717276368625 150146775028646787957276469)
                ·
                  refine ⟨14076260158935636370994669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150146775028646787957276469 14076260158935636370994669)
                  ·
                    refine ⟨5278597559600863639123001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14076260158935636370994669 5278597559600863639123001)
                    ·
                      refine ⟨3958948169700647729342251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278597559600863639123001 3958948169700647729342251)
                      ·
                        rfl

theorem cell23_7710024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_7710024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710024 prefixEnd_7710024 := by exact prefixLift 7710024
  have htrace : WordTrace (prefixWord ++ tailWord_7710024) baseStart_7710024 baseEnd_7710024 := by
    simpa [prefixWord, tailWord_7710024, baseEnd_7710024] using wordTrace_append hprefix tailTrace_7710024
  have hstable : (prefixWord ++ tailWord_7710024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710024).length < 2 ^ (prefixWord ++ tailWord_7710024).sum := by decide
  have hdescent : baseEnd_7710024 < baseStart_7710024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710048 : List Nat := [2, 1, 1, 3, 4, 1, 4, 1, 2, 1, 3]
def baseStart_7710048 : Nat := 118140960795 + 7710048 * 2 ^ 59
def prefixEnd_7710048 : Nat := 4983230072969 + 3 ^ 40 * 7710048 * 2
def baseEnd_7710048 : Nat := 3958960493236355635442141

theorem tailTrace_7710048 : CollatzResearch.WordTrace tailWord_7710048 prefixEnd_7710048 3958960493236355635442141 := by
  unfold tailWord_7710048
  simp only [CollatzResearch.WordTrace]
  refine ⟨140604276385910171104993399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187472368514546894806657865 140604276385910171104993399)
  ·
    refine ⟨210906414578865256657490099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140604276385910171104993399 210906414578865256657490099)
    ·
      refine ⟨316359621868297884986235149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210906414578865256657490099 316359621868297884986235149)
      ·
        refine ⟨118634858200611706869838181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316359621868297884986235149 118634858200611706869838181)
        ·
          refine ⟨22244035912614695038094659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118634858200611706869838181 22244035912614695038094659)
          ·
            refine ⟨33366053868922042557141989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22244035912614695038094659 33366053868922042557141989)
            ·
              refine ⟨6256135100422882979464123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33366053868922042557141989 6256135100422882979464123)
              ·
                refine ⟨9384202650634324469196185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6256135100422882979464123 9384202650634324469196185)
                ·
                  refine ⟨7038151987975743351897139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9384202650634324469196185 7038151987975743351897139)
                  ·
                    refine ⟨10557227981963615027845709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7038151987975743351897139 10557227981963615027845709)
                    ·
                      refine ⟨3958960493236355635442141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10557227981963615027845709 3958960493236355635442141)
                      ·
                        rfl

theorem cell23_7710048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_7710048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710048 prefixEnd_7710048 := by exact prefixLift 7710048
  have htrace : WordTrace (prefixWord ++ tailWord_7710048) baseStart_7710048 baseEnd_7710048 := by
    simpa [prefixWord, tailWord_7710048, baseEnd_7710048] using wordTrace_append hprefix tailTrace_7710048
  have hstable : (prefixWord ++ tailWord_7710048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710048).length < 2 ^ (prefixWord ++ tailWord_7710048).sum := by decide
  have hdescent : baseEnd_7710048 < baseStart_7710048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710057 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 4, 4, 3]
def baseStart_7710057 : Nat := 118140960795 + 7710057 * 2 ^ 59
def prefixEnd_7710057 : Nat := 4983230072969 + 3 ^ 40 * 7710057 * 2
def baseEnd_7710057 : Nat := 3958965114562246100229599

theorem tailTrace_7710057 : CollatzResearch.WordTrace tailWord_7710057 prefixEnd_7710057 3958965114562246100229599 := by
  unfold tailWord_7710057
  simp only [CollatzResearch.WordTrace]
  refine ⟨281208881028787736747064425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187472587352525157831376283 281208881028787736747064425)
  ·
    refine ⟨210906660771590802560298319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281208881028787736747064425 210906660771590802560298319)
    ·
      refine ⟨316359991157386203840447479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210906660771590802560298319 316359991157386203840447479)
      ·
        refine ⟨474539986736079305760671219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316359991157386203840447479 474539986736079305760671219)
        ·
          refine ⟨711809980104118958641006829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474539986736079305760671219 711809980104118958641006829)
          ·
            refine ⟨266928742539044609490377561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 711809980104118958641006829 266928742539044609490377561)
            ·
              refine ⟨200196556904283457117783171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266928742539044609490377561 200196556904283457117783171)
              ·
                refine ⟨300294835356425185676674757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200196556904283457117783171 300294835356425185676674757)
                ·
                  refine ⟨56305281629329722314376517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300294835356425185676674757 56305281629329722314376517)
                  ·
                    refine ⟨10557240305499322933945597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56305281629329722314376517 10557240305499322933945597)
                    ·
                      refine ⟨3958965114562246100229599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10557240305499322933945597 3958965114562246100229599)
                      ·
                        rfl

theorem cell23_7710057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 4, 3].length) (baseStart_7710057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710057 prefixEnd_7710057 := by exact prefixLift 7710057
  have htrace : WordTrace (prefixWord ++ tailWord_7710057) baseStart_7710057 baseEnd_7710057 := by
    simpa [prefixWord, tailWord_7710057, baseEnd_7710057] using wordTrace_append hprefix tailTrace_7710057
  have hstable : (prefixWord ++ tailWord_7710057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710057).length < 2 ^ (prefixWord ++ tailWord_7710057).sum := by decide
  have hdescent : baseEnd_7710057 < baseStart_7710057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710058 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_7710058 : Nat := 118140960795 + 7710058 * 2 ^ 59
def prefixEnd_7710058 : Nat := 4983230072969 + 3 ^ 40 * 7710058 * 2
def baseEnd_7710058 : Nat := 3958965628042900596317095

theorem tailTrace_7710058 : CollatzResearch.WordTrace tailWord_7710058 prefixEnd_7710058 3958965628042900596317095 := by
  unfold tailWord_7710058
  simp only [CollatzResearch.WordTrace]
  refine ⟨70302229375446028479462707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187472611667856075945233885 70302229375446028479462707)
  ·
    refine ⟨105453344063169042719194061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70302229375446028479462707 105453344063169042719194061)
    ·
      refine ⟨39545004023688391019697773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105453344063169042719194061 39545004023688391019697773)
      ·
        refine ⟨14829376508883146632386665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39545004023688391019697773 14829376508883146632386665)
        ·
          refine ⟨11122032381662359974289999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14829376508883146632386665 11122032381662359974289999)
          ·
            refine ⟨16683048572493539961434999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11122032381662359974289999 16683048572493539961434999)
            ·
              refine ⟨25024572858740309942152499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16683048572493539961434999 25024572858740309942152499)
              ·
                refine ⟨37536859288110464913228749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25024572858740309942152499 37536859288110464913228749)
                ·
                  refine ⟨14076322233041424342460781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37536859288110464913228749 14076322233041424342460781)
                  ·
                    refine ⟨5278620837390534128422793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14076322233041424342460781 5278620837390534128422793)
                    ·
                      refine ⟨3958965628042900596317095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278620837390534128422793 3958965628042900596317095)
                      ·
                        rfl

theorem cell23_7710058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_7710058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710058 prefixEnd_7710058 := by exact prefixLift 7710058
  have htrace : WordTrace (prefixWord ++ tailWord_7710058) baseStart_7710058 baseEnd_7710058 := by
    simpa [prefixWord, tailWord_7710058, baseEnd_7710058] using wordTrace_append hprefix tailTrace_7710058
  have hstable : (prefixWord ++ tailWord_7710058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710058).length < 2 ^ (prefixWord ++ tailWord_7710058).sum := by decide
  have hdescent : baseEnd_7710058 < baseStart_7710058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710088 : List Nat := [2, 1, 3, 3, 1, 2, 1, 4, 2, 2, 2]
def baseStart_7710088 : Nat := 118140960795 + 7710088 * 2 ^ 59
def prefixEnd_7710088 : Nat := 4983230072969 + 3 ^ 40 * 7710088 * 2
def baseEnd_7710088 : Nat := 3958981032462535478941957

theorem tailTrace_7710088 : CollatzResearch.WordTrace tailWord_7710088 prefixEnd_7710088 3958981032462535478941957 := by
  unfold tailWord_7710088
  simp only [CollatzResearch.WordTrace]
  refine ⟨140605005845837714520721459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187473341127783619360961945 140605005845837714520721459)
  ·
    refine ⟨210907508768756571781082189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140605005845837714520721459 210907508768756571781082189)
    ·
      refine ⟨79090315788283714417905821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210907508768756571781082189 79090315788283714417905821)
      ·
        refine ⟨29658868420606392906714683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79090315788283714417905821 29658868420606392906714683)
        ·
          refine ⟨44488302630909589360072025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29658868420606392906714683 44488302630909589360072025)
          ·
            refine ⟨33366226973182192020054019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44488302630909589360072025 33366226973182192020054019)
            ·
              refine ⟨50049340459773288030081029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33366226973182192020054019 50049340459773288030081029)
              ·
                refine ⟨9384251336207491505640193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50049340459773288030081029 9384251336207491505640193)
                ·
                  refine ⟨7038188502155618629230145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9384251336207491505640193 7038188502155618629230145)
                  ·
                    refine ⟨5278641376616713971922609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7038188502155618629230145 5278641376616713971922609)
                    ·
                      refine ⟨3958981032462535478941957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278641376616713971922609 3958981032462535478941957)
                      ·
                        rfl

theorem cell23_7710088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_7710088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710088 prefixEnd_7710088 := by exact prefixLift 7710088
  have htrace : WordTrace (prefixWord ++ tailWord_7710088) baseStart_7710088 baseEnd_7710088 := by
    simpa [prefixWord, tailWord_7710088, baseEnd_7710088] using wordTrace_append hprefix tailTrace_7710088
  have hstable : (prefixWord ++ tailWord_7710088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710088).length < 2 ^ (prefixWord ++ tailWord_7710088).sum := by decide
  have hdescent : baseEnd_7710088 < baseStart_7710088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710117 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_7710117 : Nat := 118140960795 + 7710117 * 2 ^ 59
def prefixEnd_7710117 : Nat := 4983230072969 + 3 ^ 40 * 7710117 * 2
def baseEnd_7710117 : Nat := 3958995923401515865479323

theorem tailTrace_7710117 : CollatzResearch.WordTrace tailWord_7710117 prefixEnd_7710117 3958995923401515865479323 := by
  unfold tailWord_7710117
  simp only [CollatzResearch.WordTrace]
  refine ⟨281211069408570366994248605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187474046272380244662832403 281211069408570366994248605)
  ·
    refine ⟨105454151028213887622843227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281211069408570366994248605 105454151028213887622843227)
    ·
      refine ⟨158181226542320831434264841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105454151028213887622843227 158181226542320831434264841)
      ·
        refine ⟨118635919906740623575698631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158181226542320831434264841 118635919906740623575698631)
        ·
          refine ⟨177953879860110935363547947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118635919906740623575698631 177953879860110935363547947)
          ·
            refine ⟨266930819790166403045321921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177953879860110935363547947 266930819790166403045321921)
            ·
              refine ⟨200198114842624802283991441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266930819790166403045321921 200198114842624802283991441)
              ·
                refine ⟨150148586131968601712993581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200198114842624802283991441 150148586131968601712993581)
                ·
                  refine ⟨56305719799488225642372593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150148586131968601712993581 56305719799488225642372593)
                  ·
                    refine ⟨42229289849616169231779445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56305719799488225642372593 42229289849616169231779445)
                    ·
                      refine ⟨3958995923401515865479323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42229289849616169231779445 3958995923401515865479323)
                      ·
                        rfl

theorem cell23_7710117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_7710117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710117 prefixEnd_7710117 := by exact prefixLift 7710117
  have htrace : WordTrace (prefixWord ++ tailWord_7710117) baseStart_7710117 baseEnd_7710117 := by
    simpa [prefixWord, tailWord_7710117, baseEnd_7710117] using wordTrace_append hprefix tailTrace_7710117
  have hstable : (prefixWord ++ tailWord_7710117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710117).length < 2 ^ (prefixWord ++ tailWord_7710117).sum := by decide
  have hdescent : baseEnd_7710117 < baseStart_7710117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710124 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 2, 5]
def baseStart_7710124 : Nat := 118140960795 + 7710124 * 2 ^ 59
def prefixEnd_7710124 : Nat := 4983230072969 + 3 ^ 40 * 7710124 * 2
def baseEnd_7710124 : Nat := 1319666505922032446030597

theorem tailTrace_7710124 : CollatzResearch.WordTrace tailWord_7710124 prefixEnd_7710124 1319666505922032446030597 := by
  unfold tailWord_7710124
  simp only [CollatzResearch.WordTrace]
  refine ⟨140605662359772503594876713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187474216479696671459835617 140605662359772503594876713)
  ·
    refine ⟨105454246769829377696157535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140605662359772503594876713 105454246769829377696157535)
    ·
      refine ⟨158181370154744066544236303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105454246769829377696157535 158181370154744066544236303)
      ·
        refine ⟨237272055232116099816354455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158181370154744066544236303 237272055232116099816354455)
        ·
          refine ⟨355908082848174149724531683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237272055232116099816354455 355908082848174149724531683)
          ·
            refine ⟨533862124272261224586797525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355908082848174149724531683 533862124272261224586797525)
            ·
              refine ⟨12512393537631122451253067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 533862124272261224586797525 12512393537631122451253067)
              ·
                refine ⟨18768590306446683676879601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12512393537631122451253067 18768590306446683676879601)
                ·
                  refine ⟨14076442729835012757659701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18768590306446683676879601 14076442729835012757659701)
                  ·
                    refine ⟨1319666505922032446030597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14076442729835012757659701 1319666505922032446030597)
                    ·
                      rfl

theorem cell23_7710124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_7710124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710124 prefixEnd_7710124 := by exact prefixLift 7710124
  have htrace : WordTrace (prefixWord ++ tailWord_7710124) baseStart_7710124 baseEnd_7710124 := by
    simpa [prefixWord, tailWord_7710124, baseEnd_7710124] using wordTrace_append hprefix tailTrace_7710124
  have hstable : (prefixWord ++ tailWord_7710124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710124).length < 2 ^ (prefixWord ++ tailWord_7710124).sum := by decide
  have hdescent : baseEnd_7710124 < baseStart_7710124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710144 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 4]
def baseStart_7710144 : Nat := 118140960795 + 7710144 * 2 ^ 59
def prefixEnd_7710144 : Nat := 4983230072969 + 3 ^ 40 * 7710144 * 2
def baseEnd_7710144 : Nat := 3959009787379187259841699

theorem tailTrace_7710144 : CollatzResearch.WordTrace tailWord_7710144 prefixEnd_7710144 3959009787379187259841699 := by
  unfold tailWord_7710144
  simp only [CollatzResearch.WordTrace]
  refine ⟨140606027089736275302740743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187474702786315033736987657 140606027089736275302740743)
  ·
    refine ⟨210909040634604412954111115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140606027089736275302740743 210909040634604412954111115)
    ·
      refine ⟨316363560951906619431166673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210909040634604412954111115 316363560951906619431166673)
      ·
        refine ⟨237272670713929964573375005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316363560951906619431166673 237272670713929964573375005)
        ·
          refine ⟨88977251517723736715015627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237272670713929964573375005 88977251517723736715015627)
          ·
            refine ⟨133465877276585605072523441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88977251517723736715015627 133465877276585605072523441)
            ·
              refine ⟨100099407957439203804392581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133465877276585605072523441 100099407957439203804392581)
              ·
                refine ⟨18768638992019850713323609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100099407957439203804392581 18768638992019850713323609)
                ·
                  refine ⟨14076479244014888034992707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18768638992019850713323609 14076479244014888034992707)
                  ·
                    refine ⟨21114718866022332052489061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14076479244014888034992707 21114718866022332052489061)
                    ·
                      refine ⟨3959009787379187259841699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21114718866022332052489061 3959009787379187259841699)
                      ·
                        rfl

theorem cell23_7710144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_7710144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710144 prefixEnd_7710144 := by exact prefixLift 7710144
  have htrace : WordTrace (prefixWord ++ tailWord_7710144) baseStart_7710144 baseEnd_7710144 := by
    simpa [prefixWord, tailWord_7710144, baseEnd_7710144] using wordTrace_append hprefix tailTrace_7710144
  have hstable : (prefixWord ++ tailWord_7710144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710144).length < 2 ^ (prefixWord ++ tailWord_7710144).sum := by decide
  have hdescent : baseEnd_7710144 < baseStart_7710144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710147 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 5]
def baseStart_7710147 : Nat := 118140960795 + 7710147 * 2 ^ 59
def prefixEnd_7710147 : Nat := 4983230072969 + 3 ^ 40 * 7710147 * 2
def baseEnd_7710147 : Nat := 3959011327821150748104185

theorem tailTrace_7710147 : CollatzResearch.WordTrace tailWord_7710147 prefixEnd_7710147 3959011327821150748104185 := by
  unfold tailWord_7710147
  simp only [CollatzResearch.WordTrace]
  refine ⟨281212163598461682117840695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187474775732307788078560463 281212163598461682117840695)
  ·
    refine ⟨421818245397692523176761043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281212163598461682117840695 421818245397692523176761043)
    ·
      refine ⟨632727368096538784765141565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421818245397692523176761043 632727368096538784765141565)
      ·
        refine ⟨237272763036202044286928087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 632727368096538784765141565 237272763036202044286928087)
        ·
          refine ⟨355909144554303066430392131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237272763036202044286928087 355909144554303066430392131)
          ·
            refine ⟨533863716831454599645588197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355909144554303066430392131 533863716831454599645588197)
            ·
              refine ⟨100099446905897737433547787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 533863716831454599645588197 100099446905897737433547787)
              ·
                refine ⟨150149170358846606150321681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100099446905897737433547787 150149170358846606150321681)
                ·
                  refine ⟨112611877769134954612741261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150149170358846606150321681 112611877769134954612741261)
                  ·
                    refine ⟨42229454163425607979777973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112611877769134954612741261 42229454163425607979777973)
                    ·
                      refine ⟨3959011327821150748104185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42229454163425607979777973 3959011327821150748104185)
                      ·
                        rfl

theorem cell23_7710147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_7710147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710147 prefixEnd_7710147 := by exact prefixLift 7710147
  have htrace : WordTrace (prefixWord ++ tailWord_7710147) baseStart_7710147 baseEnd_7710147 := by
    simpa [prefixWord, tailWord_7710147, baseEnd_7710147] using wordTrace_append hprefix tailTrace_7710147
  have hstable : (prefixWord ++ tailWord_7710147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710147).length < 2 ^ (prefixWord ++ tailWord_7710147).sum := by decide
  have hdescent : baseEnd_7710147 < baseStart_7710147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710181 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 1, 4, 3]
def baseStart_7710181 : Nat := 118140960795 + 7710181 * 2 ^ 59
def prefixEnd_7710181 : Nat := 4983230072969 + 3 ^ 40 * 7710181 * 2
def baseEnd_7710181 : Nat := 3959028786163403615079029

theorem tailTrace_7710181 : CollatzResearch.WordTrace tailWord_7710181 prefixEnd_7710181 3959028786163403615079029 := by
  unfold tailWord_7710181
  simp only [CollatzResearch.WordTrace]
  refine ⟨281213403680338505924578397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187475602453559003949718931 281213403680338505924578397)
  ·
    refine ⟨105455026380126939721716899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281213403680338505924578397 105455026380126939721716899)
    ·
      refine ⟨158182539570190409582575349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105455026380126939721716899 158182539570190409582575349)
      ·
        refine ⟨14829613084705350898366439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158182539570190409582575349 14829613084705350898366439)
        ·
          refine ⟨22244419627058026347549659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14829613084705350898366439 22244419627058026347549659)
          ·
            refine ⟨33366629440587039521324489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22244419627058026347549659 33366629440587039521324489)
            ·
              refine ⟨25024972080440279640993367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33366629440587039521324489 25024972080440279640993367)
              ·
                refine ⟨37537458120660419461490051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25024972080440279640993367 37537458120660419461490051)
                ·
                  refine ⟨56306187180990629192235077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37537458120660419461490051 56306187180990629192235077)
                  ·
                    refine ⟨10557410096435742973544077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56306187180990629192235077 10557410096435742973544077)
                    ·
                      refine ⟨3959028786163403615079029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10557410096435742973544077 3959028786163403615079029)
                      ·
                        rfl

theorem cell23_7710181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_7710181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710181 prefixEnd_7710181 := by exact prefixLift 7710181
  have htrace : WordTrace (prefixWord ++ tailWord_7710181) baseStart_7710181 baseEnd_7710181 := by
    simpa [prefixWord, tailWord_7710181, baseEnd_7710181] using wordTrace_append hprefix tailTrace_7710181
  have hstable : (prefixWord ++ tailWord_7710181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710181).length < 2 ^ (prefixWord ++ tailWord_7710181).sum := by decide
  have hdescent : baseEnd_7710181 < baseStart_7710181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710187 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 8]
def baseStart_7710187 : Nat := 118140960795 + 7710187 * 2 ^ 59
def prefixEnd_7710187 : Nat := 4983230072969 + 3 ^ 40 * 7710187 * 2
def baseEnd_7710187 : Nat := 3959031867047330591604001

theorem tailTrace_7710187 : CollatzResearch.WordTrace tailWord_7710187 prefixEnd_7710187 3959031867047330591604001 := by
  unfold tailWord_7710187
  simp only [CollatzResearch.WordTrace]
  refine ⟨281213622518316768949296815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187475748345544512632864543 281213622518316768949296815)
  ·
    refine ⟨421820433777475153423945223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281213622518316768949296815 421820433777475153423945223)
    ·
      refine ⟨632730650666212730135917835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421820433777475153423945223 632730650666212730135917835)
      ·
        refine ⟨949095975999319095203876753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632730650666212730135917835 949095975999319095203876753)
        ·
          refine ⟨711821981999489321402907565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 949095975999319095203876753 711821981999489321402907565)
          ·
            refine ⟨266933243249808495526090337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 711821981999489321402907565 266933243249808495526090337)
            ·
              refine ⟨200199932437356371644567753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266933243249808495526090337 200199932437356371644567753)
              ·
                refine ⟨150149949328017278733425815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200199932437356371644567753 150149949328017278733425815)
                ·
                  refine ⟨225224923992025918100138723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150149949328017278733425815 225224923992025918100138723)
                  ·
                    refine ⟨337837385988038877150208085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 225224923992025918100138723 337837385988038877150208085)
                    ·
                      refine ⟨3959031867047330591604001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 337837385988038877150208085 3959031867047330591604001)
                      ·
                        rfl

theorem cell23_7710187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_7710187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710187 prefixEnd_7710187 := by exact prefixLift 7710187
  have htrace : WordTrace (prefixWord ++ tailWord_7710187) baseStart_7710187 baseEnd_7710187 := by
    simpa [prefixWord, tailWord_7710187, baseEnd_7710187] using wordTrace_append hprefix tailTrace_7710187
  have hstable : (prefixWord ++ tailWord_7710187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710187).length < 2 ^ (prefixWord ++ tailWord_7710187).sum := by decide
  have hdescent : baseEnd_7710187 < baseStart_7710187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710198 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_7710198 : Nat := 118140960795 + 7710198 * 2 ^ 59
def prefixEnd_7710198 : Nat := 4983230072969 + 3 ^ 40 * 7710198 * 2
def baseEnd_7710198 : Nat := 3959037515334530048566451

theorem tailTrace_7710198 : CollatzResearch.WordTrace tailWord_7710198 prefixEnd_7710198 3959037515334530048566451 := by
  unfold tailWord_7710198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17575876482579807364246703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187476015814184611885298165 17575876482579807364246703)
  ·
    refine ⟨26363814723869711046370055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17575876482579807364246703 26363814723869711046370055)
    ·
      refine ⟨39545722085804566569555083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26363814723869711046370055 39545722085804566569555083)
      ·
        refine ⟨59318583128706849854332625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39545722085804566569555083 59318583128706849854332625)
        ·
          refine ⟨44488937346530137390749469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59318583128706849854332625 44488937346530137390749469)
          ·
            refine ⟨16683351504948801521531051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44488937346530137390749469 16683351504948801521531051)
            ·
              refine ⟨25025027257423202282296577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16683351504948801521531051 25025027257423202282296577)
              ·
                refine ⟨18768770443067401711722433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25025027257423202282296577 18768770443067401711722433)
                ·
                  refine ⟨14076577832300551283791825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18768770443067401711722433 14076577832300551283791825)
                  ·
                    refine ⟨10557433374225413462843869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14076577832300551283791825 10557433374225413462843869)
                    ·
                      refine ⟨3959037515334530048566451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10557433374225413462843869 3959037515334530048566451)
                      ·
                        rfl

theorem cell23_7710198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_7710198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710198 prefixEnd_7710198 := by exact prefixLift 7710198
  have htrace : WordTrace (prefixWord ++ tailWord_7710198) baseStart_7710198 baseEnd_7710198 := by
    simpa [prefixWord, tailWord_7710198, baseEnd_7710198] using wordTrace_append hprefix tailTrace_7710198
  have hstable : (prefixWord ++ tailWord_7710198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710198).length < 2 ^ (prefixWord ++ tailWord_7710198).sum := by decide
  have hdescent : baseEnd_7710198 < baseStart_7710198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710205 : List Nat := [1, 4, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_7710205 : Nat := 118140960795 + 7710205 * 2 ^ 59
def prefixEnd_7710205 : Nat := 4983230072969 + 3 ^ 40 * 7710205 * 2
def baseEnd_7710205 : Nat := 1319680369899703840392973

theorem tailTrace_7710205 : CollatzResearch.WordTrace tailWord_7710205 prefixEnd_7710205 1319680369899703840392973 := by
  unfold tailWord_7710205
  simp only [CollatzResearch.WordTrace]
  refine ⟨281214279032251558023452069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187476186021501038682301379 281214279032251558023452069)
  ·
    refine ⟨52727677318547167129397263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281214279032251558023452069 52727677318547167129397263)
    ·
      refine ⟨79091515977820750694095895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52727677318547167129397263 79091515977820750694095895)
      ·
        refine ⟨118637273966731126041143843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79091515977820750694095895 118637273966731126041143843)
        ·
          refine ⟨177955910950096689061715765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118637273966731126041143843 177955910950096689061715765)
          ·
            refine ⟨16683366651571564599535853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177955910950096689061715765 16683366651571564599535853)
            ·
              refine ⟨6256262494339336724825945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16683366651571564599535853 6256262494339336724825945)
              ·
                refine ⟨4692196870754502543619459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6256262494339336724825945 4692196870754502543619459)
                ·
                  refine ⟨7038295306131753815429189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692196870754502543619459 7038295306131753815429189)
                  ·
                    refine ⟨1319680369899703840392973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7038295306131753815429189 1319680369899703840392973)
                    ·
                      rfl

theorem cell23_7710205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_7710205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710205 prefixEnd_7710205 := by exact prefixLift 7710205
  have htrace : WordTrace (prefixWord ++ tailWord_7710205) baseStart_7710205 baseEnd_7710205 := by
    simpa [prefixWord, tailWord_7710205, baseEnd_7710205] using wordTrace_append hprefix tailTrace_7710205
  have hstable : (prefixWord ++ tailWord_7710205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710205).length < 2 ^ (prefixWord ++ tailWord_7710205).sum := by decide
  have hdescent : baseEnd_7710205 < baseStart_7710205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710211 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 3, 1, 3]
def baseStart_7710211 : Nat := 118140960795 + 7710211 * 2 ^ 59
def prefixEnd_7710211 : Nat := 4983230072969 + 3 ^ 40 * 7710211 * 2
def baseEnd_7710211 : Nat := 3959044190583038497703891

theorem tailTrace_7710211 : CollatzResearch.WordTrace tailWord_7710211 prefixEnd_7710211 3959044190583038497703891 := by
  unfold tailWord_7710211
  simp only [CollatzResearch.WordTrace]
  refine ⟨281214497870229821048170487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187476331913486547365446991 281214497870229821048170487)
  ·
    refine ⟨421821746805344731572255731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281214497870229821048170487 421821746805344731572255731)
    ·
      refine ⟨632732620208017097358383597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421821746805344731572255731 632732620208017097358383597)
      ·
        refine ⟨237274732578006411509393849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 632732620208017097358383597 237274732578006411509393849)
        ·
          refine ⟨177956049433504808632045387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237274732578006411509393849 177956049433504808632045387)
          ·
            refine ⟨266934074150257212948068081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177956049433504808632045387 266934074150257212948068081)
            ·
              refine ⟨200200555612692909711051061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266934074150257212948068081 200200555612692909711051061)
              ·
                refine ⟨18768802088689960285411037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200200555612692909711051061 18768802088689960285411037)
                ·
                  refine ⟨7038300783258735107029139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18768802088689960285411037 7038300783258735107029139)
                  ·
                    refine ⟨10557451174888102660543709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7038300783258735107029139 10557451174888102660543709)
                    ·
                      refine ⟨3959044190583038497703891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10557451174888102660543709 3959044190583038497703891)
                      ·
                        rfl

theorem cell23_7710211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_7710211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710211 prefixEnd_7710211 := by exact prefixLift 7710211
  have htrace : WordTrace (prefixWord ++ tailWord_7710211) baseStart_7710211 baseEnd_7710211 := by
    simpa [prefixWord, tailWord_7710211, baseEnd_7710211] using wordTrace_append hprefix tailTrace_7710211
  have hstable : (prefixWord ++ tailWord_7710211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710211).length < 2 ^ (prefixWord ++ tailWord_7710211).sum := by decide
  have hdescent : baseEnd_7710211 < baseStart_7710211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710218 : List Nat := [3, 1, 2, 2, 2, 4, 2, 1, 6]
def baseStart_7710218 : Nat := 118140960795 + 7710218 * 2 ^ 59
def prefixEnd_7710218 : Nat := 4983230072969 + 3 ^ 40 * 7710218 * 2
def baseEnd_7710218 : Nat := 439894198327513330035151

theorem tailTrace_7710218 : CollatzResearch.WordTrace tailWord_7710218 prefixEnd_7710218 439894198327513330035151 := by
  unfold tailWord_7710218
  simp only [CollatzResearch.WordTrace]
  refine ⟨70303688295301115310918827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187476502120802974162450205 70303688295301115310918827)
  ·
    refine ⟨105455532442951672966378241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70303688295301115310918827 105455532442951672966378241)
    ·
      refine ⟨79091649332213754724783681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105455532442951672966378241 79091649332213754724783681)
      ·
        refine ⟨59318736999160316043587761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79091649332213754724783681 59318736999160316043587761)
        ·
          refine ⟨44489052749370237032690821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59318736999160316043587761 44489052749370237032690821)
          ·
            refine ⟨8341697390506919443629529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44489052749370237032690821 8341697390506919443629529)
            ·
              refine ⟨6256273042880189582722147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8341697390506919443629529 6256273042880189582722147)
              ·
                refine ⟨9384409564320284374083221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6256273042880189582722147 9384409564320284374083221)
                ·
                  refine ⟨439894198327513330035151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9384409564320284374083221 439894198327513330035151)
                  ·
                    rfl

theorem cell23_7710218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 6].length) (baseStart_7710218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710218 prefixEnd_7710218 := by exact prefixLift 7710218
  have htrace : WordTrace (prefixWord ++ tailWord_7710218) baseStart_7710218 baseEnd_7710218 := by
    simpa [prefixWord, tailWord_7710218, baseEnd_7710218] using wordTrace_append hprefix tailTrace_7710218
  have hstable : (prefixWord ++ tailWord_7710218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710218).length < 2 ^ (prefixWord ++ tailWord_7710218).sum := by decide
  have hdescent : baseEnd_7710218 < baseStart_7710218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710271 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 3]
def baseStart_7710271 : Nat := 118140960795 + 7710271 * 2 ^ 59
def prefixEnd_7710271 : Nat := 4983230072969 + 3 ^ 40 * 7710271 * 2
def baseEnd_7710271 : Nat := 3959074999422308262953615

theorem tailTrace_7710271 : CollatzResearch.WordTrace tailWord_7710271 prefixEnd_7710271 3959074999422308262953615 := by
  unfold tailWord_7710271
  simp only [CollatzResearch.WordTrace]
  refine ⟨281216686250012451295354667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187477790833341634196903111 281216686250012451295354667)
  ·
    refine ⟨421825029375018676943032001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281216686250012451295354667 421825029375018676943032001)
    ·
      refine ⟨316368772031264007707274001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421825029375018676943032001 316368772031264007707274001)
      ·
        refine ⟨237276579023448005780455501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316368772031264007707274001 237276579023448005780455501)
        ·
          refine ⟨88978717133793002167670813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237276579023448005780455501 88978717133793002167670813)
          ·
            refine ⟨33367018925172375812876555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88978717133793002167670813 33367018925172375812876555)
            ·
              refine ⟨50050528387758563719314833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33367018925172375812876555 50050528387758563719314833)
              ·
                refine ⟨37537896290818922789486125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50050528387758563719314833 37537896290818922789486125)
                ·
                  refine ⟨14076711109057096046057297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37537896290818922789486125 14076711109057096046057297)
                  ·
                    refine ⟨10557533331792822034542973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14076711109057096046057297 10557533331792822034542973)
                    ·
                      refine ⟨3959074999422308262953615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10557533331792822034542973 3959074999422308262953615)
                      ·
                        rfl

theorem cell23_7710271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_7710271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710271 prefixEnd_7710271 := by exact prefixLift 7710271
  have htrace : WordTrace (prefixWord ++ tailWord_7710271) baseStart_7710271 baseEnd_7710271 := by
    simpa [prefixWord, tailWord_7710271, baseEnd_7710271] using wordTrace_append hprefix tailTrace_7710271
  have hstable : (prefixWord ++ tailWord_7710271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710271).length < 2 ^ (prefixWord ++ tailWord_7710271).sum := by decide
  have hdescent : baseEnd_7710271 < baseStart_7710271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710461 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_7710461 : Nat := 118140960795 + 7710461 * 2 ^ 59
def prefixEnd_7710461 : Nat := 4983230072969 + 3 ^ 40 * 7710461 * 2
def baseEnd_7710461 : Nat := 3959172560746662519577741

theorem tailTrace_7710461 : CollatzResearch.WordTrace tailWord_7710461 prefixEnd_7710461 3959172560746662519577741 := by
  unfold tailWord_7710461
  simp only [CollatzResearch.WordTrace]
  refine ⟨281223616119324113744771237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187482410746216075829847491 281223616119324113744771237)
  ·
    refine ⟨52729428022373271327144607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281223616119324113744771237 52729428022373271327144607)
    ·
      refine ⟨79094142033559906990716911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52729428022373271327144607 79094142033559906990716911)
      ·
        refine ⟨118641213050339860486075367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79094142033559906990716911 118641213050339860486075367)
        ·
          refine ⟨177961819575509790729113051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118641213050339860486075367 177961819575509790729113051)
          ·
            refine ⟨266942729363264686093669577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177961819575509790729113051 266942729363264686093669577)
            ·
              refine ⟨200207047022448514570252183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266942729363264686093669577 200207047022448514570252183)
              ·
                refine ⟨300310570533672771855378275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200207047022448514570252183 300310570533672771855378275)
                ·
                  refine ⟨450465855800509157783067413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300310570533672771855378275 450465855800509157783067413)
                  ·
                    refine ⟨21115586990648866771081285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 450465855800509157783067413 21115586990648866771081285)
                    ·
                      refine ⟨3959172560746662519577741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21115586990648866771081285 3959172560746662519577741)
                      ·
                        rfl

theorem cell23_7710461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_7710461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710461 prefixEnd_7710461 := by exact prefixLift 7710461
  have htrace : WordTrace (prefixWord ++ tailWord_7710461) baseStart_7710461 baseEnd_7710461 := by
    simpa [prefixWord, tailWord_7710461, baseEnd_7710461] using wordTrace_append hprefix tailTrace_7710461
  have hstable : (prefixWord ++ tailWord_7710461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710461).length < 2 ^ (prefixWord ++ tailWord_7710461).sum := by decide
  have hdescent : baseEnd_7710461 < baseStart_7710461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710462 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_7710462 : Nat := 118140960795 + 7710462 * 2 ^ 59
def prefixEnd_7710462 : Nat := 4983230072969 + 3 ^ 40 * 7710462 * 2
def baseEnd_7710462 : Nat := 1319724358075772338555079

theorem tailTrace_7710462 : CollatzResearch.WordTrace tailWord_7710462 prefixEnd_7710462 1319724358075772338555079 := by
  unfold tailWord_7710462
  simp only [CollatzResearch.WordTrace]
  refine ⟨35152956574040061364444705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187482435061546993943705093 35152956574040061364444705)
  ·
    refine ⟨26364717430530046023333529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35152956574040061364444705 26364717430530046023333529)
    ·
      refine ⟨19773538072897534517500147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26364717430530046023333529 19773538072897534517500147)
      ·
        refine ⟨29660307109346301776250221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19773538072897534517500147 29660307109346301776250221)
        ·
          refine ⟨11122615166004863166093833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29660307109346301776250221 11122615166004863166093833)
          ·
            refine ⟨8341961374503647374570375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11122615166004863166093833 8341961374503647374570375)
            ·
              refine ⟨12512942061755471061855563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8341961374503647374570375 12512942061755471061855563)
              ·
                refine ⟨18769413092633206592783345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12512942061755471061855563 18769413092633206592783345)
                ·
                  refine ⟨14077059819474904944587509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18769413092633206592783345 14077059819474904944587509)
                  ·
                    refine ⟨1319724358075772338555079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14077059819474904944587509 1319724358075772338555079)
                    ·
                      rfl

theorem cell23_7710462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_7710462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710462 prefixEnd_7710462 := by exact prefixLift 7710462
  have htrace : WordTrace (prefixWord ++ tailWord_7710462) baseStart_7710462 baseEnd_7710462 := by
    simpa [prefixWord, tailWord_7710462, baseEnd_7710462] using wordTrace_append hprefix tailTrace_7710462
  have hstable : (prefixWord ++ tailWord_7710462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710462).length < 2 ^ (prefixWord ++ tailWord_7710462).sum := by decide
  have hdescent : baseEnd_7710462 < baseStart_7710462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710475 : List Nat := [1, 1, 1, 1, 5, 1, 3, 5, 1, 4]
def baseStart_7710475 : Nat := 118140960795 + 7710475 * 2 ^ 59
def prefixEnd_7710475 : Nat := 4983230072969 + 3 ^ 40 * 7710475 * 2
def baseEnd_7710475 : Nat := 1319726583158608488267559

theorem tailTrace_7710475 : CollatzResearch.WordTrace tailWord_7710475 prefixEnd_7710475 1319726583158608488267559 := by
  unfold tailWord_7710475
  simp only [CollatzResearch.WordTrace]
  refine ⟨281224126741273394135780879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187482751160848929423853919 281224126741273394135780879)
  ·
    refine ⟨421836190111910091203671319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281224126741273394135780879 421836190111910091203671319)
    ·
      refine ⟨632754285167865136805506979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421836190111910091203671319 632754285167865136805506979)
      ·
        refine ⟨949131427751797705208260469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632754285167865136805506979 949131427751797705208260469)
        ·
          refine ⟨88981071351731034863274419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 949131427751797705208260469 88981071351731034863274419)
          ·
            refine ⟨133471607027596552294911629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88981071351731034863274419 133471607027596552294911629)
            ·
              refine ⟨50051852635348707110591861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133471607027596552294911629 50051852635348707110591861)
              ·
                refine ⟨4692361184563941291617987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50051852635348707110591861 4692361184563941291617987)
                ·
                  refine ⟨7038541776845911937426981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692361184563941291617987 7038541776845911937426981)
                  ·
                    refine ⟨1319726583158608488267559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7038541776845911937426981 1319726583158608488267559)
                    ·
                      rfl

theorem cell23_7710475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 1, 4].length) (baseStart_7710475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710475 prefixEnd_7710475 := by exact prefixLift 7710475
  have htrace : WordTrace (prefixWord ++ tailWord_7710475) baseStart_7710475 baseEnd_7710475 := by
    simpa [prefixWord, tailWord_7710475, baseEnd_7710475] using wordTrace_append hprefix tailTrace_7710475
  have hstable : (prefixWord ++ tailWord_7710475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710475).length < 2 ^ (prefixWord ++ tailWord_7710475).sum := by decide
  have hdescent : baseEnd_7710475 < baseStart_7710475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710477 : List Nat := [1, 7, 2, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_7710477 : Nat := 118140960795 + 7710477 * 2 ^ 59
def prefixEnd_7710477 : Nat := 4983230072969 + 3 ^ 40 * 7710477 * 2
def baseEnd_7710477 : Nat := 3959180776437134456977669

theorem tailTrace_7710477 : CollatzResearch.WordTrace tailWord_7710477 prefixEnd_7710477 3959180776437134456977669 := by
  unfold tailWord_7710477
  simp only [CollatzResearch.WordTrace]
  refine ⟨281224199687266148477353685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187482799791510765651569123 281224199687266148477353685)
  ·
    refine ⟨6591192180170300354937977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 281224199687266148477353685 6591192180170300354937977)
    ·
      refine ⟨4943394135127725266203483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6591192180170300354937977 4943394135127725266203483)
      ·
        refine ⟨7415091202691587899305225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4943394135127725266203483 7415091202691587899305225)
        ·
          refine ⟨5561318402018690924478919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7415091202691587899305225 5561318402018690924478919)
          ·
            refine ⟨8341977603028036386718379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5561318402018690924478919 8341977603028036386718379)
            ·
              refine ⟨12512966404542054580077569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8341977603028036386718379 12512966404542054580077569)
              ·
                refine ⟨9384724803406540935058177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12512966404542054580077569 9384724803406540935058177)
                ·
                  refine ⟨7038543602554905701293633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9384724803406540935058177 7038543602554905701293633)
                  ·
                    refine ⟨5278907701916179275970225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7038543602554905701293633 5278907701916179275970225)
                    ·
                      refine ⟨3959180776437134456977669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278907701916179275970225 3959180776437134456977669)
                      ·
                        rfl

theorem cell23_7710477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_7710477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710477 prefixEnd_7710477 := by exact prefixLift 7710477
  have htrace : WordTrace (prefixWord ++ tailWord_7710477) baseStart_7710477 baseEnd_7710477 := by
    simpa [prefixWord, tailWord_7710477, baseEnd_7710477] using wordTrace_append hprefix tailTrace_7710477
  have hstable : (prefixWord ++ tailWord_7710477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710477).length < 2 ^ (prefixWord ++ tailWord_7710477).sum := by decide
  have hdescent : baseEnd_7710477 < baseStart_7710477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710482 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_7710482 : Nat := 118140960795 + 7710482 * 2 ^ 59
def prefixEnd_7710482 : Nat := 4983230072969 + 3 ^ 40 * 7710482 * 2
def baseEnd_7710482 : Nat := 3959183343840406937415145

theorem tailTrace_7710482 : CollatzResearch.WordTrace tailWord_7710482 prefixEnd_7710482 3959183343840406937415145 := by
  unfold tailWord_7710482
  simp only [CollatzResearch.WordTrace]
  refine ⟨70306095513062008582821425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187482921368165356220857133 70306095513062008582821425)
  ·
    refine ⟨52729571634796506437116069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70306095513062008582821425 52729571634796506437116069)
    ·
      refine ⟨9886794681524344956959263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52729571634796506437116069 9886794681524344956959263)
      ·
        refine ⟨14830192022286517435438895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9886794681524344956959263 14830192022286517435438895)
        ·
          refine ⟨22245288033429776153158343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14830192022286517435438895 22245288033429776153158343)
          ·
            refine ⟨33367932050144664229737515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22245288033429776153158343 33367932050144664229737515)
            ·
              refine ⟨50051898075216996344606273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33367932050144664229737515 50051898075216996344606273)
              ·
                refine ⟨37538923556412747258454705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50051898075216996344606273 37538923556412747258454705)
                ·
                  refine ⟨28154192667309560443841029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37538923556412747258454705 28154192667309560443841029)
                  ·
                    refine ⟨5278911125120542583220193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28154192667309560443841029 5278911125120542583220193)
                    ·
                      refine ⟨3959183343840406937415145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278911125120542583220193 3959183343840406937415145)
                      ·
                        rfl

theorem cell23_7710482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_7710482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710482 prefixEnd_7710482 := by exact prefixLift 7710482
  have htrace : WordTrace (prefixWord ++ tailWord_7710482) baseStart_7710482 baseEnd_7710482 := by
    simpa [prefixWord, tailWord_7710482, baseEnd_7710482] using wordTrace_append hprefix tailTrace_7710482
  have hstable : (prefixWord ++ tailWord_7710482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710482).length < 2 ^ (prefixWord ++ tailWord_7710482).sum := by decide
  have hdescent : baseEnd_7710482 < baseStart_7710482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710488 : List Nat := [2, 1, 2, 3, 1, 1, 5, 2, 6]
def baseStart_7710488 : Nat := 118140960795 + 7710488 * 2 ^ 59
def prefixEnd_7710488 : Nat := 4983230072969 + 3 ^ 40 * 7710488 * 2
def baseEnd_7710488 : Nat := 439909602747148212660013

theorem tailTrace_7710488 : CollatzResearch.WordTrace tailWord_7710488 prefixEnd_7710488 439909602747148212660013 := by
  unfold tailWord_7710488
  simp only [CollatzResearch.WordTrace]
  refine ⟨140612300445113148678002059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187483067260150864904002745 140612300445113148678002059)
  ·
    refine ⟨210918450667669723017003089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140612300445113148678002059 210918450667669723017003089)
    ·
      refine ⟨158188838000752292262752317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210918450667669723017003089 158188838000752292262752317)
      ·
        refine ⟨59320814250282109598532119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158188838000752292262752317 59320814250282109598532119)
        ·
          refine ⟨88981221375423164397798179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59320814250282109598532119 88981221375423164397798179)
          ·
            refine ⟨133471832063134746596697269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88981221375423164397798179 133471832063134746596697269)
            ·
              refine ⟨12512984255918882493440369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133471832063134746596697269 12512984255918882493440369)
              ·
                refine ⟨9384738191939161870080277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12512984255918882493440369 9384738191939161870080277)
                ·
                  refine ⟨439909602747148212660013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9384738191939161870080277 439909602747148212660013)
                  ·
                    rfl

theorem cell23_7710488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 6].length) (baseStart_7710488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710488 prefixEnd_7710488 := by exact prefixLift 7710488
  have htrace : WordTrace (prefixWord ++ tailWord_7710488) baseStart_7710488 baseEnd_7710488 := by
    simpa [prefixWord, tailWord_7710488, baseEnd_7710488] using wordTrace_append hprefix tailTrace_7710488
  have hstable : (prefixWord ++ tailWord_7710488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710488).length < 2 ^ (prefixWord ++ tailWord_7710488).sum := by decide
  have hdescent : baseEnd_7710488 < baseStart_7710488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710568 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7710568 : Nat := 118140960795 + 7710568 * 2 ^ 59
def prefixEnd_7710568 : Nat := 4983230072969 + 3 ^ 40 * 7710568 * 2
def baseEnd_7710568 : Nat := 3959227503176693600939749

theorem tailTrace_7710568 : CollatzResearch.WordTrace tailWord_7710568 prefixEnd_7710568 3959227503176693600939749 := by
  unfold tailWord_7710568
  simp only [CollatzResearch.WordTrace]
  refine ⟨140613759364968235509458179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187485012486624314012610905 140613759364968235509458179)
  ·
    refine ⟨210920639047452353264187269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140613759364968235509458179 210920639047452353264187269)
    ·
      refine ⟨39547619821397316237035113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210920639047452353264187269 39547619821397316237035113)
      ·
        refine ⟨29660714866047987177776335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39547619821397316237035113 29660714866047987177776335)
        ·
          refine ⟨44491072299071980766664503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29660714866047987177776335 44491072299071980766664503)
          ·
            refine ⟨66736608448607971149996755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44491072299071980766664503 66736608448607971149996755)
            ·
              refine ⟨100104912672911956724995133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66736608448607971149996755 100104912672911956724995133)
              ·
                refine ⟨37539342252341983771873175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100104912672911956724995133 37539342252341983771873175)
                ·
                  refine ⟨56309013378512975657809763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37539342252341983771873175 56309013378512975657809763)
                  ·
                    refine ⟨84463520067769463486714645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56309013378512975657809763 84463520067769463486714645)
                    ·
                      refine ⟨3959227503176693600939749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84463520067769463486714645 3959227503176693600939749)
                      ·
                        rfl

theorem cell23_7710568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7710568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710568 prefixEnd_7710568 := by exact prefixLift 7710568
  have htrace : WordTrace (prefixWord ++ tailWord_7710568) baseStart_7710568 baseEnd_7710568 := by
    simpa [prefixWord, tailWord_7710568, baseEnd_7710568] using wordTrace_append hprefix tailTrace_7710568
  have hstable : (prefixWord ++ tailWord_7710568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710568).length < 2 ^ (prefixWord ++ tailWord_7710568).sum := by decide
  have hdescent : baseEnd_7710568 < baseStart_7710568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710572 : List Nat := [2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 4]
def baseStart_7710572 : Nat := 118140960795 + 7710572 * 2 ^ 59
def prefixEnd_7710572 : Nat := 4983230072969 + 3 ^ 40 * 7710572 * 2
def baseEnd_7710572 : Nat := 3959229557099311585289731

theorem tailTrace_7710572 : CollatzResearch.WordTrace tailWord_7710572 prefixEnd_7710572 3959229557099311585289731 := by
  unfold tailWord_7710572
  simp only [CollatzResearch.WordTrace]
  refine ⟨140613832310960989851030985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187485109747947986468041313 140613832310960989851030985)
  ·
    refine ⟨105460374233220742388273239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140613832310960989851030985 105460374233220742388273239)
    ·
      refine ⟨158190561349831113582409859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105460374233220742388273239 158190561349831113582409859)
      ·
        refine ⟨237285842024746670373614789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158190561349831113582409859 237285842024746670373614789)
        ·
          refine ⟨44491095379640000695052773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237285842024746670373614789 44491095379640000695052773)
          ·
            refine ⟨8342080383682500130322395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44491095379640000695052773 8342080383682500130322395)
            ·
              refine ⟨12513120575523750195483593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8342080383682500130322395 12513120575523750195483593)
              ·
                refine ⟨9384840431642812646612695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12513120575523750195483593 9384840431642812646612695)
                ·
                  refine ⟨14077260647464218969919043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9384840431642812646612695 14077260647464218969919043)
                  ·
                    refine ⟨21115890971196328454878565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14077260647464218969919043 21115890971196328454878565)
                    ·
                      refine ⟨3959229557099311585289731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21115890971196328454878565 3959229557099311585289731)
                      ·
                        rfl

theorem cell23_7710572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_7710572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710572 prefixEnd_7710572 := by exact prefixLift 7710572
  have htrace : WordTrace (prefixWord ++ tailWord_7710572) baseStart_7710572 baseEnd_7710572 := by
    simpa [prefixWord, tailWord_7710572, baseEnd_7710572] using wordTrace_append hprefix tailTrace_7710572
  have hstable : (prefixWord ++ tailWord_7710572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710572).length < 2 ^ (prefixWord ++ tailWord_7710572).sum := by decide
  have hdescent : baseEnd_7710572 < baseStart_7710572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710582 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_7710582 : Nat := 118140960795 + 7710582 * 2 ^ 59
def prefixEnd_7710582 : Nat := 4983230072969 + 3 ^ 40 * 7710582 * 2
def baseEnd_7710582 : Nat := 1319744897301952182054895

theorem tailTrace_7710582 : CollatzResearch.WordTrace tailWord_7710582 prefixEnd_7710582 1319744897301952182054895 := by
  unfold tailWord_7710582
  simp only [CollatzResearch.WordTrace]
  refine ⟨17576751834492859463120375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187485352901257167606617333 17576751834492859463120375)
  ·
    refine ⟨26365127751739289194680563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17576751834492859463120375 26365127751739289194680563)
    ·
      refine ⟨39547691627608933792020845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26365127751739289194680563 39547691627608933792020845)
      ·
        refine ⟨14830384360353350172007817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39547691627608933792020845 14830384360353350172007817)
        ·
          refine ⟨11122788270265012629005863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14830384360353350172007817 11122788270265012629005863)
          ·
            refine ⟨16684182405397518943508795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11122788270265012629005863 16684182405397518943508795)
            ·
              refine ⟨25026273608096278415263193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16684182405397518943508795 25026273608096278415263193)
              ·
                refine ⟨18769705206072208811447395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25026273608096278415263193 18769705206072208811447395)
                ·
                  refine ⟨28154557809108313217171093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18769705206072208811447395 28154557809108313217171093)
                  ·
                    refine ⟨1319744897301952182054895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28154557809108313217171093 1319744897301952182054895)
                    ·
                      rfl

theorem cell23_7710582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_7710582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710582 prefixEnd_7710582 := by exact prefixLift 7710582
  have htrace : WordTrace (prefixWord ++ tailWord_7710582) baseStart_7710582 baseEnd_7710582 := by
    simpa [prefixWord, tailWord_7710582, baseEnd_7710582] using wordTrace_append hprefix tailTrace_7710582
  have hstable : (prefixWord ++ tailWord_7710582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710582).length < 2 ^ (prefixWord ++ tailWord_7710582).sum := by decide
  have hdescent : baseEnd_7710582 < baseStart_7710582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710589 : List Nat := [1, 4, 1, 1, 2, 1, 1, 7, 1, 2, 2]
def baseStart_7710589 : Nat := 118140960795 + 7710589 * 2 ^ 59
def prefixEnd_7710589 : Nat := 4983230072969 + 3 ^ 40 * 7710589 * 2
def baseEnd_7710589 : Nat := 3959238286270438018777153

theorem tailTrace_7710589 : CollatzResearch.WordTrace tailWord_7710589 prefixEnd_7710589 3959238286270438018777153 := by
  unfold tailWord_7710589
  simp only [CollatzResearch.WordTrace]
  refine ⟨281228284662860391605430821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187485523108573594403620547 281228284662860391605430821)
  ·
    refine ⟨52730303374286323426018279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281228284662860391605430821 52730303374286323426018279)
    ·
      refine ⟨79095455061429485139027419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52730303374286323426018279 79095455061429485139027419)
      ·
        refine ⟨118643182592144227708541129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79095455061429485139027419 118643182592144227708541129)
        ·
          refine ⟨88982386944108170781405847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118643182592144227708541129 88982386944108170781405847)
          ·
            refine ⟨133473580416162256172108771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88982386944108170781405847 133473580416162256172108771)
            ·
              refine ⟨200210370624243384258163157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133473580416162256172108771 200210370624243384258163157)
              ·
                refine ⟨4692430561505704318550699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 200210370624243384258163157 4692430561505704318550699)
                ·
                  refine ⟨7038645842258556477826049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692430561505704318550699 7038645842258556477826049)
                  ·
                    refine ⟨5278984381693917358369537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7038645842258556477826049 5278984381693917358369537)
                    ·
                      refine ⟨3959238286270438018777153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5278984381693917358369537 3959238286270438018777153)
                      ·
                        rfl

theorem cell23_7710589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_7710589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710589 prefixEnd_7710589 := by exact prefixLift 7710589
  have htrace : WordTrace (prefixWord ++ tailWord_7710589) baseStart_7710589 baseEnd_7710589 := by
    simpa [prefixWord, tailWord_7710589, baseEnd_7710589] using wordTrace_append hprefix tailTrace_7710589
  have hstable : (prefixWord ++ tailWord_7710589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710589).length < 2 ^ (prefixWord ++ tailWord_7710589).sum := by decide
  have hdescent : baseEnd_7710589 < baseStart_7710589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710592 : List Nat := [2, 1, 1, 2, 1, 2, 7, 1, 1, 2, 3]
def baseStart_7710592 : Nat := 118140960795 + 7710592 * 2 ^ 59
def prefixEnd_7710592 : Nat := 4983230072969 + 3 ^ 40 * 7710592 * 2
def baseEnd_7710592 : Nat := 3959239826712401507039639

theorem tailTrace_7710592 : CollatzResearch.WordTrace tailWord_7710592 prefixEnd_7710592 3959239826712401507039639 := by
  unfold tailWord_7710592
  simp only [CollatzResearch.WordTrace]
  refine ⟨140614197040924761558895015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187485596054566348745193353 140614197040924761558895015)
  ·
    refine ⟨210921295561387142338342523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140614197040924761558895015 210921295561387142338342523)
    ·
      refine ⟨316381943342080713507513785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210921295561387142338342523 316381943342080713507513785)
      ·
        refine ⟨237286457506560535130635339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316381943342080713507513785 237286457506560535130635339)
        ·
          refine ⟨355929686259840802695953009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237286457506560535130635339 355929686259840802695953009)
          ·
            refine ⟨266947264694880602021964757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355929686259840802695953009 266947264694880602021964757)
            ·
              refine ⟨6256576516286264109889799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 266947264694880602021964757 6256576516286264109889799)
              ·
                refine ⟨9384864774429396164834699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6256576516286264109889799 9384864774429396164834699)
                ·
                  refine ⟨14077297161644094247252049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9384864774429396164834699 14077297161644094247252049)
                  ·
                    refine ⟨10557972871233070685439037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14077297161644094247252049 10557972871233070685439037)
                    ·
                      refine ⟨3959239826712401507039639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10557972871233070685439037 3959239826712401507039639)
                      ·
                        rfl

theorem cell23_7710592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 1, 2, 3].length) (baseStart_7710592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710592 prefixEnd_7710592 := by exact prefixLift 7710592
  have htrace : WordTrace (prefixWord ++ tailWord_7710592) baseStart_7710592 baseEnd_7710592 := by
    simpa [prefixWord, tailWord_7710592, baseEnd_7710592] using wordTrace_append hprefix tailTrace_7710592
  have hstable : (prefixWord ++ tailWord_7710592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710592).length < 2 ^ (prefixWord ++ tailWord_7710592).sum := by decide
  have hdescent : baseEnd_7710592 < baseStart_7710592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710648 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_7710648 : Nat := 118140960795 + 7710648 * 2 ^ 59
def prefixEnd_7710648 : Nat := 4983230072969 + 3 ^ 40 * 7710648 * 2
def baseEnd_7710648 : Nat := 3959268581629053287939381

theorem tailTrace_7710648 : CollatzResearch.WordTrace tailWord_7710648 prefixEnd_7710648 3959268581629053287939381 := by
  unfold tailWord_7710648
  simp only [CollatzResearch.WordTrace]
  refine ⟨140615218284823322340914299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187486957713097763121219065 140615218284823322340914299)
  ·
    refine ⟨210922827427234983511371449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140615218284823322340914299 210922827427234983511371449)
    ·
      refine ⟨158192120570426237633528587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210922827427234983511371449 158192120570426237633528587)
      ·
        refine ⟨237288180855639356450292881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158192120570426237633528587 237288180855639356450292881)
        ·
          refine ⟨177966135641729517337719661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237288180855639356450292881 177966135641729517337719661)
          ·
            refine ⟨66737300865648569001644873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177966135641729517337719661 66737300865648569001644873)
            ·
              refine ⟨50052975649236426751233655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66737300865648569001644873 50052975649236426751233655)
              ·
                refine ⟨75079463473854640126850483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50052975649236426751233655 75079463473854640126850483)
                ·
                  refine ⟨112619195210781960190275725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75079463473854640126850483 112619195210781960190275725)
                  ·
                    refine ⟨42232198204043235071353397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112619195210781960190275725 42232198204043235071353397)
                    ·
                      refine ⟨3959268581629053287939381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42232198204043235071353397 3959268581629053287939381)
                      ·
                        rfl

theorem cell23_7710648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_7710648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710648 prefixEnd_7710648 := by exact prefixLift 7710648
  have htrace : WordTrace (prefixWord ++ tailWord_7710648) baseStart_7710648 baseEnd_7710648 := by
    simpa [prefixWord, tailWord_7710648, baseEnd_7710648] using wordTrace_append hprefix tailTrace_7710648
  have hstable : (prefixWord ++ tailWord_7710648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710648).length < 2 ^ (prefixWord ++ tailWord_7710648).sum := by decide
  have hdescent : baseEnd_7710648 < baseStart_7710648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710725 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_7710725 : Nat := 118140960795 + 7710725 * 2 ^ 59
def prefixEnd_7710725 : Nat := 4983230072969 + 3 ^ 40 * 7710725 * 2
def baseEnd_7710725 : Nat := 3959308119639449486676527

theorem tailTrace_7710725 : CollatzResearch.WordTrace tailWord_7710725 prefixEnd_7710725 3959308119639449486676527 := by
  unfold tailWord_7710725
  simp only [CollatzResearch.WordTrace]
  refine ⟨281233244990367686832381629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187488829993578457888254419 281233244990367686832381629)
  ·
    refine ⟨105462466871387882562143111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281233244990367686832381629 105462466871387882562143111)
    ·
      refine ⟨158193700307081823843214667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105462466871387882562143111 158193700307081823843214667)
      ·
        refine ⟨237290550460622735764822001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158193700307081823843214667 237290550460622735764822001)
        ·
          refine ⟨177967912845467051823616501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237290550460622735764822001 177967912845467051823616501)
          ·
            refine ⟨16684491829262536108464047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177967912845467051823616501 16684491829262536108464047)
            ·
              refine ⟨25026737743893804162696071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16684491829262536108464047 25026737743893804162696071)
              ·
                refine ⟨37540106615840706244044107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25026737743893804162696071 37540106615840706244044107)
                ·
                  refine ⟨56310159923761059366066161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37540106615840706244044107 56310159923761059366066161)
                  ·
                    refine ⟨42232619942820794524549621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56310159923761059366066161 42232619942820794524549621)
                    ·
                      refine ⟨3959308119639449486676527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42232619942820794524549621 3959308119639449486676527)
                      ·
                        rfl

theorem cell23_7710725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_7710725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710725 prefixEnd_7710725 := by exact prefixLift 7710725
  have htrace : WordTrace (prefixWord ++ tailWord_7710725) baseStart_7710725 baseEnd_7710725 := by
    simpa [prefixWord, tailWord_7710725, baseEnd_7710725] using wordTrace_append hprefix tailTrace_7710725
  have hstable : (prefixWord ++ tailWord_7710725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710725).length < 2 ^ (prefixWord ++ tailWord_7710725).sum := by decide
  have hdescent : baseEnd_7710725 < baseStart_7710725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710730 : List Nat := [3, 1, 2, 2, 5, 1, 2, 1, 2, 2, 2]
def baseStart_7710730 : Nat := 118140960795 + 7710730 * 2 ^ 59
def prefixEnd_7710730 : Nat := 4983230072969 + 3 ^ 40 * 7710730 * 2
def baseEnd_7710730 : Nat := 3959310687042721967114005

theorem tailTrace_7710730 : CollatzResearch.WordTrace tailWord_7710730 prefixEnd_7710730 3959310687042721967114005 := by
  unfold tailWord_7710730
  simp only [CollatzResearch.WordTrace]
  refine ⟨70308356838837393171578411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187488951570233048457542429 70308356838837393171578411)
  ·
    refine ⟨105462535258256089757367617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70308356838837393171578411 105462535258256089757367617)
    ·
      refine ⟨79096901443692067318025713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105462535258256089757367617 79096901443692067318025713)
      ·
        refine ⟨59322676082769050488519285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79096901443692067318025713 59322676082769050488519285)
        ·
          refine ⟨5561500882759598483298683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59322676082769050488519285 5561500882759598483298683)
          ·
            refine ⟨8342251324139397724948025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5561500882759598483298683 8342251324139397724948025)
            ·
              refine ⟨6256688493104548293711019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8342251324139397724948025 6256688493104548293711019)
              ·
                refine ⟨9385032739656822440566529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6256688493104548293711019 9385032739656822440566529)
                ·
                  refine ⟨7038774554742616830424897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9385032739656822440566529 7038774554742616830424897)
                  ·
                    refine ⟨5279080916056962622818673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7038774554742616830424897 5279080916056962622818673)
                    ·
                      refine ⟨3959310687042721967114005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5279080916056962622818673 3959310687042721967114005)
                      ·
                        rfl

theorem cell23_7710730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_7710730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710730 prefixEnd_7710730 := by exact prefixLift 7710730
  have htrace : WordTrace (prefixWord ++ tailWord_7710730) baseStart_7710730 baseEnd_7710730 := by
    simpa [prefixWord, tailWord_7710730, baseEnd_7710730] using wordTrace_append hprefix tailTrace_7710730
  have hstable : (prefixWord ++ tailWord_7710730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710730).length < 2 ^ (prefixWord ++ tailWord_7710730).sum := by decide
  have hdescent : baseEnd_7710730 < baseStart_7710730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710745 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 5, 4]
def baseStart_7710745 : Nat := 118140960795 + 7710745 * 2 ^ 59
def prefixEnd_7710745 : Nat := 4983230072969 + 3 ^ 40 * 7710745 * 2
def baseEnd_7710745 : Nat := 1319772796417513136142145

theorem tailTrace_7710745 : CollatzResearch.WordTrace tailWord_7710745 prefixEnd_7710745 1319772796417513136142145 := by
  unfold tailWord_7710745
  simp only [CollatzResearch.WordTrace]
  refine ⟨281233974450295230248109689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187489316300196820165406459 281233974450295230248109689)
  ·
    refine ⟨210925480837721422686082267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281233974450295230248109689 210925480837721422686082267)
    ·
      refine ⟨316388221256582134029123401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210925480837721422686082267 316388221256582134029123401)
      ·
        refine ⟨237291165942436600521842551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316388221256582134029123401 237291165942436600521842551)
        ·
          refine ⟨355936748913654900782763827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237291165942436600521842551 355936748913654900782763827)
          ·
            refine ⟨533905123370482351174145741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355936748913654900782763827 533905123370482351174145741)
            ·
              refine ⟨200214421263930881690304653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 533905123370482351174145741 200214421263930881690304653)
              ·
                refine ⟨75080407973974080633864245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200214421263930881690304653 75080407973974080633864245)
                ·
                  refine ⟨7038788247560070059424773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75080407973974080633864245 7038788247560070059424773)
                  ·
                    refine ⟨1319772796417513136142145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7038788247560070059424773 1319772796417513136142145)
                    ·
                      rfl

theorem cell23_7710745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 4].length) (baseStart_7710745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710745 prefixEnd_7710745 := by exact prefixLift 7710745
  have htrace : WordTrace (prefixWord ++ tailWord_7710745) baseStart_7710745 baseEnd_7710745 := by
    simpa [prefixWord, tailWord_7710745, baseEnd_7710745] using wordTrace_append hprefix tailTrace_7710745
  have hstable : (prefixWord ++ tailWord_7710745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710745).length < 2 ^ (prefixWord ++ tailWord_7710745).sum := by decide
  have hdescent : baseEnd_7710745 < baseStart_7710745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710775 : List Nat := [1, 1, 3, 1, 2, 2, 3, 4, 6]
def baseStart_7710775 : Nat := 118140960795 + 7710775 * 2 ^ 59
def prefixEnd_7710775 : Nat := 4983230072969 + 3 ^ 40 * 7710775 * 2
def baseEnd_7710775 : Nat := 439925977074686032339033

theorem tailTrace_7710775 : CollatzResearch.WordTrace tailWord_7710775 prefixEnd_7710775 439925977074686032339033 := by
  unfold tailWord_7710775
  simp only [CollatzResearch.WordTrace]
  refine ⟨281235068640186545371701779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187490045760124363581134519 281235068640186545371701779)
  ·
    refine ⟨421852602960279818057552669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281235068640186545371701779 421852602960279818057552669)
    ·
      refine ⟨158194726110104931771582251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421852602960279818057552669 158194726110104931771582251)
      ·
        refine ⟨237292089165157397657373377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158194726110104931771582251 237292089165157397657373377)
        ·
          refine ⟨177969066873868048243030033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237292089165157397657373377 177969066873868048243030033)
          ·
            refine ⟨133476800155401036182272525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177969066873868048243030033 133476800155401036182272525)
            ·
              refine ⟨50053800058275388568352197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133476800155401036182272525 50053800058275388568352197)
              ·
                refine ⟨9385087510926635356566037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50053800058275388568352197 9385087510926635356566037)
                ·
                  refine ⟨439925977074686032339033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9385087510926635356566037 439925977074686032339033)
                  ·
                    rfl

theorem cell23_7710775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 6].length) (baseStart_7710775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710775 prefixEnd_7710775 := by exact prefixLift 7710775
  have htrace : WordTrace (prefixWord ++ tailWord_7710775) baseStart_7710775 baseEnd_7710775 := by
    simpa [prefixWord, tailWord_7710775, baseEnd_7710775] using wordTrace_append hprefix tailTrace_7710775
  have hstable : (prefixWord ++ tailWord_7710775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710775).length < 2 ^ (prefixWord ++ tailWord_7710775).sum := by decide
  have hdescent : baseEnd_7710775 < baseStart_7710775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710806 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_7710806 : Nat := 118140960795 + 7710806 * 2 ^ 59
def prefixEnd_7710806 : Nat := 4983230072969 + 3 ^ 40 * 7710806 * 2
def baseEnd_7710806 : Nat := 3959349711572463669763655

theorem tailTrace_7710806 : CollatzResearch.WordTrace tailWord_7710806 prefixEnd_7710806 3959349711572463669763655 := by
  unfold tailWord_7710806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17577262456442139854130017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187490799535382825110720181 17577262456442139854130017)
  ·
    refine ⟨13182946842331604890597513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17577262456442139854130017 13182946842331604890597513)
    ·
      refine ⟨9887210131748703667948135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13182946842331604890597513 9887210131748703667948135)
      ·
        refine ⟨14830815197623055501922203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9887210131748703667948135 14830815197623055501922203)
        ·
          refine ⟨22246222796434583252883305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14830815197623055501922203 22246222796434583252883305)
          ·
            refine ⟨16684667097325937439662479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22246222796434583252883305 16684667097325937439662479)
            ·
              refine ⟨25027000645988906159493719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16684667097325937439662479 25027000645988906159493719)
              ·
                refine ⟨37540500968983359239240579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25027000645988906159493719 37540500968983359239240579)
                ·
                  refine ⟨56310751453475038858860869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37540500968983359239240579 56310751453475038858860869)
                  ·
                    refine ⟨10558265897526569786036413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56310751453475038858860869 10558265897526569786036413)
                    ·
                      refine ⟨3959349711572463669763655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10558265897526569786036413 3959349711572463669763655)
                      ·
                        rfl

theorem cell23_7710806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_7710806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710806 prefixEnd_7710806 := by exact prefixLift 7710806
  have htrace : WordTrace (prefixWord ++ tailWord_7710806) baseStart_7710806 baseEnd_7710806 := by
    simpa [prefixWord, tailWord_7710806, baseEnd_7710806] using wordTrace_append hprefix tailTrace_7710806
  have hstable : (prefixWord ++ tailWord_7710806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710806).length < 2 ^ (prefixWord ++ tailWord_7710806).sum := by decide
  have hdescent : baseEnd_7710806 < baseStart_7710806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710813 : List Nat := [1, 4, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7710813 : Nat := 118140960795 + 7710813 * 2 ^ 59
def prefixEnd_7710813 : Nat := 4983230072969 + 3 ^ 40 * 7710813 * 2
def baseEnd_7710813 : Nat := 1319784435312348380792041

theorem tailTrace_7710813 : CollatzResearch.WordTrace tailWord_7710813 prefixEnd_7710813 1319784435312348380792041 := by
  unfold tailWord_7710813
  simp only [CollatzResearch.WordTrace]
  refine ⟨281236454614048877861585093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187490969742699251907723395 281236454614048877861585093)
  ·
    refine ⟨52731835240134164599047205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281236454614048877861585093 52731835240134164599047205)
    ·
      refine ⟨9887219107525155862321351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52731835240134164599047205 9887219107525155862321351)
      ·
        refine ⟨14830828661287733793482027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9887219107525155862321351 14830828661287733793482027)
        ·
          refine ⟨22246242991931600690223041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14830828661287733793482027 22246242991931600690223041)
          ·
            refine ⟨16684682243948700517667281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22246242991931600690223041 16684682243948700517667281)
            ·
              refine ⟨12513511682961525388250461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16684682243948700517667281 12513511682961525388250461)
              ·
                refine ⟨4692566881110572020593923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12513511682961525388250461 4692566881110572020593923)
                ·
                  refine ⟨7038850321665858030890885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692566881110572020593923 7038850321665858030890885)
                  ·
                    refine ⟨1319784435312348380792041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7038850321665858030890885 1319784435312348380792041)
                    ·
                      rfl

theorem cell23_7710813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7710813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710813 prefixEnd_7710813 := by exact prefixLift 7710813
  have htrace : WordTrace (prefixWord ++ tailWord_7710813) baseStart_7710813 baseEnd_7710813 := by
    simpa [prefixWord, tailWord_7710813, baseEnd_7710813] using wordTrace_append hprefix tailTrace_7710813
  have hstable : (prefixWord ++ tailWord_7710813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710813).length < 2 ^ (prefixWord ++ tailWord_7710813).sum := by decide
  have hdescent : baseEnd_7710813 < baseStart_7710813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710826 : List Nat := [3, 1, 3, 2, 4, 1, 1, 2, 6]
def baseStart_7710826 : Nat := 118140960795 + 7710826 * 2 ^ 59
def prefixEnd_7710826 : Nat := 4983230072969 + 3 ^ 40 * 7710826 * 2
def baseEnd_7710826 : Nat := 439928886798394843501507

theorem tailTrace_7710826 : CollatzResearch.WordTrace tailWord_7710826 prefixEnd_7710826 439928886798394843501507 := by
  unfold tailWord_7710826
  simp only [CollatzResearch.WordTrace]
  refine ⟨70309232190750445270452083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187491285842001187387872221 70309232190750445270452083)
  ·
    refine ⟨105463848286125667905678125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70309232190750445270452083 105463848286125667905678125)
    ·
      refine ⟨39548943107297125464629297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105463848286125667905678125 39548943107297125464629297)
      ·
        refine ⟨29661707330472844098471973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39548943107297125464629297 29661707330472844098471973)
        ·
          refine ⟨5561570124463658268463495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29661707330472844098471973 5561570124463658268463495)
          ·
            refine ⟨8342355186695487402695243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5561570124463658268463495 8342355186695487402695243)
            ·
              refine ⟨12513532780043231104042865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8342355186695487402695243 12513532780043231104042865)
              ·
                refine ⟨9385149585032423328032149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12513532780043231104042865 9385149585032423328032149)
                ·
                  refine ⟨439928886798394843501507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9385149585032423328032149 439928886798394843501507)
                  ·
                    rfl

theorem cell23_7710826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 6].length) (baseStart_7710826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710826 prefixEnd_7710826 := by exact prefixLift 7710826
  have htrace : WordTrace (prefixWord ++ tailWord_7710826) baseStart_7710826 baseEnd_7710826 := by
    simpa [prefixWord, tailWord_7710826, baseEnd_7710826] using wordTrace_append hprefix tailTrace_7710826
  have hstable : (prefixWord ++ tailWord_7710826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710826).length < 2 ^ (prefixWord ++ tailWord_7710826).sum := by decide
  have hdescent : baseEnd_7710826 < baseStart_7710826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710829 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_7710829 : Nat := 118140960795 + 7710829 * 2 ^ 59
def prefixEnd_7710829 : Nat := 4983230072969 + 3 ^ 40 * 7710829 * 2
def baseEnd_7710829 : Nat := 3959361521627517079776049

theorem tailTrace_7710829 : CollatzResearch.WordTrace tailWord_7710829 prefixEnd_7710829 3959361521627517079776049 := by
  unfold tailWord_7710829
  simp only [CollatzResearch.WordTrace]
  refine ⟨281237038181990912594167541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187491358787993941729445027 281237038181990912594167541)
  ·
    refine ⟨26365972329561648055703207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281237038181990912594167541 26365972329561648055703207)
    ·
      refine ⟨39548958494342472083554811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26365972329561648055703207 39548958494342472083554811)
      ·
        refine ⟨59323437741513708125332217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39548958494342472083554811 59323437741513708125332217)
        ·
          refine ⟨44492578306135281093999163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59323437741513708125332217 44492578306135281093999163)
          ·
            refine ⟨66738867459202921640998745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44492578306135281093999163 66738867459202921640998745)
            ·
              refine ⟨50054150594402191230749059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66738867459202921640998745 50054150594402191230749059)
              ·
                refine ⟨75081225891603286846123589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50054150594402191230749059 75081225891603286846123589)
                ·
                  refine ⟨14077729854675616283648173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75081225891603286846123589 14077729854675616283648173)
                  ·
                    refine ⟨5279148695503356106368065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14077729854675616283648173 5279148695503356106368065)
                    ·
                      refine ⟨3959361521627517079776049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5279148695503356106368065 3959361521627517079776049)
                      ·
                        rfl

theorem cell23_7710829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_7710829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710829 prefixEnd_7710829 := by exact prefixLift 7710829
  have htrace : WordTrace (prefixWord ++ tailWord_7710829) baseStart_7710829 baseEnd_7710829 := by
    simpa [prefixWord, tailWord_7710829, baseEnd_7710829] using wordTrace_append hprefix tailTrace_7710829
  have hstable : (prefixWord ++ tailWord_7710829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710829).length < 2 ^ (prefixWord ++ tailWord_7710829).sum := by decide
  have hdescent : baseEnd_7710829 < baseStart_7710829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710879 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 5]
def baseStart_7710879 : Nat := 118140960795 + 7710879 * 2 ^ 59
def prefixEnd_7710879 : Nat := 4983230072969 + 3 ^ 40 * 7710879 * 2
def baseEnd_7710879 : Nat := 3959387195660241884150819

theorem tailTrace_7710879 : CollatzResearch.WordTrace tailWord_7710879 prefixEnd_7710879 3959387195660241884150819 := by
  unfold tailWord_7710879
  simp only [CollatzResearch.WordTrace]
  refine ⟨281238861831809771133487691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187492574554539847422325127 281238861831809771133487691)
  ·
    refine ⟨421858292747714656700231537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281238861831809771133487691 421858292747714656700231537)
    ·
      refine ⟨316393719560785992525173653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421858292747714656700231537 316393719560785992525173653)
      ·
        refine ⟨14830955604411843399617515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 316393719560785992525173653 14830955604411843399617515)
        ·
          refine ⟨22246433406617765099426273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14830955604411843399617515 22246433406617765099426273)
          ·
            refine ⟨16684825054963323824569705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22246433406617765099426273 16684825054963323824569705)
            ·
              refine ⟨12513618791222492868427279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16684825054963323824569705 12513618791222492868427279)
              ·
                refine ⟨18770428186833739302640919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12513618791222492868427279 18770428186833739302640919)
                ·
                  refine ⟨28155642280250608953961379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18770428186833739302640919 28155642280250608953961379)
                  ·
                    refine ⟨42233463420375913430942069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28155642280250608953961379 42233463420375913430942069)
                    ·
                      refine ⟨3959387195660241884150819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42233463420375913430942069 3959387195660241884150819)
                      ·
                        rfl

theorem cell23_7710879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_7710879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710879 prefixEnd_7710879 := by exact prefixLift 7710879
  have htrace : WordTrace (prefixWord ++ tailWord_7710879) baseStart_7710879 baseEnd_7710879 := by
    simpa [prefixWord, tailWord_7710879, baseEnd_7710879] using wordTrace_append hprefix tailTrace_7710879
  have hstable : (prefixWord ++ tailWord_7710879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710879).length < 2 ^ (prefixWord ++ tailWord_7710879).sum := by decide
  have hdescent : baseEnd_7710879 < baseStart_7710879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710882 : List Nat := [3, 3, 1, 3, 1, 1, 11]
def baseStart_7710882 : Nat := 118140960795 + 7710882 * 2 ^ 59
def prefixEnd_7710882 : Nat := 4983230072969 + 3 ^ 40 * 7710882 * 2
def baseEnd_7710882 : Nat := 48881342421014881140905

theorem tailTrace_7710882 : CollatzResearch.WordTrace tailWord_7710882 prefixEnd_7710882 48881342421014881140905 := by
  unfold tailWord_7710882
  simp only [CollatzResearch.WordTrace]
  refine ⟨70309742812699725661461725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187492647500532601763897933 70309742812699725661461725)
  ·
    refine ⟨26366153554762397123048147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70309742812699725661461725 26366153554762397123048147)
    ·
      refine ⟨39549230332143595684572221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26366153554762397123048147 39549230332143595684572221)
      ·
        refine ⟨14830961374553848381714583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39549230332143595684572221 14830961374553848381714583)
        ·
          refine ⟨22246442061830772572571875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14830961374553848381714583 22246442061830772572571875)
          ·
            refine ⟨33369663092746158858857813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22246442061830772572571875 33369663092746158858857813)
            ·
              refine ⟨48881342421014881140905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33369663092746158858857813 48881342421014881140905)
              ·
                rfl

theorem cell23_7710882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 11].length) (baseStart_7710882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710882 prefixEnd_7710882 := by exact prefixLift 7710882
  have htrace : WordTrace (prefixWord ++ tailWord_7710882) baseStart_7710882 baseEnd_7710882 := by
    simpa [prefixWord, tailWord_7710882, baseEnd_7710882] using wordTrace_append hprefix tailTrace_7710882
  have hstable : (prefixWord ++ tailWord_7710882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710882).length < 2 ^ (prefixWord ++ tailWord_7710882).sum := by decide
  have hdescent : baseEnd_7710882 < baseStart_7710882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710893 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_7710893 : Nat := 118140960795 + 7710893 * 2 ^ 59
def prefixEnd_7710893 : Nat := 4983230072969 + 3 ^ 40 * 7710893 * 2
def baseEnd_7710893 : Nat := 3959394384389404829375755

theorem tailTrace_7710893 : CollatzResearch.WordTrace tailWord_7710893 prefixEnd_7710893 3959394384389404829375755 := by
  unfold tailWord_7710893
  simp only [CollatzResearch.WordTrace]
  refine ⟨281239372453759051524497333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187492914969172701016331555 281239372453759051524497333)
  ·
    refine ⟨26366191167539911080421625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281239372453759051524497333 26366191167539911080421625)
    ·
      refine ⟨19774643375654933310316219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26366191167539911080421625 19774643375654933310316219)
      ·
        refine ⟨29661965063482399965474329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19774643375654933310316219 29661965063482399965474329)
        ·
          refine ⟨22246473797611799974105747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29661965063482399965474329 22246473797611799974105747)
          ·
            refine ⟨33369710696417699961158621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22246473797611799974105747 33369710696417699961158621)
            ·
              refine ⟨12513641511156637485434483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33369710696417699961158621 12513641511156637485434483)
              ·
                refine ⟨18770462266734956228151725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12513641511156637485434483 18770462266734956228151725)
                ·
                  refine ⟨7038923350025608585556897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18770462266734956228151725 7038923350025608585556897)
                  ·
                    refine ⟨5279192512519206439167673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7038923350025608585556897 5279192512519206439167673)
                    ·
                      refine ⟨3959394384389404829375755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5279192512519206439167673 3959394384389404829375755)
                      ·
                        rfl

theorem cell23_7710893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_7710893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710893 prefixEnd_7710893 := by exact prefixLift 7710893
  have htrace : WordTrace (prefixWord ++ tailWord_7710893) baseStart_7710893 baseEnd_7710893 := by
    simpa [prefixWord, tailWord_7710893, baseEnd_7710893] using wordTrace_append hprefix tailTrace_7710893
  have hstable : (prefixWord ++ tailWord_7710893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710893).length < 2 ^ (prefixWord ++ tailWord_7710893).sum := by decide
  have hdescent : baseEnd_7710893 < baseStart_7710893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710895 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 2, 7]
def baseStart_7710895 : Nat := 118140960795 + 7710895 * 2 ^ 59
def prefixEnd_7710895 : Nat := 4983230072969 + 3 ^ 40 * 7710895 * 2
def baseEnd_7710895 : Nat := 1319798470450237940516915

theorem tailTrace_7710895 : CollatzResearch.WordTrace tailWord_7710895 prefixEnd_7710895 1319798470450237940516915 := by
  unfold tailWord_7710895
  simp only [CollatzResearch.WordTrace]
  refine ⟨281239445399751805866070139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187492963599834537244046759 281239445399751805866070139)
  ·
    refine ⟨421859168099627708799105209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281239445399751805866070139 421859168099627708799105209)
    ·
      refine ⟨316394376074720781599328907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421859168099627708799105209 316394376074720781599328907)
      ·
        refine ⟨474591564112081172398993361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316394376074720781599328907 474591564112081172398993361)
        ·
          refine ⟨355943673084060879299245021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474591564112081172398993361 355943673084060879299245021)
          ·
            refine ⟨133478877406522829737216883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355943673084060879299245021 133478877406522829737216883)
            ·
              refine ⟨200218316109784244605825325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133478877406522829737216883 200218316109784244605825325)
              ·
                refine ⟨75081868541169091727184497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200218316109784244605825325 75081868541169091727184497)
                ·
                  refine ⟨56311401405876818795388373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75081868541169091727184497 56311401405876818795388373)
                  ·
                    refine ⟨1319798470450237940516915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56311401405876818795388373 1319798470450237940516915)
                    ·
                      rfl

theorem cell23_7710895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_7710895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710895 prefixEnd_7710895 := by exact prefixLift 7710895
  have htrace : WordTrace (prefixWord ++ tailWord_7710895) baseStart_7710895 baseEnd_7710895 := by
    simpa [prefixWord, tailWord_7710895, baseEnd_7710895] using wordTrace_append hprefix tailTrace_7710895
  have hstable : (prefixWord ++ tailWord_7710895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710895).length < 2 ^ (prefixWord ++ tailWord_7710895).sum := by decide
  have hdescent : baseEnd_7710895 < baseStart_7710895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710966 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_7710966 : Nat := 118140960795 + 7710966 * 2 ^ 59
def prefixEnd_7710966 : Nat := 4983230072969 + 3 ^ 40 * 7710966 * 2
def baseEnd_7710966 : Nat := 3959431868477183043762919

theorem tailTrace_7710966 : CollatzResearch.WordTrace tailWord_7710966 prefixEnd_7710966 3959431868477183043762919 := by
  unfold tailWord_7710966
  simp only [CollatzResearch.WordTrace]
  refine ⟨17577627186405911561994047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187494689988329723327936501 17577627186405911561994047)
  ·
    refine ⟨26366440779608867342991071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17577627186405911561994047 26366440779608867342991071)
    ·
      refine ⟨39549661169413301014486607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26366440779608867342991071 39549661169413301014486607)
      ·
        refine ⟨59324491754119951521729911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39549661169413301014486607 59324491754119951521729911)
        ·
          refine ⟨88986737631179927282594867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59324491754119951521729911 88986737631179927282594867)
          ·
            refine ⟨133480106446769890923892301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88986737631179927282594867 133480106446769890923892301)
            ·
              refine ⟨50055039917538709096459613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133480106446769890923892301 50055039917538709096459613)
              ·
                refine ⟨18770639969077015911172355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50055039917538709096459613 18770639969077015911172355)
                ·
                  refine ⟨28155959953615523866758533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18770639969077015911172355 28155959953615523866758533)
                  ·
                    refine ⟨5279242491302910725017225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28155959953615523866758533 5279242491302910725017225)
                    ·
                      refine ⟨3959431868477183043762919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5279242491302910725017225 3959431868477183043762919)
                      ·
                        rfl

theorem cell23_7710966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_7710966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710966 prefixEnd_7710966 := by exact prefixLift 7710966
  have htrace : WordTrace (prefixWord ++ tailWord_7710966) baseStart_7710966 baseEnd_7710966 := by
    simpa [prefixWord, tailWord_7710966, baseEnd_7710966] using wordTrace_append hprefix tailTrace_7710966
  have hstable : (prefixWord ++ tailWord_7710966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710966).length < 2 ^ (prefixWord ++ tailWord_7710966).sum := by decide
  have hdescent : baseEnd_7710966 < baseStart_7710966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710972 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 9]
def baseStart_7710972 : Nat := 118140960795 + 7710972 * 2 ^ 59
def prefixEnd_7710972 : Nat := 4983230072969 + 3 ^ 40 * 7710972 * 2
def baseEnd_7710972 : Nat := 439937216595678891143099

theorem tailTrace_7710972 : CollatzResearch.WordTrace tailWord_7710972 prefixEnd_7710972 439937216595678891143099 := by
  unfold tailWord_7710972
  simp only [CollatzResearch.WordTrace]
  refine ⟨140621126910236424008311585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187494835880315232011082113 140621126910236424008311585)
  ·
    refine ⟨105465845182677318006233689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140621126910236424008311585 105465845182677318006233689)
    ·
      refine ⟨79099383887007988504675267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105465845182677318006233689 79099383887007988504675267)
      ·
        refine ⟨118649075830511982757012901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79099383887007988504675267 118649075830511982757012901)
        ·
          refine ⟨22246701718220996766939919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118649075830511982757012901 22246701718220996766939919)
          ·
            refine ⟨33370052577331495150409879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22246701718220996766939919 33370052577331495150409879)
            ·
              refine ⟨50055078865997242725614819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33370052577331495150409879 50055078865997242725614819)
              ·
                refine ⟨75082618298995864088422229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50055078865997242725614819 75082618298995864088422229)
                ·
                  refine ⟨439937216595678891143099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75082618298995864088422229 439937216595678891143099)
                  ·
                    rfl

theorem cell23_7710972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_7710972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710972 prefixEnd_7710972 := by exact prefixLift 7710972
  have htrace : WordTrace (prefixWord ++ tailWord_7710972) baseStart_7710972 baseEnd_7710972 := by
    simpa [prefixWord, tailWord_7710972, baseEnd_7710972] using wordTrace_append hprefix tailTrace_7710972
  have hstable : (prefixWord ++ tailWord_7710972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710972).length < 2 ^ (prefixWord ++ tailWord_7710972).sum := by decide
  have hdescent : baseEnd_7710972 < baseStart_7710972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7710999 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 3]
def baseStart_7710999 : Nat := 118140960795 + 7710999 * 2 ^ 59
def prefixEnd_7710999 : Nat := 4983230072969 + 3 ^ 40 * 7710999 * 2
def baseEnd_7710999 : Nat := 3959448813338781414650267

theorem tailTrace_7710999 : CollatzResearch.WordTrace tailWord_7710999 prefixEnd_7710999 3959448813338781414650267 := by
  unfold tailWord_7710999
  simp only [CollatzResearch.WordTrace]
  refine ⟨281243238591375031627856051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187495492394250021085237367 281243238591375031627856051)
  ·
    refine ⟨421864857887062547441784077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281243238591375031627856051 421864857887062547441784077)
    ·
      refine ⟨158199321707648455290669029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421864857887062547441784077 158199321707648455290669029)
      ·
        refine ⟨29662372820184085367000443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158199321707648455290669029 29662372820184085367000443)
        ·
          refine ⟨44493559230276128050500665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29662372820184085367000443 44493559230276128050500665)
          ·
            refine ⟨33370169422707096037875499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44493559230276128050500665 33370169422707096037875499)
            ·
              refine ⟨50055254134060644056813249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33370169422707096037875499 50055254134060644056813249)
              ·
                refine ⟨37541440600545483042609937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50055254134060644056813249 37541440600545483042609937)
                ·
                  refine ⟨28156080450409112281957453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37541440600545483042609937 28156080450409112281957453)
                  ·
                    refine ⟨10558530168903417105734045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28156080450409112281957453 10558530168903417105734045)
                    ·
                      refine ⟨3959448813338781414650267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10558530168903417105734045 3959448813338781414650267)
                      ·
                        rfl

theorem cell23_7710999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_7710999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7710999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7710999 prefixEnd_7710999 := by exact prefixLift 7710999
  have htrace : WordTrace (prefixWord ++ tailWord_7710999) baseStart_7710999 baseEnd_7710999 := by
    simpa [prefixWord, tailWord_7710999, baseEnd_7710999] using wordTrace_append hprefix tailTrace_7710999
  have hstable : (prefixWord ++ tailWord_7710999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7710999).length < 2 ^ (prefixWord ++ tailWord_7710999).sum := by decide
  have hdescent : baseEnd_7710999 < baseStart_7710999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7710999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711006 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 7]
def baseStart_7711006 : Nat := 118140960795 + 7711006 * 2 ^ 59
def prefixEnd_7711006 : Nat := 4983230072969 + 3 ^ 40 * 7711006 * 2
def baseEnd_7711006 : Nat := 439939156411484765251415

theorem tailTrace_7711006 : CollatzResearch.WordTrace tailWord_7711006 prefixEnd_7711006 439939156411484765251415 := by
  unfold tailWord_7711006
  simp only [CollatzResearch.WordTrace]
  refine ⟨35155436737793708977920109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187495662601566447882240581 35155436737793708977920109)
  ·
    refine ⟨13183288776672640866720041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35155436737793708977920109 13183288776672640866720041)
    ·
      refine ⟨9887466582504480650040031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13183288776672640866720041 9887466582504480650040031)
      ·
        refine ⟨14831199873756720975060047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9887466582504480650040031 14831199873756720975060047)
        ·
          refine ⟨22246799810635081462590071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14831199873756720975060047 22246799810635081462590071)
          ·
            refine ⟨33370199715952622193885107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22246799810635081462590071 33370199715952622193885107)
            ·
              refine ⟨50055299573928933290827661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33370199715952622193885107 50055299573928933290827661)
              ·
                refine ⟨18770737340223349984060373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50055299573928933290827661 18770737340223349984060373)
                ·
                  refine ⟨439939156411484765251415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18770737340223349984060373 439939156411484765251415)
                  ·
                    rfl

theorem cell23_7711006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_7711006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711006 prefixEnd_7711006 := by exact prefixLift 7711006
  have htrace : WordTrace (prefixWord ++ tailWord_7711006) baseStart_7711006 baseEnd_7711006 := by
    simpa [prefixWord, tailWord_7711006, baseEnd_7711006] using wordTrace_append hprefix tailTrace_7711006
  have hstable : (prefixWord ++ tailWord_7711006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711006).length < 2 ^ (prefixWord ++ tailWord_7711006).sum := by decide
  have hdescent : baseEnd_7711006 < baseStart_7711006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711009 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 1, 7, 2]
def baseStart_7711009 : Nat := 118140960795 + 7711009 * 2 ^ 59
def prefixEnd_7711009 : Nat := 4983230072969 + 3 ^ 40 * 7711009 * 2
def baseEnd_7711009 : Nat := 3959453948145326375525221

theorem tailTrace_7711009 : CollatzResearch.WordTrace tailWord_7711009 prefixEnd_7711009 3959453948145326375525221 := by
  unfold tailWord_7711009
  simp only [CollatzResearch.WordTrace]
  refine ⟨281243603321338803335720081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187495735547559202223813387 281243603321338803335720081)
  ·
    refine ⟨210932702491004102501790061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281243603321338803335720081 210932702491004102501790061)
    ·
      refine ⟨79099763434126538438171273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210932702491004102501790061 79099763434126538438171273)
      ·
        refine ⟨59324822575594903828628455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79099763434126538438171273 59324822575594903828628455)
        ·
          refine ⟨88987233863392355742942683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59324822575594903828628455 88987233863392355742942683)
          ·
            refine ⟨133480850795088533614414025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88987233863392355742942683 133480850795088533614414025)
            ·
              refine ⟨100110638096316400210810519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133480850795088533614414025 100110638096316400210810519)
              ·
                refine ⟨150165957144474600316215779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100110638096316400210810519 150165957144474600316215779)
                ·
                  refine ⟨225248935716711900474323669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150165957144474600316215779 225248935716711900474323669)
                  ·
                    refine ⟨5279271930860435167366961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 225248935716711900474323669 5279271930860435167366961)
                    ·
                      refine ⟨3959453948145326375525221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5279271930860435167366961 3959453948145326375525221)
                      ·
                        rfl

theorem cell23_7711009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_7711009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711009 prefixEnd_7711009 := by exact prefixLift 7711009
  have htrace : WordTrace (prefixWord ++ tailWord_7711009) baseStart_7711009 baseEnd_7711009 := by
    simpa [prefixWord, tailWord_7711009, baseEnd_7711009] using wordTrace_append hprefix tailTrace_7711009
  have hstable : (prefixWord ++ tailWord_7711009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711009).length < 2 ^ (prefixWord ++ tailWord_7711009).sum := by decide
  have hdescent : baseEnd_7711009 < baseStart_7711009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711039 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 4]
def baseStart_7711039 : Nat := 118140960795 + 7711039 * 2 ^ 59
def prefixEnd_7711039 : Nat := 4983230072969 + 3 ^ 40 * 7711039 * 2
def baseEnd_7711039 : Nat := 3959469352564961258150083

theorem tailTrace_7711039 : CollatzResearch.WordTrace tailWord_7711039 prefixEnd_7711039 3959469352564961258150083 := by
  unfold tailWord_7711039
  simp only [CollatzResearch.WordTrace]
  refine ⟨281244697511230118459312171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187496465007486745639541447 281244697511230118459312171)
  ·
    refine ⟨421867046266845177688968257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281244697511230118459312171 421867046266845177688968257)
    ·
      refine ⟨316400284700133883266726193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421867046266845177688968257 316400284700133883266726193)
      ·
        refine ⟨237300213525100412450044645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316400284700133883266726193 237300213525100412450044645)
        ·
          refine ⟨44493790035956327334383371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237300213525100412450044645 44493790035956327334383371)
          ·
            refine ⟨66740685053934491001575057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44493790035956327334383371 66740685053934491001575057)
            ·
              refine ⟨50055513790450868251181293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66740685053934491001575057 50055513790450868251181293)
              ·
                refine ⟨18770817671419075594192985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50055513790450868251181293 18770817671419075594192985)
                ·
                  refine ⟨14078113253564306695644739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18770817671419075594192985 14078113253564306695644739)
                  ·
                    refine ⟨21117169880346460043467109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14078113253564306695644739 21117169880346460043467109)
                    ·
                      refine ⟨3959469352564961258150083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21117169880346460043467109 3959469352564961258150083)
                      ·
                        rfl

theorem cell23_7711039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_7711039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711039 prefixEnd_7711039 := by exact prefixLift 7711039
  have htrace : WordTrace (prefixWord ++ tailWord_7711039) baseStart_7711039 baseEnd_7711039 := by
    simpa [prefixWord, tailWord_7711039, baseEnd_7711039] using wordTrace_append hprefix tailTrace_7711039
  have hstable : (prefixWord ++ tailWord_7711039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711039).length < 2 ^ (prefixWord ++ tailWord_7711039).sum := by decide
  have hdescent : baseEnd_7711039 < baseStart_7711039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711093 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_7711093 : Nat := 118140960795 + 7711093 * 2 ^ 59
def prefixEnd_7711093 : Nat := 4983230072969 + 3 ^ 40 * 7711093 * 2
def baseEnd_7711093 : Nat := 3959497080520304046874835

theorem tailTrace_7711093 : CollatzResearch.WordTrace tailWord_7711093 prefixEnd_7711093 3959497080520304046874835 := by
  unfold tailWord_7711093
  simp only [CollatzResearch.WordTrace]
  refine ⟨281246667053034485681777933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187497778035356323787851955 281246667053034485681777933)
  ·
    refine ⟨105467500144887932130666725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281246667053034485681777933 105467500144887932130666725)
    ·
      refine ⟨19775156277166487274500011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105467500144887932130666725 19775156277166487274500011)
      ·
        refine ⟨29662734415749730911750017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19775156277166487274500011 29662734415749730911750017)
        ·
          refine ⟨22247050811812298183812513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29662734415749730911750017 22247050811812298183812513)
          ·
            refine ⟨16685288108859223637859385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22247050811812298183812513 16685288108859223637859385)
            ·
              refine ⟨12513966081644417728394539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16685288108859223637859385 12513966081644417728394539)
              ·
                refine ⟨18770949122466626592591809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12513966081644417728394539 18770949122466626592591809)
                ·
                  refine ⟨14078211841849969944443857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18770949122466626592591809 14078211841849969944443857)
                  ·
                    refine ⟨10558658881387477458332893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14078211841849969944443857 10558658881387477458332893)
                    ·
                      refine ⟨3959497080520304046874835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10558658881387477458332893 3959497080520304046874835)
                      ·
                        rfl

theorem cell23_7711093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_7711093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711093 prefixEnd_7711093 := by exact prefixLift 7711093
  have htrace : WordTrace (prefixWord ++ tailWord_7711093) baseStart_7711093 baseEnd_7711093 := by
    simpa [prefixWord, tailWord_7711093, baseEnd_7711093] using wordTrace_append hprefix tailTrace_7711093
  have hstable : (prefixWord ++ tailWord_7711093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711093).length < 2 ^ (prefixWord ++ tailWord_7711093).sum := by decide
  have hdescent : baseEnd_7711093 < baseStart_7711093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711129 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 5, 1, 4]
def baseStart_7711129 : Nat := 118140960795 + 7711129 * 2 ^ 59
def prefixEnd_7711129 : Nat := 4983230072969 + 3 ^ 40 * 7711129 * 2
def baseEnd_7711129 : Nat := 3959515565823865906024669

theorem tailTrace_7711129 : CollatzResearch.WordTrace tailWord_7711129 prefixEnd_7711129 3959515565823865906024669 := by
  unfold tailWord_7711129
  simp only [CollatzResearch.WordTrace]
  refine ⟨281247980080904063830088441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187498653387269375886725627 281247980080904063830088441)
  ·
    refine ⟨210935985060678047872566331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281247980080904063830088441 210935985060678047872566331)
    ·
      refine ⟨316403977591017071808849497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210935985060678047872566331 316403977591017071808849497)
      ·
        refine ⟨237302983193262803856637123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316403977591017071808849497 237302983193262803856637123)
        ·
          refine ⟨355954474789894205784955685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237302983193262803856637123 355954474789894205784955685)
          ·
            refine ⟨66741464023105163584679191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355954474789894205784955685 66741464023105163584679191)
            ·
              refine ⟨100112196034657745377018787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66741464023105163584679191 100112196034657745377018787)
              ·
                refine ⟨150168294051986618065528181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100112196034657745377018787 150168294051986618065528181)
                ·
                  refine ⟨14078277567373745443643267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150168294051986618065528181 14078277567373745443643267)
                  ·
                    refine ⟨21117416351060618165464901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14078277567373745443643267 21117416351060618165464901)
                    ·
                      refine ⟨3959515565823865906024669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21117416351060618165464901 3959515565823865906024669)
                      ·
                        rfl

theorem cell23_7711129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_7711129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711129 prefixEnd_7711129 := by exact prefixLift 7711129
  have htrace : WordTrace (prefixWord ++ tailWord_7711129) baseStart_7711129 baseEnd_7711129 := by
    simpa [prefixWord, tailWord_7711129, baseEnd_7711129] using wordTrace_append hprefix tailTrace_7711129
  have hstable : (prefixWord ++ tailWord_7711129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711129).length < 2 ^ (prefixWord ++ tailWord_7711129).sum := by decide
  have hdescent : baseEnd_7711129 < baseStart_7711129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711139 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 1, 6]
def baseStart_7711139 : Nat := 118140960795 + 7711139 * 2 ^ 59
def prefixEnd_7711139 : Nat := 4983230072969 + 3 ^ 40 * 7711139 * 2
def baseEnd_7711139 : Nat := 1319840233543470288966541

theorem tailTrace_7711139 : CollatzResearch.WordTrace tailWord_7711139 prefixEnd_7711139 1319840233543470288966541 := by
  unfold tailWord_7711139
  simp only [CollatzResearch.WordTrace]
  refine ⟨281248344810867835537952471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187498896540578557025301647 281248344810867835537952471)
  ·
    refine ⟨421872517216301753306928707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281248344810867835537952471 421872517216301753306928707)
    ·
      refine ⟨632808775824452629960393061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421872517216301753306928707 632808775824452629960393061)
      ·
        refine ⟨118651645467084868117573699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 632808775824452629960393061 118651645467084868117573699)
        ·
          refine ⟨177977468200627302176360549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118651645467084868117573699 177977468200627302176360549)
          ·
            refine ⟨33370775287617619158067603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177977468200627302176360549 33370775287617619158067603)
            ·
              refine ⟨50056162931426428737101405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33370775287617619158067603 50056162931426428737101405)
              ·
                refine ⟨18771061099284910776413027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50056162931426428737101405 18771061099284910776413027)
                ·
                  refine ⟨28156591648927366164619541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18771061099284910776413027 28156591648927366164619541)
                  ·
                    refine ⟨1319840233543470288966541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28156591648927366164619541 1319840233543470288966541)
                    ·
                      rfl

theorem cell23_7711139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 6].length) (baseStart_7711139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711139 prefixEnd_7711139 := by exact prefixLift 7711139
  have htrace : WordTrace (prefixWord ++ tailWord_7711139) baseStart_7711139 baseEnd_7711139 := by
    simpa [prefixWord, tailWord_7711139, baseEnd_7711139] using wordTrace_append hprefix tailTrace_7711139
  have hstable : (prefixWord ++ tailWord_7711139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711139).length < 2 ^ (prefixWord ++ tailWord_7711139).sum := by decide
  have hdescent : baseEnd_7711139 < baseStart_7711139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711157 : List Nat := [1, 3, 3, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_7711157 : Nat := 118140960795 + 7711157 * 2 ^ 59
def prefixEnd_7711157 : Nat := 4983230072969 + 3 ^ 40 * 7711157 * 2
def baseEnd_7711157 : Nat := 3959529943282191796474541

theorem tailTrace_7711157 : CollatzResearch.WordTrace tailWord_7711157 prefixEnd_7711157 3959529943282191796474541 := by
  unfold tailWord_7711157
  simp only [CollatzResearch.WordTrace]
  refine ⟨281249001324802624612107725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187499334216535083074738483 281249001324802624612107725)
  ·
    refine ⟨105468375496800984229540397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281249001324802624612107725 105468375496800984229540397)
    ·
      refine ⟨39550640811300369086077649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105468375496800984229540397 39550640811300369086077649)
      ·
        refine ⟨29662980608475276814558237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39550640811300369086077649 29662980608475276814558237)
        ·
          refine ⟨11123617728178228805459339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29662980608475276814558237 11123617728178228805459339)
          ·
            refine ⟨16685426592267343208189009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11123617728178228805459339 16685426592267343208189009)
            ·
              refine ⟨12514069944200507406141757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16685426592267343208189009 12514069944200507406141757)
              ·
                refine ⟨4692776229075190277303159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12514069944200507406141757 4692776229075190277303159)
                ·
                  refine ⟨7039164343612785415954739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692776229075190277303159 7039164343612785415954739)
                  ·
                    refine ⟨10558746515419178123932109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7039164343612785415954739 10558746515419178123932109)
                    ·
                      refine ⟨3959529943282191796474541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10558746515419178123932109 3959529943282191796474541)
                      ·
                        rfl

theorem cell23_7711157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_7711157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711157 prefixEnd_7711157 := by exact prefixLift 7711157
  have htrace : WordTrace (prefixWord ++ tailWord_7711157) baseStart_7711157 baseEnd_7711157 := by
    simpa [prefixWord, tailWord_7711157, baseEnd_7711157] using wordTrace_append hprefix tailTrace_7711157
  have hstable : (prefixWord ++ tailWord_7711157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711157).length < 2 ^ (prefixWord ++ tailWord_7711157).sum := by decide
  have hdescent : baseEnd_7711157 < baseStart_7711157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711203 : List Nat := [1, 1, 1, 6, 3, 2, 2, 7]
def baseStart_7711203 : Nat := 118140960795 + 7711203 * 2 ^ 59
def prefixEnd_7711203 : Nat := 4983230072969 + 3 ^ 40 * 7711203 * 2
def baseEnd_7711203 : Nat := 146650131977492541351827

theorem tailTrace_7711203 : CollatzResearch.WordTrace tailWord_7711203 prefixEnd_7711203 146650131977492541351827 := by
  unfold tailWord_7711203
  simp only [CollatzResearch.WordTrace]
  refine ⟨281250679082635974468282263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187500452721757316312188175 281250679082635974468282263)
  ·
    refine ⟨421876018623953961702423395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281250679082635974468282263 421876018623953961702423395)
    ·
      refine ⟨632814027935930942553635093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421876018623953961702423395 632814027935930942553635093)
      ·
        refine ⟨29663157559496762932201645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 632814027935930942553635093 29663157559496762932201645)
        ·
          refine ⟨11123684084811286099575617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29663157559496762932201645 11123684084811286099575617)
          ·
            refine ⟨8342763063608464574681713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11123684084811286099575617 8342763063608464574681713)
            ·
              refine ⟨6257072297706348431011285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8342763063608464574681713 6257072297706348431011285)
              ·
                refine ⟨146650131977492541351827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6257072297706348431011285 146650131977492541351827)
                ·
                  rfl

theorem cell23_7711203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 7].length) (baseStart_7711203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711203 prefixEnd_7711203 := by exact prefixLift 7711203
  have htrace : WordTrace (prefixWord ++ tailWord_7711203) baseStart_7711203 baseEnd_7711203 := by
    simpa [prefixWord, tailWord_7711203, baseEnd_7711203] using wordTrace_append hprefix tailTrace_7711203
  have hstable : (prefixWord ++ tailWord_7711203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711203).length < 2 ^ (prefixWord ++ tailWord_7711203).sum := by decide
  have hdescent : baseEnd_7711203 < baseStart_7711203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711214 : List Nat := [4, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_7711214 : Nat := 118140960795 + 7711214 * 2 ^ 59
def prefixEnd_7711214 : Nat := 4983230072969 + 3 ^ 40 * 7711214 * 2
def baseEnd_7711214 : Nat := 3959559211679498073461779

theorem tailTrace_7711214 : CollatzResearch.WordTrace tailWord_7711214 prefixEnd_7711214 3959559211679498073461779 := by
  unfold tailWord_7711214
  simp only [CollatzResearch.WordTrace]
  refine ⟨35156385035699515418366587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187500720190397415564621797 35156385035699515418366587)
  ·
    refine ⟨52734577553549273127549881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35156385035699515418366587 52734577553549273127549881)
    ·
      refine ⟨39550933165161954845662411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52734577553549273127549881 39550933165161954845662411)
      ·
        refine ⟨59326399747742932268493617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39550933165161954845662411 59326399747742932268493617)
        ·
          refine ⟨44494799810807199201370213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59326399747742932268493617 44494799810807199201370213)
          ·
            refine ⟨8342774964526349850256915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44494799810807199201370213 8342774964526349850256915)
            ·
              refine ⟨12514162446789524775385373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8342774964526349850256915 12514162446789524775385373)
              ·
                refine ⟨4692810917546071790769515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12514162446789524775385373 4692810917546071790769515)
                ·
                  refine ⟨7039216376319107686154273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692810917546071790769515 7039216376319107686154273)
                  ·
                    refine ⟨5279412282239330764615705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7039216376319107686154273 5279412282239330764615705)
                    ·
                      refine ⟨3959559211679498073461779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5279412282239330764615705 3959559211679498073461779)
                      ·
                        rfl

theorem cell23_7711214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_7711214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711214 prefixEnd_7711214 := by exact prefixLift 7711214
  have htrace : WordTrace (prefixWord ++ tailWord_7711214) baseStart_7711214 baseEnd_7711214 := by
    simpa [prefixWord, tailWord_7711214, baseEnd_7711214] using wordTrace_append hprefix tailTrace_7711214
  have hstable : (prefixWord ++ tailWord_7711214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711214).length < 2 ^ (prefixWord ++ tailWord_7711214).sum := by decide
  have hdescent : baseEnd_7711214 < baseStart_7711214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711253 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 1, 4, 2]
def baseStart_7711253 : Nat := 118140960795 + 7711253 * 2 ^ 59
def prefixEnd_7711253 : Nat := 4983230072969 + 3 ^ 40 * 7711253 * 2
def baseEnd_7711253 : Nat := 3959579237425023420874099

theorem tailTrace_7711253 : CollatzResearch.WordTrace tailWord_7711253 prefixEnd_7711253 3959579237425023420874099 := by
  unfold tailWord_7711253
  simp only [CollatzResearch.WordTrace]
  refine ⟨281252502732454833007602413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187501668488303222005068275 281252502732454833007602413)
  ·
    refine ⟨105469688524670562377850905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281252502732454833007602413 105469688524670562377850905)
    ·
      refine ⟨79102266393502921783388179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105469688524670562377850905 79102266393502921783388179)
      ·
        refine ⟨118653399590254382675082269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79102266393502921783388179 118653399590254382675082269)
        ·
          refine ⟨44495024846345393503155851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118653399590254382675082269 44495024846345393503155851)
          ·
            refine ⟨66742537269518090254733777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44495024846345393503155851 66742537269518090254733777)
            ·
              refine ⟨50056902952138567691050333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66742537269518090254733777 50056902952138567691050333)
              ·
                refine ⟨18771338607051962884143875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50056902952138567691050333 18771338607051962884143875)
                ·
                  refine ⟨28157007910577944326215813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18771338607051962884143875 28157007910577944326215813)
                  ·
                    refine ⟨5279438983233364561165465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28157007910577944326215813 5279438983233364561165465)
                    ·
                      refine ⟨3959579237425023420874099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5279438983233364561165465 3959579237425023420874099)
                      ·
                        rfl

theorem cell23_7711253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_7711253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711253 prefixEnd_7711253 := by exact prefixLift 7711253
  have htrace : WordTrace (prefixWord ++ tailWord_7711253) baseStart_7711253 baseEnd_7711253 := by
    simpa [prefixWord, tailWord_7711253, baseEnd_7711253] using wordTrace_append hprefix tailTrace_7711253
  have hstable : (prefixWord ++ tailWord_7711253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711253).length < 2 ^ (prefixWord ++ tailWord_7711253).sum := by decide
  have hdescent : baseEnd_7711253 < baseStart_7711253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711256 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_7711256 : Nat := 118140960795 + 7711256 * 2 ^ 59
def prefixEnd_7711256 : Nat := 4983230072969 + 3 ^ 40 * 7711256 * 2
def baseEnd_7711256 : Nat := 3959580777866986909136585

theorem tailTrace_7711256 : CollatzResearch.WordTrace tailWord_7711256 prefixEnd_7711256 3959580777866986909136585 := by
  unfold tailWord_7711256
  simp only [CollatzResearch.WordTrace]
  refine ⟨140626306075721982259980811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187501741434295976346641081 140626306075721982259980811)
  ·
    refine ⟨210939459113582973389971217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140626306075721982259980811 210939459113582973389971217)
    ·
      refine ⟨158204594335187230042478413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210939459113582973389971217 158204594335187230042478413)
      ·
        refine ⟨59326722875695211265929405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158204594335187230042478413 59326722875695211265929405)
        ·
          refine ⟨22247521078385704224723527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59326722875695211265929405 22247521078385704224723527)
          ·
            refine ⟨33371281617578556337085291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22247521078385704224723527 33371281617578556337085291)
            ·
              refine ⟨50056922426367834505627937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33371281617578556337085291 50056922426367834505627937)
              ·
                refine ⟨37542691819775875879220953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50056922426367834505627937 37542691819775875879220953)
                ·
                  refine ⟨28157018864831906909415715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37542691819775875879220953 28157018864831906909415715)
                  ·
                    refine ⟨42235528297247860364123573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28157018864831906909415715 42235528297247860364123573)
                    ·
                      refine ⟨3959580777866986909136585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42235528297247860364123573 3959580777866986909136585)
                      ·
                        rfl

theorem cell23_7711256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_7711256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711256 prefixEnd_7711256 := by exact prefixLift 7711256
  have htrace : WordTrace (prefixWord ++ tailWord_7711256) baseStart_7711256 baseEnd_7711256 := by
    simpa [prefixWord, tailWord_7711256, baseEnd_7711256] using wordTrace_append hprefix tailTrace_7711256
  have hstable : (prefixWord ++ tailWord_7711256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711256).length < 2 ^ (prefixWord ++ tailWord_7711256).sum := by decide
  have hdescent : baseEnd_7711256 < baseStart_7711256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711266 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_7711266 : Nat := 118140960795 + 7711266 * 2 ^ 59
def prefixEnd_7711266 : Nat := 4983230072969 + 3 ^ 40 * 7711266 * 2
def baseEnd_7711266 : Nat := 3959585912673531870011539

theorem tailTrace_7711266 : CollatzResearch.WordTrace tailWord_7711266 prefixEnd_7711266 3959585912673531870011539 := by
  unfold tailWord_7711266
  simp only [CollatzResearch.WordTrace]
  refine ⟨70313244220351934056956413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187501984587605157485217101 70313244220351934056956413)
  ·
    refine ⟨26367466582631975271358655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70313244220351934056956413 26367466582631975271358655)
    ·
      refine ⟨39551199873947962907037983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26367466582631975271358655 39551199873947962907037983)
      ·
        refine ⟨59326799810921944360556975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39551199873947962907037983 59326799810921944360556975)
        ·
          refine ⟨88990199716382916540835463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59326799810921944360556975 88990199716382916540835463)
          ·
            refine ⟨133485299574574374811253195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88990199716382916540835463 133485299574574374811253195)
            ·
              refine ⟨200227949361861562216879793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133485299574574374811253195 200227949361861562216879793)
              ·
                refine ⟨150170962021396171662659845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200227949361861562216879793 150170962021396171662659845)
                ·
                  refine ⟨28157055379011782186748721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150170962021396171662659845 28157055379011782186748721)
                  ·
                    refine ⟨21117791534258836640061541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28157055379011782186748721 21117791534258836640061541)
                    ·
                      refine ⟨3959585912673531870011539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21117791534258836640061541 3959585912673531870011539)
                      ·
                        rfl

theorem cell23_7711266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_7711266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711266 prefixEnd_7711266 := by exact prefixLift 7711266
  have htrace : WordTrace (prefixWord ++ tailWord_7711266) baseStart_7711266 baseEnd_7711266 := by
    simpa [prefixWord, tailWord_7711266, baseEnd_7711266] using wordTrace_append hprefix tailTrace_7711266
  have hstable : (prefixWord ++ tailWord_7711266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711266).length < 2 ^ (prefixWord ++ tailWord_7711266).sum := by decide
  have hdescent : baseEnd_7711266 < baseStart_7711266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711303 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_7711303 : Nat := 118140960795 + 7711303 * 2 ^ 59
def prefixEnd_7711303 : Nat := 4983230072969 + 3 ^ 40 * 7711303 * 2
def baseEnd_7711303 : Nat := 3959604911457748225248869

theorem tailTrace_7711303 : CollatzResearch.WordTrace tailWord_7711303 prefixEnd_7711303 3959604911457748225248869 := by
  unfold tailWord_7711303
  simp only [CollatzResearch.WordTrace]
  refine ⟨281254326382273691546922563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187502884254849127697948375 281254326382273691546922563)
  ·
    refine ⟨421881489573410537320383845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281254326382273691546922563 421881489573410537320383845)
    ·
      refine ⟨79102779295014475747571971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421881489573410537320383845 79102779295014475747571971)
      ·
        refine ⟨118654168942521713621357957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79102779295014475747571971 118654168942521713621357957)
        ·
          refine ⟨22247656676722821304004617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118654168942521713621357957 22247656676722821304004617)
          ·
            refine ⟨16685742507542115978003463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22247656676722821304004617 16685742507542115978003463)
            ·
              refine ⟨25028613761313173967005195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16685742507542115978003463 25028613761313173967005195)
              ·
                refine ⟨37542920641969760950507793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25028613761313173967005195 37542920641969760950507793)
                ·
                  refine ⟨28157190481477320712880845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37542920641969760950507793 28157190481477320712880845)
                  ·
                    refine ⟨10558946430553995267330317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28157190481477320712880845 10558946430553995267330317)
                    ·
                      refine ⟨3959604911457748225248869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10558946430553995267330317 3959604911457748225248869)
                      ·
                        rfl

theorem cell23_7711303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_7711303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711303 prefixEnd_7711303 := by exact prefixLift 7711303
  have htrace : WordTrace (prefixWord ++ tailWord_7711303) baseStart_7711303 baseEnd_7711303 := by
    simpa [prefixWord, tailWord_7711303, baseEnd_7711303] using wordTrace_append hprefix tailTrace_7711303
  have hstable : (prefixWord ++ tailWord_7711303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711303).length < 2 ^ (prefixWord ++ tailWord_7711303).sum := by decide
  have hdescent : baseEnd_7711303 < baseStart_7711303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711343 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 2, 4, 2]
def baseStart_7711343 : Nat := 118140960795 + 7711343 * 2 ^ 59
def prefixEnd_7711343 : Nat := 4983230072969 + 3 ^ 40 * 7711343 * 2
def baseEnd_7711343 : Nat := 3959625450683928068748685

theorem tailTrace_7711343 : CollatzResearch.WordTrace tailWord_7711343 prefixEnd_7711343 3959625450683928068748685 := by
  unfold tailWord_7711343
  simp only [CollatzResearch.WordTrace]
  refine ⟨281255785302128778378378683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187503856868085852252252455 281255785302128778378378683)
  ·
    refine ⟨421883677953193167567568025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281255785302128778378378683 421883677953193167567568025)
    ·
      refine ⟨316412758464894875675676019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421883677953193167567568025 316412758464894875675676019)
      ·
        refine ⟨474619137697342313513514029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316412758464894875675676019 474619137697342313513514029)
        ·
          refine ⟨177982176636503367567567761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474619137697342313513514029 177982176636503367567567761)
          ·
            refine ⟨133486632477377525675675821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177982176636503367567567761 133486632477377525675675821)
            ·
              refine ⟨50057487179016572128378433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133486632477377525675675821 50057487179016572128378433)
              ·
                refine ⟨37543115384262429096283825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50057487179016572128378433 37543115384262429096283825)
                ·
                  refine ⟨28157336538196821822212869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37543115384262429096283825 28157336538196821822212869)
                  ·
                    refine ⟨5279500600911904091664913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28157336538196821822212869 5279500600911904091664913)
                    ·
                      refine ⟨3959625450683928068748685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5279500600911904091664913 3959625450683928068748685)
                      ·
                        rfl

theorem cell23_7711343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 4, 2].length) (baseStart_7711343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711343 prefixEnd_7711343 := by exact prefixLift 7711343
  have htrace : WordTrace (prefixWord ++ tailWord_7711343) baseStart_7711343 baseEnd_7711343 := by
    simpa [prefixWord, tailWord_7711343, baseEnd_7711343] using wordTrace_append hprefix tailTrace_7711343
  have hstable : (prefixWord ++ tailWord_7711343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711343).length < 2 ^ (prefixWord ++ tailWord_7711343).sum := by decide
  have hdescent : baseEnd_7711343 < baseStart_7711343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711353 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 3, 4]
def baseStart_7711353 : Nat := 118140960795 + 7711353 * 2 ^ 59
def prefixEnd_7711353 : Nat := 4983230072969 + 3 ^ 40 * 7711353 * 2
def baseEnd_7711353 : Nat := 1319876861830157676541213

theorem tailTrace_7711353 : CollatzResearch.WordTrace tailWord_7711353 prefixEnd_7711353 1319876861830157676541213 := by
  unfold tailWord_7711353
  simp only [CollatzResearch.WordTrace]
  refine ⟨281256150032092550086242713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187504100021395033390828475 281256150032092550086242713)
  ·
    refine ⟨210942112524069412564682035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281256150032092550086242713 210942112524069412564682035)
    ·
      refine ⟨316413168786104118847023053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210942112524069412564682035 316413168786104118847023053)
      ·
        refine ⟨118654938294789044567633645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316413168786104118847023053 118654938294789044567633645)
        ·
          refine ⟨44495601860545891712862617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118654938294789044567633645 44495601860545891712862617)
          ·
            refine ⟨33371701395409418784646963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44495601860545891712862617 33371701395409418784646963)
            ·
              refine ⟨50057552093114128176970445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33371701395409418784646963 50057552093114128176970445)
              ·
                refine ⟨18771582034917798066363917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50057552093114128176970445 18771582034917798066363917)
                ·
                  refine ⟨7039343263094174274886469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18771582034917798066363917 7039343263094174274886469)
                  ·
                    refine ⟨1319876861830157676541213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7039343263094174274886469 1319876861830157676541213)
                    ·
                      rfl

theorem cell23_7711353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 4].length) (baseStart_7711353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711353 prefixEnd_7711353 := by exact prefixLift 7711353
  have htrace : WordTrace (prefixWord ++ tailWord_7711353) baseStart_7711353 baseEnd_7711353 := by
    simpa [prefixWord, tailWord_7711353, baseEnd_7711353] using wordTrace_append hprefix tailTrace_7711353
  have hstable : (prefixWord ++ tailWord_7711353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711353).length < 2 ^ (prefixWord ++ tailWord_7711353).sum := by decide
  have hdescent : baseEnd_7711353 < baseStart_7711353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711380 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_7711380 : Nat := 118140960795 + 7711380 * 2 ^ 59
def prefixEnd_7711380 : Nat := 4983230072969 + 3 ^ 40 * 7711380 * 2
def baseEnd_7711380 : Nat := 3959644449468144423986015

theorem tailTrace_7711380 : CollatzResearch.WordTrace tailWord_7711380 prefixEnd_7711380 3959644449468144423986015 := by
  unfold tailWord_7711380
  simp only [CollatzResearch.WordTrace]
  refine ⟨140628567401497366848737797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187504756535329822464983729 140628567401497366848737797)
  ·
    refine ⟨26367856387780756284138337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140628567401497366848737797 26367856387780756284138337)
    ·
      refine ⟨19775892290835567213103753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26367856387780756284138337 19775892290835567213103753)
      ·
        refine ⟨14831919218126675409827815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19775892290835567213103753 14831919218126675409827815)
        ·
          refine ⟨22247878827190013114741723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14831919218126675409827815 22247878827190013114741723)
          ·
            refine ⟨33371818240785019672112585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22247878827190013114741723 33371818240785019672112585)
            ·
              refine ⟨25028863680588764754084439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33371818240785019672112585 25028863680588764754084439)
              ·
                refine ⟨37543295520883147131126659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25028863680588764754084439 37543295520883147131126659)
                ·
                  refine ⟨56314943281324720696689989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37543295520883147131126659 56314943281324720696689989)
                  ·
                    refine ⟨10559051865248385130629373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56314943281324720696689989 10559051865248385130629373)
                    ·
                      refine ⟨3959644449468144423986015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10559051865248385130629373 3959644449468144423986015)
                      ·
                        rfl

theorem cell23_7711380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_7711380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711380 prefixEnd_7711380 := by exact prefixLift 7711380
  have htrace : WordTrace (prefixWord ++ tailWord_7711380) baseStart_7711380 baseEnd_7711380 := by
    simpa [prefixWord, tailWord_7711380, baseEnd_7711380] using wordTrace_append hprefix tailTrace_7711380
  have hstable : (prefixWord ++ tailWord_7711380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711380).length < 2 ^ (prefixWord ++ tailWord_7711380).sum := by decide
  have hdescent : baseEnd_7711380 < baseStart_7711380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711416 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_7711416 : Nat := 118140960795 + 7711416 * 2 ^ 59
def prefixEnd_7711416 : Nat := 4983230072969 + 3 ^ 40 * 7711416 * 2
def baseEnd_7711416 : Nat := 3959662934771706283135849

theorem tailTrace_7711416 : CollatzResearch.WordTrace tailWord_7711416 prefixEnd_7711416 3959662934771706283135849 := by
  unfold tailWord_7711416
  simp only [CollatzResearch.WordTrace]
  refine ⟨140629223915432155922893051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187505631887242874563857401 140629223915432155922893051)
  ·
    refine ⟨210943835873148233884339577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140629223915432155922893051 210943835873148233884339577)
    ·
      refine ⟨158207876904861175413254683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210943835873148233884339577 158207876904861175413254683)
      ·
        refine ⟨237311815357291763119882025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158207876904861175413254683 237311815357291763119882025)
        ·
          refine ⟨177983861517968822339911519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237311815357291763119882025 177983861517968822339911519)
          ·
            refine ⟨266975792276953233509867279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177983861517968822339911519 266975792276953233509867279)
            ·
              refine ⟨400463688415429850264800919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266975792276953233509867279 400463688415429850264800919)
              ·
                refine ⟨600695532623144775397201379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400463688415429850264800919 600695532623144775397201379)
                ·
                  refine ⟨901043298934717163095802069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600695532623144775397201379 901043298934717163095802069)
                  ·
                    refine ⟨21118202318782433510057861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 901043298934717163095802069 21118202318782433510057861)
                    ·
                      refine ⟨3959662934771706283135849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21118202318782433510057861 3959662934771706283135849)
                      ·
                        rfl

theorem cell23_7711416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_7711416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711416 prefixEnd_7711416 := by exact prefixLift 7711416
  have htrace : WordTrace (prefixWord ++ tailWord_7711416) baseStart_7711416 baseEnd_7711416 := by
    simpa [prefixWord, tailWord_7711416, baseEnd_7711416] using wordTrace_append hprefix tailTrace_7711416
  have hstable : (prefixWord ++ tailWord_7711416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711416).length < 2 ^ (prefixWord ++ tailWord_7711416).sum := by decide
  have hdescent : baseEnd_7711416 < baseStart_7711416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711420 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 4, 3, 2]
def baseStart_7711420 : Nat := 118140960795 + 7711420 * 2 ^ 59
def prefixEnd_7711420 : Nat := 4983230072969 + 3 ^ 40 * 7711420 * 2
def baseEnd_7711420 : Nat := 3959664988694324267485831

theorem tailTrace_7711420 : CollatzResearch.WordTrace tailWord_7711420 prefixEnd_7711420 3959664988694324267485831 := by
  unfold tailWord_7711420
  simp only [CollatzResearch.WordTrace]
  refine ⟨140629296861424910264465857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187505729148566547019287809 140629296861424910264465857)
  ·
    refine ⟨105471972646068682698349393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140629296861424910264465857 105471972646068682698349393)
    ·
      refine ⟨79103979484551512023762045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105471972646068682698349393 79103979484551512023762045)
      ·
        refine ⟨29663992306706817008910767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79103979484551512023762045 29663992306706817008910767)
        ·
          refine ⟨44495988460060225513366151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29663992306706817008910767 44495988460060225513366151)
          ·
            refine ⟨66743982690090338270049227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44495988460060225513366151 66743982690090338270049227)
            ·
              refine ⟨100115974035135507405073841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66743982690090338270049227 100115974035135507405073841)
              ·
                refine ⟨75086980526351630553805381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100115974035135507405073841 75086980526351630553805381)
                ·
                  refine ⟨14078808848690930728838509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75086980526351630553805381 14078808848690930728838509)
                  ·
                    refine ⟨5279553318259099023314441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14078808848690930728838509 5279553318259099023314441)
                    ·
                      refine ⟨3959664988694324267485831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5279553318259099023314441 3959664988694324267485831)
                      ·
                        rfl

theorem cell23_7711420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_7711420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711420 prefixEnd_7711420 := by exact prefixLift 7711420
  have htrace : WordTrace (prefixWord ++ tailWord_7711420) baseStart_7711420 baseEnd_7711420 := by
    simpa [prefixWord, tailWord_7711420, baseEnd_7711420] using wordTrace_append hprefix tailTrace_7711420
  have hstable : (prefixWord ++ tailWord_7711420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711420).length < 2 ^ (prefixWord ++ tailWord_7711420).sum := by decide
  have hdescent : baseEnd_7711420 < baseStart_7711420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711460 : List Nat := [2, 3, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_7711460 : Nat := 118140960795 + 7711460 * 2 ^ 59
def prefixEnd_7711460 : Nat := 4983230072969 + 3 ^ 40 * 7711460 * 2
def baseEnd_7711460 : Nat := 1319895175973501370328549

theorem tailTrace_7711460 : CollatzResearch.WordTrace tailWord_7711460 prefixEnd_7711460 1319895175973501370328549 := by
  unfold tailWord_7711460
  simp only [CollatzResearch.WordTrace]
  refine ⟨140630026321352453680193917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187506701761803271573591889 140630026321352453680193917)
  ·
    refine ⟨52736259870507170130072719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140630026321352453680193917 52736259870507170130072719)
    ·
      refine ⟨79104389805760755195109079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52736259870507170130072719 79104389805760755195109079)
      ·
        refine ⟨118656584708641132792663619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79104389805760755195109079 118656584708641132792663619)
        ·
          refine ⟨177984877062961699188995429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118656584708641132792663619 177984877062961699188995429)
          ·
            refine ⟨33372164449305318597936643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177984877062961699188995429 33372164449305318597936643)
            ·
              refine ⟨50058246673957977896904965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33372164449305318597936643 50058246673957977896904965)
              ·
                refine ⟨9385921251367120855669681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50058246673957977896904965 9385921251367120855669681)
                ·
                  refine ⟨7039440938525340641752261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9385921251367120855669681 7039440938525340641752261)
                  ·
                    refine ⟨1319895175973501370328549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7039440938525340641752261 1319895175973501370328549)
                    ·
                      rfl

theorem cell23_7711460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_7711460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711460 prefixEnd_7711460 := by exact prefixLift 7711460
  have htrace : WordTrace (prefixWord ++ tailWord_7711460) baseStart_7711460 baseEnd_7711460 := by
    simpa [prefixWord, tailWord_7711460, baseEnd_7711460] using wordTrace_append hprefix tailTrace_7711460
  have hstable : (prefixWord ++ tailWord_7711460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711460).length < 2 ^ (prefixWord ++ tailWord_7711460).sum := by decide
  have hdescent : baseEnd_7711460 < baseStart_7711460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711461 : List Nat := [1, 3, 1, 4, 1, 4, 2, 2, 1, 1, 3]
def baseStart_7711461 : Nat := 118140960795 + 7711461 * 2 ^ 59
def prefixEnd_7711461 : Nat := 4983230072969 + 3 ^ 40 * 7711461 * 2
def baseEnd_7711461 : Nat := 3959686041401158607073143

theorem tailTrace_7711461 : CollatzResearch.WordTrace tailWord_7711461 prefixEnd_7711461 3959686041401158607073143 := by
  unfold tailWord_7711461
  simp only [CollatzResearch.WordTrace]
  refine ⟨281260089115701284531174237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187506726077134189687449491 281260089115701284531174237)
  ·
    refine ⟨105472533418387981699190339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281260089115701284531174237 105472533418387981699190339)
    ·
      refine ⟨158208800127581972548785509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105472533418387981699190339 158208800127581972548785509)
      ·
        refine ⟨29664150023921619852897283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158208800127581972548785509 29664150023921619852897283)
        ·
          refine ⟨44496225035882429779345925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29664150023921619852897283 44496225035882429779345925)
          ·
            refine ⟨8343042194227955583627361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44496225035882429779345925 8343042194227955583627361)
            ·
              refine ⟨6257281645670966687720521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8343042194227955583627361 6257281645670966687720521)
              ·
                refine ⟨4692961234253225015790391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6257281645670966687720521 4692961234253225015790391)
                ·
                  refine ⟨7039441851379837523685587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692961234253225015790391 7039441851379837523685587)
                  ·
                    refine ⟨10559162777069756285528381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7039441851379837523685587 10559162777069756285528381)
                    ·
                      refine ⟨3959686041401158607073143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10559162777069756285528381 3959686041401158607073143)
                      ·
                        rfl

theorem cell23_7711461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_7711461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711461 prefixEnd_7711461 := by exact prefixLift 7711461
  have htrace : WordTrace (prefixWord ++ tailWord_7711461) baseStart_7711461 baseEnd_7711461 := by
    simpa [prefixWord, tailWord_7711461, baseEnd_7711461] using wordTrace_append hprefix tailTrace_7711461
  have hstable : (prefixWord ++ tailWord_7711461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711461).length < 2 ^ (prefixWord ++ tailWord_7711461).sum := by decide
  have hdescent : baseEnd_7711461 < baseStart_7711461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711470 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_7711470 : Nat := 118140960795 + 7711470 * 2 ^ 59
def prefixEnd_7711470 : Nat := 4983230072969 + 3 ^ 40 * 7711470 * 2
def baseEnd_7711470 : Nat := 3959690662727049071860601

theorem tailTrace_7711470 : CollatzResearch.WordTrace tailWord_7711470 prefixEnd_7711470 3959690662727049071860601 := by
  unfold tailWord_7711470
  simp only [CollatzResearch.WordTrace]
  refine ⟨35157552171583584883531483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187506944915112452712167909 35157552171583584883531483)
  ·
    refine ⟨52736328257375377325297225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35157552171583584883531483 52736328257375377325297225)
    ·
      refine ⟨39552246193031532993972919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52736328257375377325297225 39552246193031532993972919)
      ·
        refine ⟨59328369289547299490959379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39552246193031532993972919 59328369289547299490959379)
        ·
          refine ⟨88992553934320949236439069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59328369289547299490959379 88992553934320949236439069)
          ·
            refine ⟨33372207725370355963664651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88992553934320949236439069 33372207725370355963664651)
            ·
              refine ⟨50058311588055533945496977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33372207725370355963664651 50058311588055533945496977)
              ·
                refine ⟨37543733691041650459122733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50058311588055533945496977 37543733691041650459122733)
                ·
                  refine ⟨14078900134140618922171025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37543733691041650459122733 14078900134140618922171025)
                  ·
                    refine ⟨10559175100605464191628269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14078900134140618922171025 10559175100605464191628269)
                    ·
                      refine ⟨3959690662727049071860601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10559175100605464191628269 3959690662727049071860601)
                      ·
                        rfl

theorem cell23_7711470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_7711470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711470 prefixEnd_7711470 := by exact prefixLift 7711470
  have htrace : WordTrace (prefixWord ++ tailWord_7711470) baseStart_7711470 baseEnd_7711470 := by
    simpa [prefixWord, tailWord_7711470, baseEnd_7711470] using wordTrace_append hprefix tailTrace_7711470
  have hstable : (prefixWord ++ tailWord_7711470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711470).length < 2 ^ (prefixWord ++ tailWord_7711470).sum := by decide
  have hdescent : baseEnd_7711470 < baseStart_7711470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711500 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 4, 1, 3]
def baseStart_7711500 : Nat := 118140960795 + 7711500 * 2 ^ 59
def prefixEnd_7711500 : Nat := 4983230072969 + 3 ^ 40 * 7711500 * 2
def baseEnd_7711500 : Nat := 3959706067146683954485463

theorem tailTrace_7711500 : CollatzResearch.WordTrace tailWord_7711500 prefixEnd_7711500 3959706067146683954485463 := by
  unfold tailWord_7711500
  simp only [CollatzResearch.WordTrace]
  refine ⟨140630755781279997095921977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187507674375039996127895969 140630755781279997095921977)
  ·
    refine ⟨105473066835959997821941483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140630755781279997095921977 105473066835959997821941483)
    ·
      refine ⟨158209600253939996732912225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105473066835959997821941483 158209600253939996732912225)
      ·
        refine ⟨118657200190454997549684169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158209600253939996732912225 118657200190454997549684169)
        ·
          refine ⟨88992900142841248162263127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118657200190454997549684169 88992900142841248162263127)
          ·
            refine ⟨133489350214261872243394691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88992900142841248162263127 133489350214261872243394691)
            ·
              refine ⟨200234025321392808365092037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133489350214261872243394691 200234025321392808365092037)
              ·
                refine ⟨37543879747761151568454757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200234025321392808365092037 37543879747761151568454757)
                ·
                  refine ⟨7039477452705215919085267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37543879747761151568454757 7039477452705215919085267)
                  ·
                    refine ⟨10559216179057823878627901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7039477452705215919085267 10559216179057823878627901)
                    ·
                      refine ⟨3959706067146683954485463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10559216179057823878627901 3959706067146683954485463)
                      ·
                        rfl

theorem cell23_7711500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_7711500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711500 prefixEnd_7711500 := by exact prefixLift 7711500
  have htrace : WordTrace (prefixWord ++ tailWord_7711500) baseStart_7711500 baseEnd_7711500 := by
    simpa [prefixWord, tailWord_7711500, baseEnd_7711500] using wordTrace_append hprefix tailTrace_7711500
  have hstable : (prefixWord ++ tailWord_7711500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711500).length < 2 ^ (prefixWord ++ tailWord_7711500).sum := by decide
  have hdescent : baseEnd_7711500 < baseStart_7711500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711534 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_7711534 : Nat := 118140960795 + 7711534 * 2 ^ 59
def prefixEnd_7711534 : Nat := 4983230072969 + 3 ^ 40 * 7711534 * 2
def baseEnd_7711534 : Nat := 3959723525488936821460307

theorem tailTrace_7711534 : CollatzResearch.WordTrace tailWord_7711534 prefixEnd_7711534 3959723525488936821460307 := by
  unfold tailWord_7711534
  simp only [CollatzResearch.WordTrace]
  refine ⟨35157843955554602249822707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187508501096291211999054437 35157843955554602249822707)
  ·
    refine ⟨52736765933331903374734061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35157843955554602249822707 52736765933331903374734061)
    ·
      refine ⟨19776287224999463765525273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52736765933331903374734061 19776287224999463765525273)
      ·
        refine ⟨14832215418749597824143955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19776287224999463765525273 14832215418749597824143955)
        ·
          refine ⟨22248323128124396736215933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14832215418749597824143955 22248323128124396736215933)
          ·
            refine ⟨8343121173046648776080975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22248323128124396736215933 8343121173046648776080975)
            ·
              refine ⟨12514681759569973164121463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8343121173046648776080975 12514681759569973164121463)
              ·
                refine ⟨18772022639354959746182195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12514681759569973164121463 18772022639354959746182195)
                ·
                  refine ⟨28158033959032439619273293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18772022639354959746182195 28158033959032439619273293)
                  ·
                    refine ⟨10559262734637164857227485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28158033959032439619273293 10559262734637164857227485)
                    ·
                      refine ⟨3959723525488936821460307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10559262734637164857227485 3959723525488936821460307)
                      ·
                        rfl

theorem cell23_7711534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_7711534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711534 prefixEnd_7711534 := by exact prefixLift 7711534
  have htrace : WordTrace (prefixWord ++ tailWord_7711534) baseStart_7711534 baseEnd_7711534 := by
    simpa [prefixWord, tailWord_7711534, baseEnd_7711534] using wordTrace_append hprefix tailTrace_7711534
  have hstable : (prefixWord ++ tailWord_7711534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711534).length < 2 ^ (prefixWord ++ tailWord_7711534).sum := by decide
  have hdescent : baseEnd_7711534 < baseStart_7711534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711543 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_7711543 : Nat := 118140960795 + 7711543 * 2 ^ 59
def prefixEnd_7711543 : Nat := 4983230072969 + 3 ^ 40 * 7711543 * 2
def baseEnd_7711543 : Nat := 3959728146814827286247765

theorem tailTrace_7711543 : CollatzResearch.WordTrace tailWord_7711543 prefixEnd_7711543 3959728146814827286247765 := by
  unfold tailWord_7711543
  simp only [CollatzResearch.WordTrace]
  refine ⟨281263079901404212535659283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187508719934269475023772855 281263079901404212535659283)
  ·
    refine ⟨421894619852106318803488925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281263079901404212535659283 421894619852106318803488925)
    ·
      refine ⟨158210482444539869551308347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421894619852106318803488925 158210482444539869551308347)
      ·
        refine ⟨237315723666809804326962521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158210482444539869551308347 237315723666809804326962521)
        ·
          refine ⟨177986792750107353245221891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237315723666809804326962521 177986792750107353245221891)
          ·
            refine ⟨266980189125161029867832837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177986792750107353245221891 266980189125161029867832837)
            ·
              refine ⟨50058785460967693100218657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266980189125161029867832837 50058785460967693100218657)
              ·
                refine ⟨37544089095725769825163993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50058785460967693100218657 37544089095725769825163993)
                ·
                  refine ⟨28158066821794327368872995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37544089095725769825163993 28158066821794327368872995)
                  ·
                    refine ⟨42237100232691491053309493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28158066821794327368872995 42237100232691491053309493)
                    ·
                      refine ⟨3959728146814827286247765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42237100232691491053309493 3959728146814827286247765)
                      ·
                        rfl

theorem cell23_7711543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_7711543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711543 prefixEnd_7711543 := by exact prefixLift 7711543
  have htrace : WordTrace (prefixWord ++ tailWord_7711543) baseStart_7711543 baseEnd_7711543 := by
    simpa [prefixWord, tailWord_7711543, baseEnd_7711543] using wordTrace_append hprefix tailTrace_7711543
  have hstable : (prefixWord ++ tailWord_7711543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711543).length < 2 ^ (prefixWord ++ tailWord_7711543).sum := by decide
  have hdescent : baseEnd_7711543 < baseStart_7711543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711573 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_7711573 : Nat := 118140960795 + 7711573 * 2 ^ 59
def prefixEnd_7711573 : Nat := 4983230072969 + 3 ^ 40 * 7711573 * 2
def baseEnd_7711573 : Nat := 3959743551234462168872627

theorem tailTrace_7711573 : CollatzResearch.WordTrace tailWord_7711573 prefixEnd_7711573 3959743551234462168872627 := by
  unfold tailWord_7711573
  simp only [CollatzResearch.WordTrace]
  refine ⟨281264174091295527659251373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187509449394197018439500915 281264174091295527659251373)
  ·
    refine ⟨105474065284235822872219265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281264174091295527659251373 105474065284235822872219265)
    ·
      refine ⟨79105548963176867154164449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105474065284235822872219265 79105548963176867154164449)
      ·
        refine ⟨59329161722382650365623337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79105548963176867154164449 59329161722382650365623337)
        ·
          refine ⟨44496871291786987774217503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59329161722382650365623337 44496871291786987774217503)
          ·
            refine ⟨66745306937680481661326255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44496871291786987774217503 66745306937680481661326255)
            ·
              refine ⟨100117960406520722491989383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66745306937680481661326255 100117960406520722491989383)
              ·
                refine ⟨150176940609781083737984075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100117960406520722491989383 150176940609781083737984075)
                ·
                  refine ⟨225265410914671625606976113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150176940609781083737984075 225265410914671625606976113)
                  ·
                    refine ⟨168949058186003719205232085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225265410914671625606976113 168949058186003719205232085)
                    ·
                      refine ⟨3959743551234462168872627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168949058186003719205232085 3959743551234462168872627)
                      ·
                        rfl

theorem cell23_7711573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_7711573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711573 prefixEnd_7711573 := by exact prefixLift 7711573
  have htrace : WordTrace (prefixWord ++ tailWord_7711573) baseStart_7711573 baseEnd_7711573 := by
    simpa [prefixWord, tailWord_7711573, baseEnd_7711573] using wordTrace_append hprefix tailTrace_7711573
  have hstable : (prefixWord ++ tailWord_7711573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711573).length < 2 ^ (prefixWord ++ tailWord_7711573).sum := by decide
  have hdescent : baseEnd_7711573 < baseStart_7711573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711591 : List Nat := [1, 1, 5, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_7711591 : Nat := 118140960795 + 7711591 * 2 ^ 59
def prefixEnd_7711591 : Nat := 4983230072969 + 3 ^ 40 * 7711591 * 2
def baseEnd_7711591 : Nat := 3959752793886243098447545

theorem tailTrace_7711591 : CollatzResearch.WordTrace tailWord_7711591 prefixEnd_7711591 3959752793886243098447545 := by
  unfold tailWord_7711591
  simp only [CollatzResearch.WordTrace]
  refine ⟨281264830605230316733406627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187509887070153544488937751 281264830605230316733406627)
  ·
    refine ⟨421897245907845475100109941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281264830605230316733406627 421897245907845475100109941)
    ·
      refine ⟨39552866803860513290635307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 421897245907845475100109941 39552866803860513290635307)
      ·
        refine ⟨59329300205790769935952961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39552866803860513290635307 59329300205790769935952961)
        ·
          refine ⟨44496975154343077451964721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59329300205790769935952961 44496975154343077451964721)
          ·
            refine ⟨33372731365757308088973541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44496975154343077451964721 33372731365757308088973541)
            ·
              refine ⟨6257387131079495266682539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33372731365757308088973541 6257387131079495266682539)
              ·
                refine ⟨9386080696619242900023809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6257387131079495266682539 9386080696619242900023809)
                ·
                  refine ⟨7039560522464432175017857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9386080696619242900023809 7039560522464432175017857)
                  ·
                    refine ⟨5279670391848324131263393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7039560522464432175017857 5279670391848324131263393)
                    ·
                      refine ⟨3959752793886243098447545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5279670391848324131263393 3959752793886243098447545)
                      ·
                        rfl

theorem cell23_7711591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_7711591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711591 prefixEnd_7711591 := by exact prefixLift 7711591
  have htrace : WordTrace (prefixWord ++ tailWord_7711591) baseStart_7711591 baseEnd_7711591 := by
    simpa [prefixWord, tailWord_7711591, baseEnd_7711591] using wordTrace_append hprefix tailTrace_7711591
  have hstable : (prefixWord ++ tailWord_7711591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711591).length < 2 ^ (prefixWord ++ tailWord_7711591).sum := by decide
  have hdescent : baseEnd_7711591 < baseStart_7711591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711633 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_7711633 : Nat := 118140960795 + 7711633 * 2 ^ 59
def prefixEnd_7711633 : Nat := 4983230072969 + 3 ^ 40 * 7711633 * 2
def baseEnd_7711633 : Nat := 3959774360073731934122351

theorem tailTrace_7711633 : CollatzResearch.WordTrace tailWord_7711633 prefixEnd_7711633 3959774360073731934122351 := by
  unfold tailWord_7711633
  simp only [CollatzResearch.WordTrace]
  refine ⟨281266362471078157906435553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187510908314052105270957035 281266362471078157906435553)
  ·
    refine ⟨210949771853308618429826665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281266362471078157906435553 210949771853308618429826665)
    ·
      refine ⟨158212328889981463822369999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210949771853308618429826665 158212328889981463822369999)
      ·
        refine ⟨237318493334972195733554999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158212328889981463822369999 237318493334972195733554999)
        ·
          refine ⟨355977740002458293600332499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237318493334972195733554999 355977740002458293600332499)
          ·
            refine ⟨533966610003687440400498749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355977740002458293600332499 533966610003687440400498749)
            ·
              refine ⟨200237478751382790150187031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 533966610003687440400498749 200237478751382790150187031)
              ·
                refine ⟨300356218127074185225280547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200237478751382790150187031 300356218127074185225280547)
                ·
                  refine ⟨450534327190611277837920821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300356218127074185225280547 450534327190611277837920821)
                  ·
                    refine ⟨42237593174119807297305077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 450534327190611277837920821 42237593174119807297305077)
                    ·
                      refine ⟨3959774360073731934122351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42237593174119807297305077 3959774360073731934122351)
                      ·
                        rfl

theorem cell23_7711633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_7711633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711633 prefixEnd_7711633 := by exact prefixLift 7711633
  have htrace : WordTrace (prefixWord ++ tailWord_7711633) baseStart_7711633 baseEnd_7711633 := by
    simpa [prefixWord, tailWord_7711633, baseEnd_7711633] using wordTrace_append hprefix tailTrace_7711633
  have hstable : (prefixWord ++ tailWord_7711633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711633).length < 2 ^ (prefixWord ++ tailWord_7711633).sum := by decide
  have hdescent : baseEnd_7711633 < baseStart_7711633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711647 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 1, 6, 2]
def baseStart_7711647 : Nat := 118140960795 + 7711647 * 2 ^ 59
def prefixEnd_7711647 : Nat := 4983230072969 + 3 ^ 40 * 7711647 * 2
def baseEnd_7711647 : Nat := 3959781548802894879347287

theorem tailTrace_7711647 : CollatzResearch.WordTrace tailWord_7711647 prefixEnd_7711647 3959781548802894879347287 := by
  unfold tailWord_7711647
  simp only [CollatzResearch.WordTrace]
  refine ⟨281266873093027438297445195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187511248728684958864963463 281266873093027438297445195)
  ·
    refine ⟨421900309639541157446167793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281266873093027438297445195 421900309639541157446167793)
    ·
      refine ⟨316425232229655868084625845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421900309639541157446167793 316425232229655868084625845)
      ·
        refine ⟨29664865521530237632933673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 316425232229655868084625845 29664865521530237632933673)
        ·
          refine ⟨22248649141147678224700255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29664865521530237632933673 22248649141147678224700255)
          ·
            refine ⟨33372973711721517337050383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22248649141147678224700255 33372973711721517337050383)
            ·
              refine ⟨50059460567582276005575575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33372973711721517337050383 50059460567582276005575575)
              ·
                refine ⟨75089190851373414008363363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50059460567582276005575575 75089190851373414008363363)
                ·
                  refine ⟨112633786277060121012545045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75089190851373414008363363 112633786277060121012545045)
                  ·
                    refine ⟨5279708731737193172463049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112633786277060121012545045 5279708731737193172463049)
                    ·
                      refine ⟨3959781548802894879347287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5279708731737193172463049 3959781548802894879347287)
                      ·
                        rfl

theorem cell23_7711647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_7711647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711647 prefixEnd_7711647 := by exact prefixLift 7711647
  have htrace : WordTrace (prefixWord ++ tailWord_7711647) baseStart_7711647 baseEnd_7711647 := by
    simpa [prefixWord, tailWord_7711647, baseEnd_7711647] using wordTrace_append hprefix tailTrace_7711647
  have hstable : (prefixWord ++ tailWord_7711647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711647).length < 2 ^ (prefixWord ++ tailWord_7711647).sum := by decide
  have hdescent : baseEnd_7711647 < baseStart_7711647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711653 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 12]
def baseStart_7711653 : Nat := 118140960795 + 7711653 * 2 ^ 59
def prefixEnd_7711653 : Nat := 4983230072969 + 3 ^ 40 * 7711653 * 2
def baseEnd_7711653 : Nat := 439976069965202428430251

theorem tailTrace_7711653 : CollatzResearch.WordTrace tailWord_7711653 prefixEnd_7711653 439976069965202428430251 := by
  unfold tailWord_7711653
  simp only [CollatzResearch.WordTrace]
  refine ⟨281267091931005701322163613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187511394620670467548109075 281267091931005701322163613)
  ·
    refine ⟨105475159474127137995811355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281267091931005701322163613 105475159474127137995811355)
    ·
      refine ⟨158212739211190706993717033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105475159474127137995811355 158212739211190706993717033)
      ·
        refine ⟨118659554408393030245287775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158212739211190706993717033 118659554408393030245287775)
        ·
          refine ⟨177989331612589545367931663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118659554408393030245287775 177989331612589545367931663)
          ·
            refine ⟨266983997418884318051897495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177989331612589545367931663 266983997418884318051897495)
            ·
              refine ⟨400475996128326477077846243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266983997418884318051897495 400475996128326477077846243)
              ·
                refine ⟨600713994192489715616769365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400475996128326477077846243 600713994192489715616769365)
                ·
                  refine ⟨439976069965202428430251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 600713994192489715616769365 439976069965202428430251)
                  ·
                    rfl

theorem cell23_7711653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_7711653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711653 prefixEnd_7711653 := by exact prefixLift 7711653
  have htrace : WordTrace (prefixWord ++ tailWord_7711653) baseStart_7711653 baseEnd_7711653 := by
    simpa [prefixWord, tailWord_7711653, baseEnd_7711653] using wordTrace_append hprefix tailTrace_7711653
  have hstable : (prefixWord ++ tailWord_7711653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711653).length < 2 ^ (prefixWord ++ tailWord_7711653).sum := by decide
  have hdescent : baseEnd_7711653 < baseStart_7711653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711661 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_7711661 : Nat := 118140960795 + 7711661 * 2 ^ 59
def prefixEnd_7711661 : Nat := 4983230072969 + 3 ^ 40 * 7711661 * 2
def baseEnd_7711661 : Nat := 1319929579177352608190741

theorem tailTrace_7711661 : CollatzResearch.WordTrace tailWord_7711661 prefixEnd_7711661 1319929579177352608190741 := by
  unfold tailWord_7711661
  simp only [CollatzResearch.WordTrace]
  refine ⟨281267383714976718688454837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187511589143317812458969891 281267383714976718688454837)
  ·
    refine ⟨26368817223279067377042641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281267383714976718688454837 26368817223279067377042641)
    ·
      refine ⟨19776612917459300532781981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26368817223279067377042641 19776612917459300532781981)
      ·
        refine ⟨7416229844047237699793243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19776612917459300532781981 7416229844047237699793243)
        ·
          refine ⟨11124344766070856549689865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7416229844047237699793243 11124344766070856549689865)
          ·
            refine ⟨8343258574553142412267399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11124344766070856549689865 8343258574553142412267399)
            ·
              refine ⟨12514887861829713618401099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8343258574553142412267399 12514887861829713618401099)
              ·
                refine ⟨18772331792744570427601649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12514887861829713618401099 18772331792744570427601649)
                ·
                  refine ⟨14079248844558427820701237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18772331792744570427601649 14079248844558427820701237)
                  ·
                    refine ⟨1319929579177352608190741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14079248844558427820701237 1319929579177352608190741)
                    ·
                      rfl

theorem cell23_7711661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_7711661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711661 prefixEnd_7711661 := by exact prefixLift 7711661
  have htrace : WordTrace (prefixWord ++ tailWord_7711661) baseStart_7711661 baseEnd_7711661 := by
    simpa [prefixWord, tailWord_7711661, baseEnd_7711661] using wordTrace_append hprefix tailTrace_7711661
  have hstable : (prefixWord ++ tailWord_7711661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711661).length < 2 ^ (prefixWord ++ tailWord_7711661).sum := by decide
  have hdescent : baseEnd_7711661 < baseStart_7711661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7711674 : List Nat := [3, 1, 1, 1, 2, 1, 6, 3, 1, 4]
def baseStart_7711674 : Nat := 118140960795 + 7711674 * 2 ^ 59
def prefixEnd_7711674 : Nat := 4983230072969 + 3 ^ 40 * 7711674 * 2
def baseEnd_7711674 : Nat := 1319931804260188757903221

theorem tailTrace_7711674 : CollatzResearch.WordTrace tailWord_7711674 prefixEnd_7711674 1319931804260188757903221 := by
  unfold tailWord_7711674
  simp only [CollatzResearch.WordTrace]
  refine ⟨70316964465982405477169519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187511905242619747939118717 70316964465982405477169519)
  ·
    refine ⟨105475446698973608215754279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70316964465982405477169519 105475446698973608215754279)
    ·
      refine ⟨158213170048460412323631419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105475446698973608215754279 158213170048460412323631419)
      ·
        refine ⟨237319755072690618485447129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158213170048460412323631419 237319755072690618485447129)
        ·
          refine ⟨177989816304517963864085347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237319755072690618485447129 177989816304517963864085347)
          ·
            refine ⟨266984724456776945796128021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177989816304517963864085347 266984724456776945796128021)
            ·
              refine ⟨12514908958911419334193501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 266984724456776945796128021 12514908958911419334193501)
              ·
                refine ⟨4693090859591782250322563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12514908958911419334193501 4693090859591782250322563)
                ·
                  refine ⟨7039636289387673375483845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693090859591782250322563 7039636289387673375483845)
                  ·
                    refine ⟨1319931804260188757903221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7039636289387673375483845 1319931804260188757903221)
                    ·
                      rfl

theorem cell23_7711674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_7711674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7711674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7711674 prefixEnd_7711674 := by exact prefixLift 7711674
  have htrace : WordTrace (prefixWord ++ tailWord_7711674) baseStart_7711674 baseEnd_7711674 := by
    simpa [prefixWord, tailWord_7711674, baseEnd_7711674] using wordTrace_append hprefix tailTrace_7711674
  have hstable : (prefixWord ++ tailWord_7711674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7711674).length < 2 ^ (prefixWord ++ tailWord_7711674).sum := by decide
  have hdescent : baseEnd_7711674 < baseStart_7711674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7711674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
