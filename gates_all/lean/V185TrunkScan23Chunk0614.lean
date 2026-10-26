import V185TrunkScan23Chunk0613

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3631180 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_3631180 : Nat := 118140960795 + 3631180 * 2 ^ 59
def prefixEnd_3631180 : Nat := 4983230072969 + 3 ^ 40 * 3631180 * 2
def baseEnd_3631180 : Nat := 1864540682993208225250513

theorem tailTrace_3631180 : CollatzResearch.WordTrace tailWord_3631180 prefixEnd_3631180 1864540682993208225250513 := by
  unfold tailWord_3631180
  simp only [CollatzResearch.WordTrace]
  refine ⟨66220007492431245507977497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88293343323241660677303329 66220007492431245507977497)
  ·
    refine ⟨49665005619323434130983123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66220007492431245507977497 49665005619323434130983123)
    ·
      refine ⟨74497508428985151196474685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49665005619323434130983123 74497508428985151196474685)
      ·
        refine ⟨27936565660869431698678007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74497508428985151196474685 27936565660869431698678007)
        ·
          refine ⟨41904848491304147548017011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27936565660869431698678007 41904848491304147548017011)
          ·
            refine ⟨62857272736956221322025517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41904848491304147548017011 62857272736956221322025517)
            ·
              refine ⟨23571477276358582995759569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62857272736956221322025517 23571477276358582995759569)
              ·
                refine ⟨17678607957268937246819677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23571477276358582995759569 17678607957268937246819677)
                ·
                  refine ⟨6629477983975851467557379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17678607957268937246819677 6629477983975851467557379)
                  ·
                    refine ⟨9944216975963777201336069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6629477983975851467557379 9944216975963777201336069)
                    ·
                      refine ⟨1864540682993208225250513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9944216975963777201336069 1864540682993208225250513)
                      ·
                        rfl

theorem cell23_3631180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_3631180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631180 prefixEnd_3631180 := by exact prefixLift 3631180
  have htrace : WordTrace (prefixWord ++ tailWord_3631180) baseStart_3631180 baseEnd_3631180 := by
    simpa [prefixWord, tailWord_3631180, baseEnd_3631180] using wordTrace_append hprefix tailTrace_3631180
  have hstable : (prefixWord ++ tailWord_3631180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631180).length < 2 ^ (prefixWord ++ tailWord_3631180).sum := by decide
  have hdescent : baseEnd_3631180 < baseStart_3631180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631203 : List Nat := [1, 1, 1, 5, 1, 1, 2, 11]
def baseStart_3631203 : Nat := 118140960795 + 3631203 * 2 ^ 59
def prefixEnd_3631203 : Nat := 4983230072969 + 3 ^ 40 * 3631203 * 2
def baseEnd_3631203 : Nat := 69057499742528208713441

theorem tailTrace_3631203 : CollatzResearch.WordTrace tailWord_3631203 prefixEnd_3631203 69057499742528208713441 := by
  unfold tailWord_3631203
  simp only [CollatzResearch.WordTrace]
  refine ⟨132440853863779165944042263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88293902575852777296028175 132440853863779165944042263)
  ·
    refine ⟨198661280795668748916063395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132440853863779165944042263 198661280795668748916063395)
    ·
      refine ⟨297991921193503123374095093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198661280795668748916063395 297991921193503123374095093)
      ·
        refine ⟨27936742611890917816321415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 297991921193503123374095093 27936742611890917816321415)
        ·
          refine ⟨41905113917836376724482123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27936742611890917816321415 41905113917836376724482123)
          ·
            refine ⟨62857670876754565086723185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41905113917836376724482123 62857670876754565086723185)
            ·
              refine ⟨47143253157565923815042389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62857670876754565086723185 47143253157565923815042389)
              ·
                refine ⟨69057499742528208713441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 47143253157565923815042389 69057499742528208713441)
                ·
                  rfl

theorem cell23_3631203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 11].length) (baseStart_3631203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631203 prefixEnd_3631203 := by exact prefixLift 3631203
  have htrace : WordTrace (prefixWord ++ tailWord_3631203) baseStart_3631203 baseEnd_3631203 := by
    simpa [prefixWord, tailWord_3631203, baseEnd_3631203] using wordTrace_append hprefix tailTrace_3631203
  have hstable : (prefixWord ++ tailWord_3631203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631203).length < 2 ^ (prefixWord ++ tailWord_3631203).sum := by decide
  have hdescent : baseEnd_3631203 < baseStart_3631203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631214 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_3631214 : Nat := 118140960795 + 3631214 * 2 ^ 59
def prefixEnd_3631214 : Nat := 4983230072969 + 3 ^ 40 * 3631214 * 2
def baseEnd_3631214 : Nat := 1864558141335461092225357

theorem tailTrace_3631214 : CollatzResearch.WordTrace tailWord_3631214 prefixEnd_3631214 1864558141335461092225357 := by
  unfold tailWord_3631214
  simp only [CollatzResearch.WordTrace]
  refine ⟨16555156883342414352836587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88294170044492876548461797 16555156883342414352836587)
  ·
    refine ⟨24832735325013621529254881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16555156883342414352836587 24832735325013621529254881)
    ·
      refine ⟨18624551493760216146941161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24832735325013621529254881 18624551493760216146941161)
      ·
        refine ⟨13968413620320162110205871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18624551493760216146941161 13968413620320162110205871)
        ·
          refine ⟨20952620430480243165308807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13968413620320162110205871 20952620430480243165308807)
          ·
            refine ⟨31428930645720364747963211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20952620430480243165308807 31428930645720364747963211)
            ·
              refine ⟨47143395968580547121944817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31428930645720364747963211 47143395968580547121944817)
              ·
                refine ⟨35357546976435410341458613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47143395968580547121944817 35357546976435410341458613)
                ·
                  refine ⟨3314770029040819719511745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35357546976435410341458613 3314770029040819719511745)
                  ·
                    refine ⟨2486077521780614789633809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3314770029040819719511745 2486077521780614789633809)
                    ·
                      refine ⟨1864558141335461092225357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2486077521780614789633809 1864558141335461092225357)
                      ·
                        rfl

theorem cell23_3631214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_3631214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631214 prefixEnd_3631214 := by exact prefixLift 3631214
  have htrace : WordTrace (prefixWord ++ tailWord_3631214) baseStart_3631214 baseEnd_3631214 := by
    simpa [prefixWord, tailWord_3631214, baseEnd_3631214] using wordTrace_append hprefix tailTrace_3631214
  have hstable : (prefixWord ++ tailWord_3631214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631214).length < 2 ^ (prefixWord ++ tailWord_3631214).sum := by decide
  have hdescent : baseEnd_3631214 < baseStart_3631214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631217 : List Nat := [1, 2, 2, 2, 1, 1, 5, 3, 1, 2, 3]
def baseStart_3631217 : Nat := 118140960795 + 3631217 * 2 ^ 59
def prefixEnd_3631217 : Nat := 4983230072969 + 3 ^ 40 * 3631217 * 2
def baseEnd_3631217 : Nat := 1864559681777424580487843

theorem tailTrace_3631217 : CollatzResearch.WordTrace tailWord_3631217 prefixEnd_3631217 1864559681777424580487843 := by
  unfold tailWord_3631217
  simp only [CollatzResearch.WordTrace]
  refine ⟨132441364485728446335051905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88294242990485630890034603 132441364485728446335051905)
  ·
    refine ⟨99331023364296334751288929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132441364485728446335051905 99331023364296334751288929)
    ·
      refine ⟨74498267523222251063466697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99331023364296334751288929 74498267523222251063466697)
      ·
        refine ⟨55873700642416688297600023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74498267523222251063466697 55873700642416688297600023)
        ·
          refine ⟨83810550963625032446400035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55873700642416688297600023 83810550963625032446400035)
          ·
            refine ⟨125715826445437548669600053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83810550963625032446400035 125715826445437548669600053)
            ·
              refine ⟨11785858729259770187775005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125715826445437548669600053 11785858729259770187775005)
              ·
                refine ⟨4419697023472413820415627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11785858729259770187775005 4419697023472413820415627)
                ·
                  refine ⟨6629545535208620730623441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4419697023472413820415627 6629545535208620730623441)
                  ·
                    refine ⟨4972159151406465547967581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6629545535208620730623441 4972159151406465547967581)
                    ·
                      refine ⟨1864559681777424580487843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4972159151406465547967581 1864559681777424580487843)
                      ·
                        rfl

theorem cell23_3631217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_3631217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631217 prefixEnd_3631217 := by exact prefixLift 3631217
  have htrace : WordTrace (prefixWord ++ tailWord_3631217) baseStart_3631217 baseEnd_3631217 := by
    simpa [prefixWord, tailWord_3631217, baseEnd_3631217] using wordTrace_append hprefix tailTrace_3631217
  have hstable : (prefixWord ++ tailWord_3631217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631217).length < 2 ^ (prefixWord ++ tailWord_3631217).sum := by decide
  have hdescent : baseEnd_3631217 < baseStart_3631217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631257 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 3, 3, 2]
def baseStart_3631257 : Nat := 118140960795 + 3631257 * 2 ^ 59
def prefixEnd_3631257 : Nat := 4983230072969 + 3 ^ 40 * 3631257 * 2
def baseEnd_3631257 : Nat := 1864580221003604423987659

theorem tailTrace_3631257 : CollatzResearch.WordTrace tailWord_3631257 prefixEnd_3631257 1864580221003604423987659 := by
  unfold tailWord_3631257
  simp only [CollatzResearch.WordTrace]
  refine ⟨132442823405583533166508025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88295215603722355444338683 132442823405583533166508025)
  ·
    refine ⟨99332117554187649874881019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132442823405583533166508025 99332117554187649874881019)
    ·
      refine ⟨148998176331281474812321529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99332117554187649874881019 148998176331281474812321529)
      ·
        refine ⟨111748632248461106109241147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148998176331281474812321529 111748632248461106109241147)
        ·
          refine ⟨167622948372691659163861721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111748632248461106109241147 167622948372691659163861721)
          ·
            refine ⟨125717211279518744372896291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167622948372691659163861721 125717211279518744372896291)
            ·
              refine ⟨188575816919278116559344437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125717211279518744372896291 188575816919278116559344437)
              ·
                refine ⟨17678982836182323427438541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188575816919278116559344437 17678982836182323427438541)
                ·
                  refine ⟨6629618563568371285289453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17678982836182323427438541 6629618563568371285289453)
                  ·
                    refine ⟨2486106961338139231983545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6629618563568371285289453 2486106961338139231983545)
                    ·
                      refine ⟨1864580221003604423987659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2486106961338139231983545 1864580221003604423987659)
                      ·
                        rfl

theorem cell23_3631257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 3, 2].length) (baseStart_3631257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631257 prefixEnd_3631257 := by exact prefixLift 3631257
  have htrace : WordTrace (prefixWord ++ tailWord_3631257) baseStart_3631257 baseEnd_3631257 := by
    simpa [prefixWord, tailWord_3631257, baseEnd_3631257] using wordTrace_append hprefix tailTrace_3631257
  have hstable : (prefixWord ++ tailWord_3631257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631257).length < 2 ^ (prefixWord ++ tailWord_3631257).sum := by decide
  have hdescent : baseEnd_3631257 < baseStart_3631257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631260 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_3631260 : Nat := 118140960795 + 3631260 * 2 ^ 59
def prefixEnd_3631260 : Nat := 4983230072969 + 3 ^ 40 * 3631260 * 2
def baseEnd_3631260 : Nat := 1864581761445567912250145

theorem tailTrace_3631260 : CollatzResearch.WordTrace tailWord_3631260 prefixEnd_3631260 1864581761445567912250145 := by
  unfold tailWord_3631260
  simp only [CollatzResearch.WordTrace]
  refine ⟨66221466412286332339433617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88295288549715109785911489 66221466412286332339433617)
  ·
    refine ⟨49666099809214749254575213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66221466412286332339433617 49666099809214749254575213)
    ·
      refine ⟨18624787428455530970465705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49666099809214749254575213 18624787428455530970465705)
      ·
        refine ⟨13968590571341648227849279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18624787428455530970465705 13968590571341648227849279)
        ·
          refine ⟨20952885857012472341773919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13968590571341648227849279 20952885857012472341773919)
          ·
            refine ⟨31429328785518708512660879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20952885857012472341773919 31429328785518708512660879)
            ·
              refine ⟨47143993178278062768991319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31429328785518708512660879 47143993178278062768991319)
              ·
                refine ⟨70715989767417094153486979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47143993178278062768991319 70715989767417094153486979)
                ·
                  refine ⟨106073984651125641230230469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70715989767417094153486979 106073984651125641230230469)
                  ·
                    refine ⟨19888872122086057730668213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106073984651125641230230469 19888872122086057730668213)
                    ·
                      refine ⟨1864581761445567912250145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19888872122086057730668213 1864581761445567912250145)
                      ·
                        rfl

theorem cell23_3631260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_3631260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631260 prefixEnd_3631260 := by exact prefixLift 3631260
  have htrace : WordTrace (prefixWord ++ tailWord_3631260) baseStart_3631260 baseEnd_3631260 := by
    simpa [prefixWord, tailWord_3631260, baseEnd_3631260] using wordTrace_append hprefix tailTrace_3631260
  have hstable : (prefixWord ++ tailWord_3631260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631260).length < 2 ^ (prefixWord ++ tailWord_3631260).sum := by decide
  have hdescent : baseEnd_3631260 < baseStart_3631260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631327 : List Nat := [1, 1, 2, 3, 2, 1, 1, 7, 5]
def baseStart_3631327 : Nat := 118140960795 + 3631327 * 2 ^ 59
def prefixEnd_3631327 : Nat := 4983230072969 + 3 ^ 40 * 3631327 * 2
def baseEnd_3631327 : Nat := 207179573849935461123593

theorem tailTrace_3631327 : CollatzResearch.WordTrace tailWord_3631327 prefixEnd_3631327 207179573849935461123593 := by
  unfold tailWord_3631327
  simp only [CollatzResearch.WordTrace]
  refine ⟨132445376515329935121556235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88296917676886623414370823 132445376515329935121556235)
  ·
    refine ⟨198668064772994902682334353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132445376515329935121556235 198668064772994902682334353)
    ·
      refine ⟨149001048579746177011750765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198668064772994902682334353 149001048579746177011750765)
      ·
        refine ⟨55875393217404816379406537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149001048579746177011750765 55875393217404816379406537)
        ·
          refine ⟨41906544913053612284554903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55875393217404816379406537 41906544913053612284554903)
          ·
            refine ⟨62859817369580418426832355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41906544913053612284554903 62859817369580418426832355)
            ·
              refine ⟨94289726054370627640248533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62859817369580418426832355 94289726054370627640248533)
              ·
                refine ⟨2209915454399311585318325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 94289726054370627640248533 2209915454399311585318325)
                ·
                  refine ⟨207179573849935461123593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2209915454399311585318325 207179573849935461123593)
                  ·
                    rfl

theorem cell23_3631327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 5].length) (baseStart_3631327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631327 prefixEnd_3631327 := by exact prefixLift 3631327
  have htrace : WordTrace (prefixWord ++ tailWord_3631327) baseStart_3631327 baseEnd_3631327 := by
    simpa [prefixWord, tailWord_3631327, baseEnd_3631327] using wordTrace_append hprefix tailTrace_3631327
  have hstable : (prefixWord ++ tailWord_3631327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631327).length < 2 ^ (prefixWord ++ tailWord_3631327).sum := by decide
  have hdescent : baseEnd_3631327 < baseStart_3631327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631347 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 1, 7, 2]
def baseStart_3631347 : Nat := 118140960795 + 3631347 * 2 ^ 59
def prefixEnd_3631347 : Nat := 4983230072969 + 3 ^ 40 * 3631347 * 2
def baseEnd_3631347 : Nat := 1864626434262509071862245

theorem tailTrace_3631347 : CollatzResearch.WordTrace tailWord_3631347 prefixEnd_3631347 1864626434262509071862245 := by
  unfold tailWord_3631347
  simp only [CollatzResearch.WordTrace]
  refine ⟨132446105975257478537284295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88297403983504985691522863 132446105975257478537284295)
  ·
    refine ⟨198669158962886217805926443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132446105975257478537284295 198669158962886217805926443)
    ·
      refine ⟨298003738444329326708889665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198669158962886217805926443 298003738444329326708889665)
      ·
        refine ⟨223502803833246995031667249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298003738444329326708889665 223502803833246995031667249)
        ·
          refine ⟨167627102874935246273750437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223502803833246995031667249 167627102874935246273750437)
          ·
            refine ⟨31430081789050358676328207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167627102874935246273750437 31430081789050358676328207)
            ·
              refine ⟨47145122683575538014492311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31430081789050358676328207 47145122683575538014492311)
              ·
                refine ⟨70717684025363307021738467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47145122683575538014492311 70717684025363307021738467)
                ·
                  refine ⟨106076526038044960532607701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70717684025363307021738467 106076526038044960532607701)
                  ·
                    refine ⟨2486168579016678762482993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 106076526038044960532607701 2486168579016678762482993)
                    ·
                      refine ⟨1864626434262509071862245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2486168579016678762482993 1864626434262509071862245)
                      ·
                        rfl

theorem cell23_3631347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 7, 2].length) (baseStart_3631347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631347 prefixEnd_3631347 := by exact prefixLift 3631347
  have htrace : WordTrace (prefixWord ++ tailWord_3631347) baseStart_3631347 baseEnd_3631347 := by
    simpa [prefixWord, tailWord_3631347, baseEnd_3631347] using wordTrace_append hprefix tailTrace_3631347
  have hstable : (prefixWord ++ tailWord_3631347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631347).length < 2 ^ (prefixWord ++ tailWord_3631347).sum := by decide
  have hdescent : baseEnd_3631347 < baseStart_3631347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631377 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_3631377 : Nat := 118140960795 + 3631377 * 2 ^ 59
def prefixEnd_3631377 : Nat := 4983230072969 + 3 ^ 40 * 3631377 * 2
def baseEnd_3631377 : Nat := 1864641838682143954487107

theorem tailTrace_3631377 : CollatzResearch.WordTrace tailWord_3631377 prefixEnd_3631377 1864641838682143954487107 := by
  unfold tailWord_3631377
  simp only [CollatzResearch.WordTrace]
  refine ⟨132447200165148793660876385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88298133443432529107250923 132447200165148793660876385)
  ·
    refine ⟨99335400123861595245657289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132447200165148793660876385 99335400123861595245657289)
    ·
      refine ⟨74501550092896196434242967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99335400123861595245657289 74501550092896196434242967)
      ·
        refine ⟨111752325139344294651364451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74501550092896196434242967 111752325139344294651364451)
        ·
          refine ⟨167628487709016441977046677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111752325139344294651364451 167628487709016441977046677)
          ·
            refine ⟨7857585361360145717674063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167628487709016441977046677 7857585361360145717674063)
            ·
              refine ⟨11786378042040218576511095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7857585361360145717674063 11786378042040218576511095)
              ·
                refine ⟨17679567063060327864766643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11786378042040218576511095 17679567063060327864766643)
                ·
                  refine ⟨26519350594590491797149965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17679567063060327864766643 26519350594590491797149965)
                  ·
                    refine ⟨9944756472971434423931237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26519350594590491797149965 9944756472971434423931237)
                    ·
                      refine ⟨1864641838682143954487107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9944756472971434423931237 1864641838682143954487107)
                      ·
                        rfl

theorem cell23_3631377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_3631377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631377 prefixEnd_3631377 := by exact prefixLift 3631377
  have htrace : WordTrace (prefixWord ++ tailWord_3631377) baseStart_3631377 baseEnd_3631377 := by
    simpa [prefixWord, tailWord_3631377, baseEnd_3631377] using wordTrace_append hprefix tailTrace_3631377
  have hstable : (prefixWord ++ tailWord_3631377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631377).length < 2 ^ (prefixWord ++ tailWord_3631377).sum := by decide
  have hdescent : baseEnd_3631377 < baseStart_3631377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631461 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3]
def baseStart_3631461 : Nat := 118140960795 + 3631461 * 2 ^ 59
def prefixEnd_3631461 : Nat := 4983230072969 + 3 ^ 40 * 3631461 * 2
def baseEnd_3631461 : Nat := 1864684971057121625836721

theorem tailTrace_3631461 : CollatzResearch.WordTrace tailWord_3631461 prefixEnd_3631461 1864684971057121625836721 := by
  unfold tailWord_3631461
  simp only [CollatzResearch.WordTrace]
  refine ⟨132450263896844476006934237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88300175931229650671289491 132450263896844476006934237)
  ·
    refine ⟨49668848961316678502600339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132450263896844476006934237 49668848961316678502600339)
    ·
      refine ⟨74503273441975017753900509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49668848961316678502600339 74503273441975017753900509)
      ·
        refine ⟨27938727540740631657712691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74503273441975017753900509 27938727540740631657712691)
        ·
          refine ⟨41908091311110947486569037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27938727540740631657712691 41908091311110947486569037)
          ·
            refine ⟨15715534241666605307463389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41908091311110947486569037 15715534241666605307463389)
            ·
              refine ⟨5893325340624976990298771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15715534241666605307463389 5893325340624976990298771)
              ·
                refine ⟨8839988010937465485448157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5893325340624976990298771 8839988010937465485448157)
                ·
                  refine ⟨3314995504101549557043059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8839988010937465485448157 3314995504101549557043059)
                  ·
                    refine ⟨4972493256152324335564589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3314995504101549557043059 4972493256152324335564589)
                    ·
                      refine ⟨1864684971057121625836721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4972493256152324335564589 1864684971057121625836721)
                      ·
                        rfl

theorem cell23_3631461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_3631461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631461 prefixEnd_3631461 := by exact prefixLift 3631461
  have htrace : WordTrace (prefixWord ++ tailWord_3631461) baseStart_3631461 baseEnd_3631461 := by
    simpa [prefixWord, tailWord_3631461, baseEnd_3631461] using wordTrace_append hprefix tailTrace_3631461
  have hstable : (prefixWord ++ tailWord_3631461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631461).length < 2 ^ (prefixWord ++ tailWord_3631461).sum := by decide
  have hdescent : baseEnd_3631461 < baseStart_3631461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631467 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 4]
def baseStart_3631467 : Nat := 118140960795 + 3631467 * 2 ^ 59
def prefixEnd_3631467 : Nat := 4983230072969 + 3 ^ 40 * 3631467 * 2
def baseEnd_3631467 : Nat := 1864688051941048602361693

theorem tailTrace_3631467 : CollatzResearch.WordTrace tailWord_3631467 prefixEnd_3631467 1864688051941048602361693 := by
  unfold tailWord_3631467
  simp only [CollatzResearch.WordTrace]
  refine ⟨132450482734822739031652655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88300321823215159354435103 132450482734822739031652655)
  ·
    refine ⟨198675724102234108547478983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132450482734822739031652655 198675724102234108547478983)
    ·
      refine ⟨298013586153351162821218475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198675724102234108547478983 298013586153351162821218475)
      ·
        refine ⟨447020379230026744231827713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298013586153351162821218475 447020379230026744231827713)
        ·
          refine ⟨335265284422520058173870785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447020379230026744231827713 335265284422520058173870785)
          ·
            refine ⟨251448963316890043630403089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335265284422520058173870785 251448963316890043630403089)
            ·
              refine ⟨188586722487667532722802317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251448963316890043630403089 188586722487667532722802317)
              ·
                refine ⟨70720020932875324771050869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188586722487667532722802317 70720020932875324771050869)
                ·
                  refine ⟨6630001962457061697286019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70720020932875324771050869 6630001962457061697286019)
                  ·
                    refine ⟨9945002943685592545929029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6630001962457061697286019 9945002943685592545929029)
                    ·
                      refine ⟨1864688051941048602361693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9945002943685592545929029 1864688051941048602361693)
                      ·
                        rfl

theorem cell23_3631467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 4].length) (baseStart_3631467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631467 prefixEnd_3631467 := by exact prefixLift 3631467
  have htrace : WordTrace (prefixWord ++ tailWord_3631467) baseStart_3631467 baseEnd_3631467 := by
    simpa [prefixWord, tailWord_3631467, baseEnd_3631467] using wordTrace_append hprefix tailTrace_3631467
  have hstable : (prefixWord ++ tailWord_3631467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631467).length < 2 ^ (prefixWord ++ tailWord_3631467).sum := by decide
  have hdescent : baseEnd_3631467 < baseStart_3631467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631468 : List Nat := [2, 2, 1, 1, 7, 1, 2, 1, 6]
def baseStart_3631468 : Nat := 118140960795 + 3631468 * 2 ^ 59
def prefixEnd_3631468 : Nat := 4983230072969 + 3 ^ 40 * 3631468 * 2
def baseEnd_3631468 : Nat := 207187618380189233161021

theorem tailTrace_3631468 : CollatzResearch.WordTrace tailWord_3631468 prefixEnd_3631468 207187618380189233161021 := by
  unfold tailWord_3631468
  simp only [CollatzResearch.WordTrace]
  refine ⟨66225259603909558101219529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88300346138546077468292705 66225259603909558101219529)
  ·
    refine ⟨49668944702932168575914647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66225259603909558101219529 49668944702932168575914647)
    ·
      refine ⟨74503417054398252863871971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49668944702932168575914647 74503417054398252863871971)
      ·
        refine ⟨111755125581597379295807957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74503417054398252863871971 111755125581597379295807957)
        ·
          refine ⟨2619260755818688577245499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 111755125581597379295807957 2619260755818688577245499)
          ·
            refine ⟨3928891133728032865868249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2619260755818688577245499 3928891133728032865868249)
            ·
              refine ⟨2946668350296024649401187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3928891133728032865868249 2946668350296024649401187)
              ·
                refine ⟨4420002525444036974101781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2946668350296024649401187 4420002525444036974101781)
                ·
                  refine ⟨207187618380189233161021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4420002525444036974101781 207187618380189233161021)
                  ·
                    rfl

theorem cell23_3631468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 6].length) (baseStart_3631468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631468 prefixEnd_3631468 := by exact prefixLift 3631468
  have htrace : WordTrace (prefixWord ++ tailWord_3631468) baseStart_3631468 baseEnd_3631468 := by
    simpa [prefixWord, tailWord_3631468, baseEnd_3631468] using wordTrace_append hprefix tailTrace_3631468
  have hstable : (prefixWord ++ tailWord_3631468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631468).length < 2 ^ (prefixWord ++ tailWord_3631468).sum := by decide
  have hdescent : baseEnd_3631468 < baseStart_3631468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631484 : List Nat := [2, 2, 2, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_3631484 : Nat := 118140960795 + 3631484 * 2 ^ 59
def prefixEnd_3631484 : Nat := 4983230072969 + 3 ^ 40 * 3631484 * 2
def baseEnd_3631484 : Nat := 1864696781112175035849115

theorem tailTrace_3631484 : CollatzResearch.WordTrace tailWord_3631484 prefixEnd_3631484 1864696781112175035849115 := by
  unfold tailWord_3631484
  simp only [CollatzResearch.WordTrace]
  refine ⟨66225551387880575467510753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88300735183840767290014337 66225551387880575467510753)
  ·
    refine ⟨49669163540910431600633065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66225551387880575467510753 49669163540910431600633065)
    ·
      refine ⟨37251872655682823700474799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49669163540910431600633065 37251872655682823700474799)
      ·
        refine ⟨55877808983524235550712199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37251872655682823700474799 55877808983524235550712199)
        ·
          refine ⟨83816713475286353326068299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55877808983524235550712199 83816713475286353326068299)
          ·
            refine ⟨125725070212929529989102449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83816713475286353326068299 125725070212929529989102449)
            ·
              refine ⟨94293802659697147491826837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125725070212929529989102449 94293802659697147491826837)
              ·
                refine ⟨4420021999673303788679383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94293802659697147491826837 4420021999673303788679383)
                ·
                  refine ⟨6630032999509955683019075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4420021999673303788679383 6630032999509955683019075)
                  ·
                    refine ⟨9945049499264933524528613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6630032999509955683019075 9945049499264933524528613)
                    ·
                      refine ⟨1864696781112175035849115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9945049499264933524528613 1864696781112175035849115)
                      ·
                        rfl

theorem cell23_3631484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_3631484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631484 prefixEnd_3631484 := by exact prefixLift 3631484
  have htrace : WordTrace (prefixWord ++ tailWord_3631484) baseStart_3631484 baseEnd_3631484 := by
    simpa [prefixWord, tailWord_3631484, baseEnd_3631484] using wordTrace_append hprefix tailTrace_3631484
  have hstable : (prefixWord ++ tailWord_3631484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631484).length < 2 ^ (prefixWord ++ tailWord_3631484).sum := by decide
  have hdescent : baseEnd_3631484 < baseStart_3631484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631487 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 3]
def baseStart_3631487 : Nat := 118140960795 + 3631487 * 2 ^ 59
def prefixEnd_3631487 : Nat := 4983230072969 + 3 ^ 40 * 3631487 * 2
def baseEnd_3631487 : Nat := 1864698321554138524111601

theorem tailTrace_3631487 : CollatzResearch.WordTrace tailWord_3631487 prefixEnd_3631487 1864698321554138524111601 := by
  unfold tailWord_3631487
  simp only [CollatzResearch.WordTrace]
  refine ⟨132451212194750282447380715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88300808129833521631587143 132451212194750282447380715)
  ·
    refine ⟨198676818292125423671071073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132451212194750282447380715 198676818292125423671071073)
    ·
      refine ⟨149007613719094067753303305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198676818292125423671071073 149007613719094067753303305)
      ·
        refine ⟨111755710289320550814977479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149007613719094067753303305 111755710289320550814977479)
        ·
          refine ⟨167633565433980826222466219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111755710289320550814977479 167633565433980826222466219)
          ·
            refine ⟨251450348150971239333699329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167633565433980826222466219 251450348150971239333699329)
            ·
              refine ⟨188587761113228429500274497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251450348150971239333699329 188587761113228429500274497)
              ·
                refine ⟨141440820834921322125205873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188587761113228429500274497 141440820834921322125205873)
                ·
                  refine ⟨106080615626190991593904405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141440820834921322125205873 106080615626190991593904405)
                  ·
                    refine ⟨4972528857477702730964269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106080615626190991593904405 4972528857477702730964269)
                    ·
                      refine ⟨1864698321554138524111601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4972528857477702730964269 1864698321554138524111601)
                      ·
                        rfl

theorem cell23_3631487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_3631487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631487 prefixEnd_3631487 := by exact prefixLift 3631487
  have htrace : WordTrace (prefixWord ++ tailWord_3631487) baseStart_3631487 baseEnd_3631487 := by
    simpa [prefixWord, tailWord_3631487, baseEnd_3631487] using wordTrace_append hprefix tailTrace_3631487
  have hstable : (prefixWord ++ tailWord_3631487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631487).length < 2 ^ (prefixWord ++ tailWord_3631487).sum := by decide
  have hdescent : baseEnd_3631487 < baseStart_3631487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631512 : List Nat := [2, 1, 2, 5, 1, 3, 2, 2, 1, 1, 3]
def baseStart_3631512 : Nat := 118140960795 + 3631512 * 2 ^ 59
def prefixEnd_3631512 : Nat := 4983230072969 + 3 ^ 40 * 3631512 * 2
def baseEnd_3631512 : Nat := 1864711158570500926298987

theorem tailTrace_3631512 : CollatzResearch.WordTrace tailWord_3631512 prefixEnd_3631512 1864711158570500926298987 := by
  unfold tailWord_3631512
  simp only [CollatzResearch.WordTrace]
  refine ⟨66226062009829855858520395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88301416013106474478027193 66226062009829855858520395)
  ·
    refine ⟨99339093014744783787780593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66226062009829855858520395 99339093014744783787780593)
    ·
      refine ⟨74504319761058587840835445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99339093014744783787780593 74504319761058587840835445)
      ·
        refine ⟨6984779977599242610078323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74504319761058587840835445 6984779977599242610078323)
        ·
          refine ⟨10477169966398863915117485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6984779977599242610078323 10477169966398863915117485)
          ·
            refine ⟨3928938737399573968169057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10477169966398863915117485 3928938737399573968169057)
            ·
              refine ⟨2946704053049680476126793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3928938737399573968169057 2946704053049680476126793)
              ·
                refine ⟨2210028039787260357095095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2946704053049680476126793 2210028039787260357095095)
                ·
                  refine ⟨3315042059680890535642643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210028039787260357095095 3315042059680890535642643)
                  ·
                    refine ⟨4972563089521335803463965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3315042059680890535642643 4972563089521335803463965)
                    ·
                      refine ⟨1864711158570500926298987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4972563089521335803463965 1864711158570500926298987)
                      ·
                        rfl

theorem cell23_3631512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_3631512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631512 prefixEnd_3631512 := by exact prefixLift 3631512
  have htrace : WordTrace (prefixWord ++ tailWord_3631512) baseStart_3631512 baseEnd_3631512 := by
    simpa [prefixWord, tailWord_3631512, baseEnd_3631512] using wordTrace_append hprefix tailTrace_3631512
  have hstable : (prefixWord ++ tailWord_3631512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631512).length < 2 ^ (prefixWord ++ tailWord_3631512).sum := by decide
  have hdescent : baseEnd_3631512 < baseStart_3631512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631528 : List Nat := [2, 1, 6, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3631528 : Nat := 118140960795 + 3631528 * 2 ^ 59
def prefixEnd_3631528 : Nat := 4983230072969 + 3 ^ 40 * 3631528 * 2
def baseEnd_3631528 : Nat := 621573124753657621232971

theorem tailTrace_3631528 : CollatzResearch.WordTrace tailWord_3631528 prefixEnd_3631528 621573124753657621232971 := by
  unfold tailWord_3631528
  simp only [CollatzResearch.WordTrace]
  refine ⟨66226353793800873224811619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88301805058401164299748825 66226353793800873224811619)
  ·
    refine ⟨99339530690701309837217429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66226353793800873224811619 99339530690701309837217429)
    ·
      refine ⟨4656540501126623898619567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 99339530690701309837217429 4656540501126623898619567)
      ·
        refine ⟨6984810751689935847929351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4656540501126623898619567 6984810751689935847929351)
        ·
          refine ⟨10477216127534903771894027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6984810751689935847929351 10477216127534903771894027)
          ·
            refine ⟨15715824191302355657841041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10477216127534903771894027 15715824191302355657841041)
            ·
              refine ⟨11786868143476766743380781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15715824191302355657841041 11786868143476766743380781)
              ·
                refine ⟨4420075553803787528767793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11786868143476766743380781 4420075553803787528767793)
                ·
                  refine ⟨3315056665352840646575845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4420075553803787528767793 3315056665352840646575845)
                  ·
                    refine ⟨621573124753657621232971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3315056665352840646575845 621573124753657621232971)
                    ·
                      rfl

theorem cell23_3631528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3631528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631528 prefixEnd_3631528 := by exact prefixLift 3631528
  have htrace : WordTrace (prefixWord ++ tailWord_3631528) baseStart_3631528 baseEnd_3631528 := by
    simpa [prefixWord, tailWord_3631528, baseEnd_3631528] using wordTrace_append hprefix tailTrace_3631528
  have hstable : (prefixWord ++ tailWord_3631528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631528).length < 2 ^ (prefixWord ++ tailWord_3631528).sum := by decide
  have hdescent : baseEnd_3631528 < baseStart_3631528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631541 : List Nat := [1, 3, 3, 2, 3, 1, 3, 7]
def baseStart_3631541 : Nat := 118140960795 + 3631541 * 2 ^ 59
def prefixEnd_3631541 : Nat := 4983230072969 + 3 ^ 40 * 3631541 * 2
def baseEnd_3631541 : Nat := 69063927759610418993939

theorem tailTrace_3631541 : CollatzResearch.WordTrace tailWord_3631541 prefixEnd_3631541 69063927759610418993939 := by
  unfold tailWord_3631541
  simp only [CollatzResearch.WordTrace]
  refine ⟨132453181736554649669846477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88302121157703099779897651 132453181736554649669846477)
  ·
    refine ⟨49669943151207993626192429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132453181736554649669846477 49669943151207993626192429)
    ·
      refine ⟨18626228681702997609822161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49669943151207993626192429 18626228681702997609822161)
      ·
        refine ⟨13969671511277248207366621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18626228681702997609822161 13969671511277248207366621)
        ·
          refine ⟨5238626816728968077762483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13969671511277248207366621 5238626816728968077762483)
          ·
            refine ⟨7857940225093452116643725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5238626816728968077762483 7857940225093452116643725)
            ·
              refine ⟨2946727584410044543741397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7857940225093452116643725 2946727584410044543741397)
              ·
                refine ⟨69063927759610418993939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2946727584410044543741397 69063927759610418993939)
                ·
                  rfl

theorem cell23_3631541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 7].length) (baseStart_3631541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631541 prefixEnd_3631541 := by exact prefixLift 3631541
  have htrace : WordTrace (prefixWord ++ tailWord_3631541) baseStart_3631541 baseEnd_3631541 := by
    simpa [prefixWord, tailWord_3631541, baseEnd_3631541] using wordTrace_append hprefix tailTrace_3631541
  have hstable : (prefixWord ++ tailWord_3631541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631541).length < 2 ^ (prefixWord ++ tailWord_3631541).sum := by decide
  have hdescent : baseEnd_3631541 < baseStart_3631541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631664 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 4]
def baseStart_3631664 : Nat := 118140960795 + 3631664 * 2 ^ 59
def prefixEnd_3631664 : Nat := 4983230072969 + 3 ^ 40 * 3631664 * 2
def baseEnd_3631664 : Nat := 1864789207629984331598287

theorem tailTrace_3631664 : CollatzResearch.WordTrace tailWord_3631664 prefixEnd_3631664 1864789207629984331598287 := by
  unfold tailWord_3631664
  simp only [CollatzResearch.WordTrace]
  refine ⟨66228833957554520838287023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88305111943406027784382697 66228833957554520838287023)
  ·
    refine ⟨99343250936331781257430535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66228833957554520838287023 99343250936331781257430535)
    ·
      refine ⟨149014876404497671886145803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99343250936331781257430535 149014876404497671886145803)
      ·
        refine ⟨223522314606746507829218705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149014876404497671886145803 223522314606746507829218705)
        ·
          refine ⟨167641735955059880871914029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223522314606746507829218705 167641735955059880871914029)
          ·
            refine ⟨62865650983147455326967761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167641735955059880871914029 62865650983147455326967761)
            ·
              refine ⟨47149238237360591495225821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62865650983147455326967761 47149238237360591495225821)
              ·
                refine ⟨17680964339010221810709683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47149238237360591495225821 17680964339010221810709683)
                ·
                  refine ⟨26521446508515332716064525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17680964339010221810709683 26521446508515332716064525)
                  ·
                    refine ⟨9945542440693249768524197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26521446508515332716064525 9945542440693249768524197)
                    ·
                      refine ⟨1864789207629984331598287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9945542440693249768524197 1864789207629984331598287)
                      ·
                        rfl

theorem cell23_3631664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_3631664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631664 prefixEnd_3631664 := by exact prefixLift 3631664
  have htrace : WordTrace (prefixWord ++ tailWord_3631664) baseStart_3631664 baseEnd_3631664 := by
    simpa [prefixWord, tailWord_3631664, baseEnd_3631664] using wordTrace_append hprefix tailTrace_3631664
  have hstable : (prefixWord ++ tailWord_3631664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631664).length < 2 ^ (prefixWord ++ tailWord_3631664).sum := by decide
  have hdescent : baseEnd_3631664 < baseStart_3631664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631698 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_3631698 : Nat := 118140960795 + 3631698 * 2 ^ 59
def prefixEnd_3631698 : Nat := 4983230072969 + 3 ^ 40 * 3631698 * 2
def baseEnd_3631698 : Nat := 1864806665972237198573131

theorem tailTrace_3631698 : CollatzResearch.WordTrace tailWord_3631698 prefixEnd_3631698 1864806665972237198573131 := by
  unfold tailWord_3631698
  simp only [CollatzResearch.WordTrace]
  refine ⟨33114726999246466370827937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88305938664657243655541165 33114726999246466370827937)
  ·
    refine ⟨24836045249434849778120953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33114726999246466370827937 24836045249434849778120953)
    ·
      refine ⟨18627033937076137333590715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24836045249434849778120953 18627033937076137333590715)
      ·
        refine ⟨27940550905614206000386073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18627033937076137333590715 27940550905614206000386073)
        ·
          refine ⟨20955413179210654500289555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27940550905614206000386073 20955413179210654500289555)
          ·
            refine ⟨31433119768815981750434333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20955413179210654500289555 31433119768815981750434333)
            ·
              refine ⟨11787419913305993156412875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31433119768815981750434333 11787419913305993156412875)
              ·
                refine ⟨17681129869958989734619313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11787419913305993156412875 17681129869958989734619313)
                ·
                  refine ⟨13260847402469242300964485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17681129869958989734619313 13260847402469242300964485)
                  ·
                    refine ⟨2486408887962982931430841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13260847402469242300964485 2486408887962982931430841)
                    ·
                      refine ⟨1864806665972237198573131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2486408887962982931430841 1864806665972237198573131)
                      ·
                        rfl

theorem cell23_3631698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_3631698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631698 prefixEnd_3631698 := by exact prefixLift 3631698
  have htrace : WordTrace (prefixWord ++ tailWord_3631698) baseStart_3631698 baseEnd_3631698 := by
    simpa [prefixWord, tailWord_3631698, baseEnd_3631698] using wordTrace_append hprefix tailTrace_3631698
  have hstable : (prefixWord ++ tailWord_3631698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631698).length < 2 ^ (prefixWord ++ tailWord_3631698).sum := by decide
  have hdescent : baseEnd_3631698 < baseStart_3631698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631701 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_3631701 : Nat := 118140960795 + 3631701 * 2 ^ 59
def prefixEnd_3631701 : Nat := 4983230072969 + 3 ^ 40 * 3631701 * 2
def baseEnd_3631701 : Nat := 1864808206414200686835617

theorem tailTrace_3631701 : CollatzResearch.WordTrace tailWord_3631701 prefixEnd_3631701 1864808206414200686835617 := by
  unfold tailWord_3631701
  simp only [CollatzResearch.WordTrace]
  refine ⟨132459017415974996995670957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88306011610649997997113971 132459017415974996995670957)
  ·
    refine ⟨49672131530990623873376609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132459017415974996995670957 49672131530990623873376609)
    ·
      refine ⟨37254098648242967905032457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49672131530990623873376609 37254098648242967905032457)
      ·
        refine ⟨27940573986182225928774343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37254098648242967905032457 27940573986182225928774343)
        ·
          refine ⟨41910860979273338893161515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27940573986182225928774343 41910860979273338893161515)
          ·
            refine ⟨62866291468910008339742273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41910860979273338893161515 62866291468910008339742273)
            ·
              refine ⟨47149718601682506254806705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62866291468910008339742273 47149718601682506254806705)
              ·
                refine ⟨35362288951261879691105029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47149718601682506254806705 35362288951261879691105029)
                ·
                  refine ⟨6630429178361602442082193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35362288951261879691105029 6630429178361602442082193)
                  ·
                    refine ⟨4972821883771201831561645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6630429178361602442082193 4972821883771201831561645)
                    ·
                      refine ⟨1864808206414200686835617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4972821883771201831561645 1864808206414200686835617)
                      ·
                        rfl

theorem cell23_3631701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_3631701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631701 prefixEnd_3631701 := by exact prefixLift 3631701
  have htrace : WordTrace (prefixWord ++ tailWord_3631701) baseStart_3631701 baseEnd_3631701 := by
    simpa [prefixWord, tailWord_3631701, baseEnd_3631701] using wordTrace_append hprefix tailTrace_3631701
  have hstable : (prefixWord ++ tailWord_3631701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631701).length < 2 ^ (prefixWord ++ tailWord_3631701).sum := by decide
  have hdescent : baseEnd_3631701 < baseStart_3631701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631725 : List Nat := [1, 5, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_3631725 : Nat := 118140960795 + 3631725 * 2 ^ 59
def prefixEnd_3631725 : Nat := 4983230072969 + 3 ^ 40 * 3631725 * 2
def baseEnd_3631725 : Nat := 621606843316636197645169

theorem tailTrace_3631725 : CollatzResearch.WordTrace tailWord_3631725 prefixEnd_3631725 621606843316636197645169 := by
  unfold tailWord_3631725
  simp only [CollatzResearch.WordTrace]
  refine ⟨132459892767888049094544629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88306595178592032729696419 132459892767888049094544629)
  ·
    refine ⟨12418114946989504602613559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132459892767888049094544629 12418114946989504602613559)
    ·
      refine ⟨18627172420484256903920339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12418114946989504602613559 18627172420484256903920339)
      ·
        refine ⟨27940758630726385355880509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18627172420484256903920339 27940758630726385355880509)
        ·
          refine ⟨10477784486522394508455191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27940758630726385355880509 10477784486522394508455191)
          ·
            refine ⟨15716676729783591762682787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10477784486522394508455191 15716676729783591762682787)
            ·
              refine ⟨23575015094675387644024181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15716676729783591762682787 23575015094675387644024181)
              ·
                refine ⟨2210157665125817591627267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23575015094675387644024181 2210157665125817591627267)
                ·
                  refine ⟨3315236497688726387440901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210157665125817591627267 3315236497688726387440901)
                  ·
                    refine ⟨621606843316636197645169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3315236497688726387440901 621606843316636197645169)
                    ·
                      rfl

theorem cell23_3631725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_3631725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631725 prefixEnd_3631725 := by exact prefixLift 3631725
  have htrace : WordTrace (prefixWord ++ tailWord_3631725) baseStart_3631725 baseEnd_3631725 := by
    simpa [prefixWord, tailWord_3631725, baseEnd_3631725] using wordTrace_append hprefix tailTrace_3631725
  have hstable : (prefixWord ++ tailWord_3631725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631725).length < 2 ^ (prefixWord ++ tailWord_3631725).sum := by decide
  have hdescent : baseEnd_3631725 < baseStart_3631725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631758 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2]
def baseStart_3631758 : Nat := 118140960795 + 3631758 * 2 ^ 59
def prefixEnd_3631758 : Nat := 4983230072969 + 3 ^ 40 * 3631758 * 2
def baseEnd_3631758 : Nat := 1864837474811506963822855

theorem tailTrace_3631758 : CollatzResearch.WordTrace tailWord_3631758 prefixEnd_3631758 1864837474811506963822855 := by
  unfold tailWord_3631758
  simp only [CollatzResearch.WordTrace]
  refine ⟨16557637047096061966311991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88307397584512330486997285 16557637047096061966311991)
  ·
    refine ⟨24836455570644092949467987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16557637047096061966311991 24836455570644092949467987)
    ·
      refine ⟨37254683355966139424201981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24836455570644092949467987 37254683355966139424201981)
      ·
        refine ⟨13970506258487302284075743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37254683355966139424201981 13970506258487302284075743)
        ·
          refine ⟨20955759387730953426113615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13970506258487302284075743 20955759387730953426113615)
          ·
            refine ⟨31433639081596430139170423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20955759387730953426113615 31433639081596430139170423)
            ·
              refine ⟨47150458622394645208755635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31433639081596430139170423 47150458622394645208755635)
              ·
                refine ⟨70725687933591967813133453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47150458622394645208755635 70725687933591967813133453)
                ·
                  refine ⟨26522132975096987929925045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70725687933591967813133453 26522132975096987929925045)
                  ·
                    refine ⟨2486449966415342618430473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26522132975096987929925045 2486449966415342618430473)
                    ·
                      refine ⟨1864837474811506963822855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2486449966415342618430473 1864837474811506963822855)
                      ·
                        rfl

theorem cell23_3631758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_3631758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631758 prefixEnd_3631758 := by exact prefixLift 3631758
  have htrace : WordTrace (prefixWord ++ tailWord_3631758) baseStart_3631758 baseEnd_3631758 := by
    simpa [prefixWord, tailWord_3631758, baseEnd_3631758] using wordTrace_append hprefix tailTrace_3631758
  have hstable : (prefixWord ++ tailWord_3631758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631758).length < 2 ^ (prefixWord ++ tailWord_3631758).sum := by decide
  have hdescent : baseEnd_3631758 < baseStart_3631758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631768 : List Nat := [2, 1, 2, 4, 1, 1, 4, 2, 1, 5]
def baseStart_3631768 : Nat := 118140960795 + 3631768 * 2 ^ 59
def prefixEnd_3631768 : Nat := 4983230072969 + 3 ^ 40 * 3631768 * 2
def baseEnd_3631768 : Nat := 621614203206017308232603

theorem tailTrace_3631768 : CollatzResearch.WordTrace tailWord_3631768 prefixEnd_3631768 621614203206017308232603 := by
  unfold tailWord_3631768
  simp only [CollatzResearch.WordTrace]
  refine ⟨66230730553366133719179979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88307640737821511625573305 66230730553366133719179979)
  ·
    refine ⟨99346095830049200578769969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66230730553366133719179979 99346095830049200578769969)
    ·
      refine ⟨74509571872536900434077477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99346095830049200578769969 74509571872536900434077477)
      ·
        refine ⟨13970544726100668831389527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74509571872536900434077477 13970544726100668831389527)
        ·
          refine ⟨20955817089151003247084291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13970544726100668831389527 20955817089151003247084291)
          ·
            refine ⟨31433725633726504870626437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20955817089151003247084291 31433725633726504870626437)
            ·
              refine ⟨5893823556323719663242457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31433725633726504870626437 5893823556323719663242457)
              ·
                refine ⟨4420367667242789747431843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5893823556323719663242457 4420367667242789747431843)
                ·
                  refine ⟨6630551500864184621147765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4420367667242789747431843 6630551500864184621147765)
                  ·
                    refine ⟨621614203206017308232603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6630551500864184621147765 621614203206017308232603)
                    ·
                      rfl

theorem cell23_3631768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_3631768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631768 prefixEnd_3631768 := by exact prefixLift 3631768
  have htrace : WordTrace (prefixWord ++ tailWord_3631768) baseStart_3631768 baseEnd_3631768 := by
    simpa [prefixWord, tailWord_3631768, baseEnd_3631768] using wordTrace_append hprefix tailTrace_3631768
  have hstable : (prefixWord ++ tailWord_3631768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631768).length < 2 ^ (prefixWord ++ tailWord_3631768).sum := by decide
  have hdescent : baseEnd_3631768 < baseStart_3631768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631791 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 5]
def baseStart_3631791 : Nat := 118140960795 + 3631791 * 2 ^ 59
def prefixEnd_3631791 : Nat := 4983230072969 + 3 ^ 40 * 3631791 * 2
def baseEnd_3631791 : Nat := 1864854419673105334710203

theorem tailTrace_3631791 : CollatzResearch.WordTrace tailWord_3631791 prefixEnd_3631791 1864854419673105334710203 := by
  unfold tailWord_3631791
  simp only [CollatzResearch.WordTrace]
  refine ⟨132462299985648942366447227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88308199990432628244298151 132462299985648942366447227)
  ·
    refine ⟨198693449978473413549670841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132462299985648942366447227 198693449978473413549670841)
    ·
      refine ⟨149020087483855060162253131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198693449978473413549670841 149020087483855060162253131)
      ·
        refine ⟨223530131225782590243379697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149020087483855060162253131 223530131225782590243379697)
        ·
          refine ⟨167647598419336942682534773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223530131225782590243379697 167647598419336942682534773)
          ·
            refine ⟨15716962351812838376487635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167647598419336942682534773 15716962351812838376487635)
            ·
              refine ⟨23575443527719257564731453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15716962351812838376487635 23575443527719257564731453)
              ·
                refine ⟨8840791322894721586774295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23575443527719257564731453 8840791322894721586774295)
                ·
                  refine ⟨13261186984342082380161443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8840791322894721586774295 13261186984342082380161443)
                  ·
                    refine ⟨19891780476513123570242165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13261186984342082380161443 19891780476513123570242165)
                    ·
                      refine ⟨1864854419673105334710203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19891780476513123570242165 1864854419673105334710203)
                      ·
                        rfl

theorem cell23_3631791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_3631791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631791 prefixEnd_3631791 := by exact prefixLift 3631791
  have htrace : WordTrace (prefixWord ++ tailWord_3631791) baseStart_3631791 baseEnd_3631791 := by
    simpa [prefixWord, tailWord_3631791, baseEnd_3631791] using wordTrace_append hprefix tailTrace_3631791
  have hstable : (prefixWord ++ tailWord_3631791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631791).length < 2 ^ (prefixWord ++ tailWord_3631791).sum := by decide
  have hdescent : baseEnd_3631791 < baseStart_3631791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631799 : List Nat := [1, 1, 3, 1, 6, 1, 3, 2, 1, 1, 3]
def baseStart_3631799 : Nat := 118140960795 + 3631799 * 2 ^ 59
def prefixEnd_3631799 : Nat := 4983230072969 + 3 ^ 40 * 3631799 * 2
def baseEnd_3631799 : Nat := 1864858527518341303410167

theorem tailTrace_3631799 : CollatzResearch.WordTrace tailWord_3631799 prefixEnd_3631799 1864858527518341303410167 := by
  unfold tailWord_3631799
  simp only [CollatzResearch.WordTrace]
  refine ⟨132462591769619959732738451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88308394513079973155158967 132462591769619959732738451)
  ·
    refine ⟨198693887654429939599107677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132462591769619959732738451 198693887654429939599107677)
    ·
      refine ⟨74510207870411227349665379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198693887654429939599107677 74510207870411227349665379)
      ·
        refine ⟨111765311805616841024498069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74510207870411227349665379 111765311805616841024498069)
        ·
          refine ⟨5238998990888289423023347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111765311805616841024498069 5238998990888289423023347)
          ·
            refine ⟨7858498486332434134535021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5238998990888289423023347 7858498486332434134535021)
            ·
              refine ⟨2946936932374662800450633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7858498486332434134535021 2946936932374662800450633)
              ·
                refine ⟨2210202699280997100337975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2946936932374662800450633 2210202699280997100337975)
                ·
                  refine ⟨3315304048921495650506963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210202699280997100337975 3315304048921495650506963)
                  ·
                    refine ⟨4972956073382243475760445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3315304048921495650506963 4972956073382243475760445)
                    ·
                      refine ⟨1864858527518341303410167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4972956073382243475760445 1864858527518341303410167)
                      ·
                        rfl

theorem cell23_3631799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 1, 1, 3].length) (baseStart_3631799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631799 prefixEnd_3631799 := by exact prefixLift 3631799
  have htrace : WordTrace (prefixWord ++ tailWord_3631799) baseStart_3631799 baseEnd_3631799 := by
    simpa [prefixWord, tailWord_3631799, baseEnd_3631799] using wordTrace_append hprefix tailTrace_3631799
  have hstable : (prefixWord ++ tailWord_3631799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631799).length < 2 ^ (prefixWord ++ tailWord_3631799).sum := by decide
  have hdescent : baseEnd_3631799 < baseStart_3631799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631855 : List Nat := [1, 1, 2, 1, 5, 2, 1, 4, 2, 1, 3]
def baseStart_3631855 : Nat := 118140960795 + 3631855 * 2 ^ 59
def prefixEnd_3631855 : Nat := 4983230072969 + 3 ^ 40 * 3631855 * 2
def baseEnd_3631855 : Nat := 1864887282434993084309909

theorem tailTrace_3631855 : CollatzResearch.WordTrace tailWord_3631855 prefixEnd_3631855 1864887282434993084309909 := by
  unfold tailWord_3631855
  simp only [CollatzResearch.WordTrace]
  refine ⟨132464634257417081296777019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88309756171611387531184679 132464634257417081296777019)
  ·
    refine ⟨198696951386125621945165529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132464634257417081296777019 198696951386125621945165529)
    ·
      refine ⟨149022713539594216458874147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198696951386125621945165529 149022713539594216458874147)
      ·
        refine ⟨223534070309391324688311221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149022713539594216458874147 223534070309391324688311221)
        ·
          refine ⟨20956319091505436689529177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223534070309391324688311221 20956319091505436689529177)
          ·
            refine ⟨15717239318629077517146883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20956319091505436689529177 15717239318629077517146883)
            ·
              refine ⟨23575858977943616275720325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15717239318629077517146883 23575858977943616275720325)
              ·
                refine ⟨4420473558364428051697561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23575858977943616275720325 4420473558364428051697561)
                ·
                  refine ⟨3315355168773321038773171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4420473558364428051697561 3315355168773321038773171)
                  ·
                    refine ⟨4973032753159981558159757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3315355168773321038773171 4973032753159981558159757)
                    ·
                      refine ⟨1864887282434993084309909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4973032753159981558159757 1864887282434993084309909)
                      ·
                        rfl

theorem cell23_3631855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 1, 3].length) (baseStart_3631855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631855 prefixEnd_3631855 := by exact prefixLift 3631855
  have htrace : WordTrace (prefixWord ++ tailWord_3631855) baseStart_3631855 baseEnd_3631855 := by
    simpa [prefixWord, tailWord_3631855, baseEnd_3631855] using wordTrace_append hprefix tailTrace_3631855
  have hstable : (prefixWord ++ tailWord_3631855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631855).length < 2 ^ (prefixWord ++ tailWord_3631855).sum := by decide
  have hdescent : baseEnd_3631855 < baseStart_3631855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631881 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 5]
def baseStart_3631881 : Nat := 118140960795 + 3631881 * 2 ^ 59
def prefixEnd_3631881 : Nat := 4983230072969 + 3 ^ 40 * 3631881 * 2
def baseEnd_3631881 : Nat := 1864900632932009982584789

theorem tailTrace_3631881 : CollatzResearch.WordTrace tailWord_3631881 prefixEnd_3631881 1864900632932009982584789 := by
  unfold tailWord_3631881
  simp only [CollatzResearch.WordTrace]
  refine ⟨132465582555322887737223497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88310388370215258491482331 132465582555322887737223497)
  ·
    refine ⟨99349186916492165802917623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132465582555322887737223497 99349186916492165802917623)
    ·
      refine ⟨149023780374738248704376435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99349186916492165802917623 149023780374738248704376435)
      ·
        refine ⟨223535670562107373056564653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149023780374738248704376435 223535670562107373056564653)
        ·
          refine ⟨83825876460790264896211745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223535670562107373056564653 83825876460790264896211745)
          ·
            refine ⟨62869407345592698672158809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83825876460790264896211745 62869407345592698672158809)
            ·
              refine ⟨47152055509194524004119107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62869407345592698672158809 47152055509194524004119107)
              ·
                refine ⟨70728083263791786006178661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47152055509194524004119107 70728083263791786006178661)
                ·
                  refine ⟨13261515611960959876158499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70728083263791786006178661 13261515611960959876158499)
                  ·
                    refine ⟨19892273417941439814237749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13261515611960959876158499 19892273417941439814237749)
                    ·
                      refine ⟨1864900632932009982584789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19892273417941439814237749 1864900632932009982584789)
                      ·
                        rfl

theorem cell23_3631881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_3631881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631881 prefixEnd_3631881 := by exact prefixLift 3631881
  have htrace : WordTrace (prefixWord ++ tailWord_3631881) baseStart_3631881 baseEnd_3631881 := by
    simpa [prefixWord, tailWord_3631881, baseEnd_3631881] using wordTrace_append hprefix tailTrace_3631881
  have hstable : (prefixWord ++ tailWord_3631881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631881).length < 2 ^ (prefixWord ++ tailWord_3631881).sum := by decide
  have hdescent : baseEnd_3631881 < baseStart_3631881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631891 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 4]
def baseStart_3631891 : Nat := 118140960795 + 3631891 * 2 ^ 59
def prefixEnd_3631891 : Nat := 4983230072969 + 3 ^ 40 * 3631891 * 2
def baseEnd_3631891 : Nat := 1864905767738554943459743

theorem tailTrace_3631891 : CollatzResearch.WordTrace tailWord_3631891 prefixEnd_3631891 1864905767738554943459743 := by
  unfold tailWord_3631891
  simp only [CollatzResearch.WordTrace]
  refine ⟨132465947285286659445087527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88310631523524439630058351 132465947285286659445087527)
  ·
    refine ⟨198698920927929989167631291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132465947285286659445087527 198698920927929989167631291)
    ·
      refine ⟨298048381391894983751446937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198698920927929989167631291 298048381391894983751446937)
      ·
        refine ⟨223536286043921237813585203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298048381391894983751446937 223536286043921237813585203)
        ·
          refine ⟨335304429065881856720377805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223536286043921237813585203 335304429065881856720377805)
          ·
            refine ⟨125739160899705696270141677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335304429065881856720377805 125739160899705696270141677)
            ·
              refine ⟨47152185337389636101303129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125739160899705696270141677 47152185337389636101303129)
              ·
                refine ⟨35364139003042227075977347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47152185337389636101303129 35364139003042227075977347)
                ·
                  refine ⟨53046208504563340613966021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35364139003042227075977347 53046208504563340613966021)
                  ·
                    refine ⟨9946164094605626365118629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53046208504563340613966021 9946164094605626365118629)
                    ·
                      refine ⟨1864905767738554943459743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9946164094605626365118629 1864905767738554943459743)
                      ·
                        rfl

theorem cell23_3631891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_3631891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631891 prefixEnd_3631891 := by exact prefixLift 3631891
  have htrace : WordTrace (prefixWord ++ tailWord_3631891) baseStart_3631891 baseEnd_3631891 := by
    simpa [prefixWord, tailWord_3631891, baseEnd_3631891] using wordTrace_append hprefix tailTrace_3631891
  have hstable : (prefixWord ++ tailWord_3631891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631891).length < 2 ^ (prefixWord ++ tailWord_3631891).sum := by decide
  have hdescent : baseEnd_3631891 < baseStart_3631891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631912 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_3631912 : Nat := 118140960795 + 3631912 * 2 ^ 59
def prefixEnd_3631912 : Nat := 4983230072969 + 3 ^ 40 * 3631912 * 2
def baseEnd_3631912 : Nat := 1864916550832299361297147

theorem tailTrace_3631912 : CollatzResearch.WordTrace tailWord_3631912 prefixEnd_3631912 1864916550832299361297147 := by
  unfold tailWord_3631912
  simp only [CollatzResearch.WordTrace]
  refine ⟨66233356609105290015800995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88311142145473720021067993 66233356609105290015800995)
  ·
    refine ⟨99350034913657935023701493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66233356609105290015800995 99350034913657935023701493)
    ·
      refine ⟨9314065773155431408472015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99350034913657935023701493 9314065773155431408472015)
      ·
        refine ⟨13971098659733147112708023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9314065773155431408472015 13971098659733147112708023)
        ·
          refine ⟨20956647989599720669062035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13971098659733147112708023 20956647989599720669062035)
          ·
            refine ⟨31434971984399581003593053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20956647989599720669062035 31434971984399581003593053)
            ·
              refine ⟨11788114494149842876347395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31434971984399581003593053 11788114494149842876347395)
              ·
                refine ⟨17682171741224764314521093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11788114494149842876347395 17682171741224764314521093)
                ·
                  refine ⟨3315407201479643308972705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17682171741224764314521093 3315407201479643308972705)
                  ·
                    refine ⟨2486555401109732481729529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3315407201479643308972705 2486555401109732481729529)
                    ·
                      refine ⟨1864916550832299361297147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2486555401109732481729529 1864916550832299361297147)
                      ·
                        rfl

theorem cell23_3631912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_3631912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631912 prefixEnd_3631912 := by exact prefixLift 3631912
  have htrace : WordTrace (prefixWord ++ tailWord_3631912) baseStart_3631912 baseEnd_3631912 := by
    simpa [prefixWord, tailWord_3631912, baseEnd_3631912] using wordTrace_append hprefix tailTrace_3631912
  have hstable : (prefixWord ++ tailWord_3631912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631912).length < 2 ^ (prefixWord ++ tailWord_3631912).sum := by decide
  have hdescent : baseEnd_3631912 < baseStart_3631912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631928 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 2, 3, 3]
def baseStart_3631928 : Nat := 118140960795 + 3631928 * 2 ^ 59
def prefixEnd_3631928 : Nat := 4983230072969 + 3 ^ 40 * 3631928 * 2
def baseEnd_3631928 : Nat := 1864924766522771298697073

theorem tailTrace_3631928 : CollatzResearch.WordTrace tailWord_3631928 prefixEnd_3631928 1864924766522771298697073 := by
  unfold tailWord_3631928
  simp only [CollatzResearch.WordTrace]
  refine ⟨66233648393076307382092219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88311531190768409842789625 66233648393076307382092219)
  ·
    refine ⟨99350472589614461073138329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66233648393076307382092219 99350472589614461073138329)
    ·
      refine ⟨74512854442210845804853747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99350472589614461073138329 74512854442210845804853747)
      ·
        refine ⟨111769281663316268707280621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74512854442210845804853747 111769281663316268707280621)
        ·
          refine ⟨41913480623743600765230233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111769281663316268707280621 41913480623743600765230233)
          ·
            refine ⟨31435110467807700573922675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41913480623743600765230233 31435110467807700573922675)
            ·
              refine ⟨47152665701711550860884013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31435110467807700573922675 47152665701711550860884013)
              ·
                refine ⟨17682249638141831572831505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47152665701711550860884013 17682249638141831572831505)
                ·
                  refine ⟨13261687228606373679623629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17682249638141831572831505 13261687228606373679623629)
                  ·
                    refine ⟨4973132710727390129858861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13261687228606373679623629 4973132710727390129858861)
                    ·
                      refine ⟨1864924766522771298697073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4973132710727390129858861 1864924766522771298697073)
                      ·
                        rfl

theorem cell23_3631928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_3631928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631928 prefixEnd_3631928 := by exact prefixLift 3631928
  have htrace : WordTrace (prefixWord ++ tailWord_3631928) baseStart_3631928 baseEnd_3631928 := by
    simpa [prefixWord, tailWord_3631928, baseEnd_3631928] using wordTrace_append hprefix tailTrace_3631928
  have hstable : (prefixWord ++ tailWord_3631928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631928).length < 2 ^ (prefixWord ++ tailWord_3631928).sum := by decide
  have hdescent : baseEnd_3631928 < baseStart_3631928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631941 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_3631941 : Nat := 118140960795 + 3631941 * 2 ^ 59
def prefixEnd_3631941 : Nat := 4983230072969 + 3 ^ 40 * 3631941 * 2
def baseEnd_3631941 : Nat := 1864931441771279747834513

theorem tailTrace_3631941 : CollatzResearch.WordTrace tailWord_3631941 prefixEnd_3631941 1864931441771279747834513 := by
  unfold tailWord_3631941
  simp only [CollatzResearch.WordTrace]
  refine ⟨132467770935105517984407677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88311847290070345322938451 132467770935105517984407677)
  ·
    refine ⟨49675414100664569244152879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132467770935105517984407677 49675414100664569244152879)
    ·
      refine ⟨74513121150996853866229319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49675414100664569244152879 74513121150996853866229319)
      ·
        refine ⟨111769681726495280799343979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74513121150996853866229319 111769681726495280799343979)
        ·
          refine ⟨167654522589742921199015969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111769681726495280799343979 167654522589742921199015969)
          ·
            refine ⟨125740891942307190899261977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167654522589742921199015969 125740891942307190899261977)
            ·
              refine ⟨94305668956730393174446483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125740891942307190899261977 94305668956730393174446483)
              ·
                refine ⟨141458503435095589761669725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94305668956730393174446483 141458503435095589761669725)
                ·
                  refine ⟨53046938788160846160626147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141458503435095589761669725 53046938788160846160626147)
                  ·
                    refine ⟨79570408182241269240939221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53046938788160846160626147 79570408182241269240939221)
                    ·
                      refine ⟨1864931441771279747834513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79570408182241269240939221 1864931441771279747834513)
                      ·
                        rfl

theorem cell23_3631941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_3631941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631941 prefixEnd_3631941 := by exact prefixLift 3631941
  have htrace : WordTrace (prefixWord ++ tailWord_3631941) baseStart_3631941 baseEnd_3631941 := by
    simpa [prefixWord, tailWord_3631941, baseEnd_3631941] using wordTrace_append hprefix tailTrace_3631941
  have hstable : (prefixWord ++ tailWord_3631941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631941).length < 2 ^ (prefixWord ++ tailWord_3631941).sum := by decide
  have hdescent : baseEnd_3631941 < baseStart_3631941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631948 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 1, 7]
def baseStart_3631948 : Nat := 118140960795 + 3631948 * 2 ^ 59
def prefixEnd_3631948 : Nat := 4983230072969 + 3 ^ 40 * 3631948 * 2
def baseEnd_3631948 : Nat := 621645012045287073482327

theorem tailTrace_3631948 : CollatzResearch.WordTrace tailWord_3631948 prefixEnd_3631948 621645012045287073482327 := by
  unfold tailWord_3631948
  simp only [CollatzResearch.WordTrace]
  refine ⟨66234013123040079089956249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88312017497386772119941665 66234013123040079089956249)
  ·
    refine ⟨49675509842280059317467187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66234013123040079089956249 49675509842280059317467187)
    ·
      refine ⟨74513264763420088976200781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49675509842280059317467187 74513264763420088976200781)
      ·
        refine ⟨27942474286282533366075293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74513264763420088976200781 27942474286282533366075293)
        ·
          refine ⟨10478427857355950012278235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27942474286282533366075293 10478427857355950012278235)
          ·
            refine ⟨15717641786033925018417353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10478427857355950012278235 15717641786033925018417353)
            ·
              refine ⟨11788231339525443763813015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15717641786033925018417353 11788231339525443763813015)
              ·
                refine ⟨17682347009288165645719523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11788231339525443763813015 17682347009288165645719523)
                ·
                  refine ⟨26523520513932248468579285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17682347009288165645719523 26523520513932248468579285)
                  ·
                    refine ⟨621645012045287073482327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26523520513932248468579285 621645012045287073482327)
                    ·
                      rfl

theorem cell23_3631948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_3631948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631948 prefixEnd_3631948 := by exact prefixLift 3631948
  have htrace : WordTrace (prefixWord ++ tailWord_3631948) baseStart_3631948 baseEnd_3631948 := by
    simpa [prefixWord, tailWord_3631948, baseEnd_3631948] using wordTrace_append hprefix tailTrace_3631948
  have hstable : (prefixWord ++ tailWord_3631948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631948).length < 2 ^ (prefixWord ++ tailWord_3631948).sum := by decide
  have hdescent : baseEnd_3631948 < baseStart_3631948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632005 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 2, 2, 3]
def baseStart_3632005 : Nat := 118140960795 + 3632005 * 2 ^ 59
def prefixEnd_3632005 : Nat := 4983230072969 + 3 ^ 40 * 3632005 * 2
def baseEnd_3632005 : Nat := 1864964304533167497434219

theorem tailTrace_3632005 : CollatzResearch.WordTrace tailWord_3632005 prefixEnd_3632005 1864964304533167497434219 := by
  unfold tailWord_3632005
  simp only [CollatzResearch.WordTrace]
  refine ⟨132470105206873656914737469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88313403471249104609824979 132470105206873656914737469)
  ·
    refine ⟨49676289452577621343026551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132470105206873656914737469 49676289452577621343026551)
    ·
      refine ⟨74514434178866432014539827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49676289452577621343026551 74514434178866432014539827)
      ·
        refine ⟨111771651268299648021809741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74514434178866432014539827 111771651268299648021809741)
        ·
          refine ⟨41914369225612368008178653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111771651268299648021809741 41914369225612368008178653)
          ·
            refine ⟨15717888459604638003066995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41914369225612368008178653 15717888459604638003066995)
            ·
              refine ⟨23576832689406957004600493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15717888459604638003066995 23576832689406957004600493)
              ·
                refine ⟨8841312258527608876725185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23576832689406957004600493 8841312258527608876725185)
                ·
                  refine ⟨6630984193895706657543889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8841312258527608876725185 6630984193895706657543889)
                  ·
                    refine ⟨4973238145421779993157917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6630984193895706657543889 4973238145421779993157917)
                    ·
                      refine ⟨1864964304533167497434219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4973238145421779993157917 1864964304533167497434219)
                      ·
                        rfl

theorem cell23_3632005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_3632005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632005 prefixEnd_3632005 := by exact prefixLift 3632005
  have htrace : WordTrace (prefixWord ++ tailWord_3632005) baseStart_3632005 baseEnd_3632005 := by
    simpa [prefixWord, tailWord_3632005, baseEnd_3632005] using wordTrace_append hprefix tailTrace_3632005
  have hstable : (prefixWord ++ tailWord_3632005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632005).length < 2 ^ (prefixWord ++ tailWord_3632005).sum := by decide
  have hdescent : baseEnd_3632005 < baseStart_3632005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632062 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_3632062 : Nat := 118140960795 + 3632062 * 2 ^ 59
def prefixEnd_3632062 : Nat := 4983230072969 + 3 ^ 40 * 3632062 * 2
def baseEnd_3632062 : Nat := 1864993572930473774421457

theorem tailTrace_3632062 : CollatzResearch.WordTrace tailWord_3632062 prefixEnd_3632062 1864993572930473774421457 := by
  unfold tailWord_3632062
  simp only [CollatzResearch.WordTrace]
  refine ⟨16559023020958394456195305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88314789445111437099708293 16559023020958394456195305)
  ·
    refine ⟨12419267265718795842146479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16559023020958394456195305 12419267265718795842146479)
    ·
      refine ⟨18628900898578193763219719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12419267265718795842146479 18628900898578193763219719)
      ·
        refine ⟨27943351347867290644829579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18628900898578193763219719 27943351347867290644829579)
        ·
          refine ⟨41915027021800935967244369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27943351347867290644829579 41915027021800935967244369)
          ·
            refine ⟨31436270266350701975433277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41915027021800935967244369 31436270266350701975433277)
            ·
              refine ⟨11788601349881513240787479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31436270266350701975433277 11788601349881513240787479)
              ·
                refine ⟨17682902024822269861181219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11788601349881513240787479 17682902024822269861181219)
                ·
                  refine ⟨26524353037233404791771829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17682902024822269861181219 26524353037233404791771829)
                  ·
                    refine ⟨2486658097240631699228609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26524353037233404791771829 2486658097240631699228609)
                    ·
                      refine ⟨1864993572930473774421457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2486658097240631699228609 1864993572930473774421457)
                      ·
                        rfl

theorem cell23_3632062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_3632062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632062 prefixEnd_3632062 := by exact prefixLift 3632062
  have htrace : WordTrace (prefixWord ++ tailWord_3632062) baseStart_3632062 baseEnd_3632062 := by
    simpa [prefixWord, tailWord_3632062, baseEnd_3632062] using wordTrace_append hprefix tailTrace_3632062
  have hstable : (prefixWord ++ tailWord_3632062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632062).length < 2 ^ (prefixWord ++ tailWord_3632062).sum := by decide
  have hdescent : baseEnd_3632062 < baseStart_3632062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632072 : List Nat := [2, 1, 3, 1, 5, 1, 1, 3, 1, 5]
def baseStart_3632072 : Nat := 118140960795 + 3632072 * 2 ^ 59
def prefixEnd_3632072 : Nat := 4983230072969 + 3 ^ 40 * 3632072 * 2
def baseEnd_3632072 : Nat := 621666235912339578432137

theorem tailTrace_3632072 : CollatzResearch.WordTrace tailWord_3632072 prefixEnd_3632072 621666235912339578432137 := by
  unfold tailWord_3632072
  simp only [CollatzResearch.WordTrace]
  refine ⟨66236274448815463678713235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88315032598420618238284313 66236274448815463678713235)
  ·
    refine ⟨99354411673223195518069853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66236274448815463678713235 99354411673223195518069853)
    ·
      refine ⟨37257904377458698319276195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99354411673223195518069853 37257904377458698319276195)
      ·
        refine ⟨55886856566188047478914293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37257904377458698319276195 55886856566188047478914293)
        ·
          refine ⟨5239392803080129451148215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55886856566188047478914293 5239392803080129451148215)
          ·
            refine ⟨7859089204620194176722323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5239392803080129451148215 7859089204620194176722323)
            ·
              refine ⟨11788633806930291265083485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7859089204620194176722323 11788633806930291265083485)
              ·
                refine ⟨4420737677598859224406307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11788633806930291265083485 4420737677598859224406307)
                ·
                  refine ⟨6631106516398288836609461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4420737677598859224406307 6631106516398288836609461)
                  ·
                    refine ⟨621666235912339578432137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6631106516398288836609461 621666235912339578432137)
                    ·
                      rfl

theorem cell23_3632072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_3632072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632072 prefixEnd_3632072 := by exact prefixLift 3632072
  have htrace : WordTrace (prefixWord ++ tailWord_3632072) baseStart_3632072 baseEnd_3632072 := by
    simpa [prefixWord, tailWord_3632072, baseEnd_3632072] using wordTrace_append hprefix tailTrace_3632072
  have hstable : (prefixWord ++ tailWord_3632072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632072).length < 2 ^ (prefixWord ++ tailWord_3632072).sum := by decide
  have hdescent : baseEnd_3632072 < baseStart_3632072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632086 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_3632086 : Nat := 118140960795 + 3632086 * 2 ^ 59
def prefixEnd_3632086 : Nat := 4983230072969 + 3 ^ 40 * 3632086 * 2
def baseEnd_3632086 : Nat := 1865005896466181680521347

theorem tailTrace_3632086 : CollatzResearch.WordTrace tailWord_3632086 prefixEnd_3632086 1865005896466181680521347 := by
  unfold tailWord_3632086
  simp only [CollatzResearch.WordTrace]
  refine ⟨8279566219973762984277257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88315373013053471832290741 8279566219973762984277257)
  ·
    refine ⟨6209674664980322238207943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8279566219973762984277257 6209674664980322238207943)
    ·
      refine ⟨9314511997470483357311915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6209674664980322238207943 9314511997470483357311915)
      ·
        refine ⟨13971767996205725035967873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9314511997470483357311915 13971767996205725035967873)
        ·
          refine ⟨10478825997154293776975905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13971767996205725035967873 10478825997154293776975905)
          ·
            refine ⟨7859119497865720332731929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10478825997154293776975905 7859119497865720332731929)
            ·
              refine ⟨5894339623399290249548947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7859119497865720332731929 5894339623399290249548947)
              ·
                refine ⟨8841509435098935374323421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5894339623399290249548947 8841509435098935374323421)
                ·
                  refine ⟨3315566038162100765371283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8841509435098935374323421 3315566038162100765371283)
                  ·
                    refine ⟨4973349057243151148056925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3315566038162100765371283 4973349057243151148056925)
                    ·
                      refine ⟨1865005896466181680521347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4973349057243151148056925 1865005896466181680521347)
                      ·
                        rfl

theorem cell23_3632086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_3632086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632086 prefixEnd_3632086 := by exact prefixLift 3632086
  have htrace : WordTrace (prefixWord ++ tailWord_3632086) baseStart_3632086 baseEnd_3632086 := by
    simpa [prefixWord, tailWord_3632086, baseEnd_3632086] using wordTrace_append hprefix tailTrace_3632086
  have hstable : (prefixWord ++ tailWord_3632086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632086).length < 2 ^ (prefixWord ++ tailWord_3632086).sum := by decide
  have hdescent : baseEnd_3632086 < baseStart_3632086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632125 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_3632125 : Nat := 118140960795 + 3632125 * 2 ^ 59
def prefixEnd_3632125 : Nat := 4983230072969 + 3 ^ 40 * 3632125 * 2
def baseEnd_3632125 : Nat := 1865025922211707027933667

theorem tailTrace_3632125 : CollatzResearch.WordTrace tailWord_3632125 prefixEnd_3632125 1865025922211707027933667 := by
  unfold tailWord_3632125
  simp only [CollatzResearch.WordTrace]
  refine ⟨132474481966438917409105829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88316321310959278272737219 132474481966438917409105829)
  ·
    refine ⟨24838965368707297014207343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132474481966438917409105829 24838965368707297014207343)
    ·
      refine ⟨37258448053060945521311015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24838965368707297014207343 37258448053060945521311015)
      ·
        refine ⟨55887672079591418281966523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37258448053060945521311015 55887672079591418281966523)
        ·
          refine ⟨83831508119387127422949785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55887672079591418281966523 83831508119387127422949785)
          ·
            refine ⟨62873631089540345567212339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83831508119387127422949785 62873631089540345567212339)
            ·
              refine ⟨94310446634310518350818509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62873631089540345567212339 94310446634310518350818509)
              ·
                refine ⟨35366417487866444381556941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94310446634310518350818509 35366417487866444381556941)
                ·
                  refine ⟨13262406557949916643083853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35366417487866444381556941 13262406557949916643083853)
                  ·
                    refine ⟨4973402459231218741156445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13262406557949916643083853 4973402459231218741156445)
                    ·
                      refine ⟨1865025922211707027933667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4973402459231218741156445 1865025922211707027933667)
                      ·
                        rfl

theorem cell23_3632125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_3632125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632125 prefixEnd_3632125 := by exact prefixLift 3632125
  have htrace : WordTrace (prefixWord ++ tailWord_3632125) baseStart_3632125 baseEnd_3632125 := by
    simpa [prefixWord, tailWord_3632125, baseEnd_3632125] using wordTrace_append hprefix tailTrace_3632125
  have hstable : (prefixWord ++ tailWord_3632125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632125).length < 2 ^ (prefixWord ++ tailWord_3632125).sum := by decide
  have hdescent : baseEnd_3632125 < baseStart_3632125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632159 : List Nat := [1, 1, 2, 4, 1, 4, 1, 3, 2, 1, 3]
def baseStart_3632159 : Nat := 118140960795 + 3632159 * 2 ^ 59
def prefixEnd_3632159 : Nat := 4983230072969 + 3 ^ 40 * 3632159 * 2
def baseEnd_3632159 : Nat := 1865043380553959894908511

theorem tailTrace_3632159 : CollatzResearch.WordTrace tailWord_3632159 prefixEnd_3632159 1865043380553959894908511 := by
  unfold tailWord_3632159
  simp only [CollatzResearch.WordTrace]
  refine ⟨132475722048315741215843531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88317148032210494143895687 132475722048315741215843531)
  ·
    refine ⟨198713583072473611823765297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132475722048315741215843531 198713583072473611823765297)
    ·
      refine ⟨149035187304355208867823973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198713583072473611823765297 149035187304355208867823973)
      ·
        refine ⟨27944097619566601662716995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149035187304355208867823973 27944097619566601662716995)
        ·
          refine ⟨41916146429349902494075493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27944097619566601662716995 41916146429349902494075493)
          ·
            refine ⟨7859277455503106717639155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41916146429349902494075493 7859277455503106717639155)
            ·
              refine ⟨11788916183254660076458733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7859277455503106717639155 11788916183254660076458733)
              ·
                refine ⟨4420843568720497528672025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11788916183254660076458733 4420843568720497528672025)
                ·
                  refine ⟨3315632676540373146504019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4420843568720497528672025 3315632676540373146504019)
                  ·
                    refine ⟨4973449014810559719756029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3315632676540373146504019 4973449014810559719756029)
                    ·
                      refine ⟨1865043380553959894908511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4973449014810559719756029 1865043380553959894908511)
                      ·
                        rfl

theorem cell23_3632159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_3632159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632159 prefixEnd_3632159 := by exact prefixLift 3632159
  have htrace : WordTrace (prefixWord ++ tailWord_3632159) baseStart_3632159 baseEnd_3632159 := by
    simpa [prefixWord, tailWord_3632159, baseEnd_3632159] using wordTrace_append hprefix tailTrace_3632159
  have hstable : (prefixWord ++ tailWord_3632159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632159).length < 2 ^ (prefixWord ++ tailWord_3632159).sum := by decide
  have hdescent : baseEnd_3632159 < baseStart_3632159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632195 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 4]
def baseStart_3632195 : Nat := 118140960795 + 3632195 * 2 ^ 59
def prefixEnd_3632195 : Nat := 4983230072969 + 3 ^ 40 * 3632195 * 2
def baseEnd_3632195 : Nat := 1865061865857521754058345

theorem tailTrace_3632195 : CollatzResearch.WordTrace tailWord_3632195 prefixEnd_3632195 1865061865857521754058345 := by
  unfold tailWord_3632195
  simp only [CollatzResearch.WordTrace]
  refine ⟨132477035076185319364154039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88318023384123546242769359 132477035076185319364154039)
  ·
    refine ⟨198715552614277979046231059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132477035076185319364154039 198715552614277979046231059)
    ·
      refine ⟨298073328921416968569346589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198715552614277979046231059 298073328921416968569346589)
      ·
        refine ⟨111777498345531363213504971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298073328921416968569346589 111777498345531363213504971)
        ·
          refine ⟨167666247518297044820257457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111777498345531363213504971 167666247518297044820257457)
          ·
            refine ⟨125749685638722783615193093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167666247518297044820257457 125749685638722783615193093)
            ·
              refine ⟨23578066057260521927848705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125749685638722783615193093 23578066057260521927848705)
              ·
                refine ⟨17683549542945391445886529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23578066057260521927848705 17683549542945391445886529)
                ·
                  refine ⟨13262662157209043584414897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17683549542945391445886529 13262662157209043584414897)
                  ·
                    refine ⟨9946996617906782688311173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13262662157209043584414897 9946996617906782688311173)
                    ·
                      refine ⟨1865061865857521754058345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9946996617906782688311173 1865061865857521754058345)
                      ·
                        rfl

theorem cell23_3632195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_3632195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632195 prefixEnd_3632195 := by exact prefixLift 3632195
  have htrace : WordTrace (prefixWord ++ tailWord_3632195) baseStart_3632195 baseEnd_3632195 := by
    simpa [prefixWord, tailWord_3632195, baseEnd_3632195] using wordTrace_append hprefix tailTrace_3632195
  have hstable : (prefixWord ++ tailWord_3632195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632195).length < 2 ^ (prefixWord ++ tailWord_3632195).sum := by decide
  have hdescent : baseEnd_3632195 < baseStart_3632195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632272 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 1, 6, 2]
def baseStart_3632272 : Nat := 118140960795 + 3632272 * 2 ^ 59
def prefixEnd_3632272 : Nat := 4983230072969 + 3 ^ 40 * 3632272 * 2
def baseEnd_3632272 : Nat := 1865101403867917952795491

theorem tailTrace_3632272 : CollatzResearch.WordTrace tailWord_3632272 prefixEnd_3632272 1865101403867917952795491 := by
  unfold tailWord_3632272
  simp only [CollatzResearch.WordTrace]
  refine ⟨66239921748453180757353535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88319895664604241009804713 66239921748453180757353535)
  ·
    refine ⟨99359882622679771136030303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66239921748453180757353535 99359882622679771136030303)
    ·
      refine ⟨149039823934019656704045455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99359882622679771136030303 149039823934019656704045455)
      ·
        refine ⟨223559735901029485056068183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149039823934019656704045455 223559735901029485056068183)
        ·
          refine ⟨335339603851544227584102275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223559735901029485056068183 335339603851544227584102275)
          ·
            refine ⟨503009405777316341376153413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335339603851544227584102275 503009405777316341376153413)
            ·
              refine ⟨94314263583246814008028765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 503009405777316341376153413 94314263583246814008028765)
              ·
                refine ⟨35367848843717555253010787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94314263583246814008028765 35367848843717555253010787)
                ·
                  refine ⟨53051773265576332879516181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35367848843717555253010787 53051773265576332879516181)
                  ·
                    refine ⟨2486801871823890603727321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53051773265576332879516181 2486801871823890603727321)
                    ·
                      refine ⟨1865101403867917952795491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2486801871823890603727321 1865101403867917952795491)
                      ·
                        rfl

theorem cell23_3632272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 6, 2].length) (baseStart_3632272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632272 prefixEnd_3632272 := by exact prefixLift 3632272
  have htrace : WordTrace (prefixWord ++ tailWord_3632272) baseStart_3632272 baseEnd_3632272 := by
    simpa [prefixWord, tailWord_3632272, baseEnd_3632272] using wordTrace_append hprefix tailTrace_3632272
  have hstable : (prefixWord ++ tailWord_3632272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632272).length < 2 ^ (prefixWord ++ tailWord_3632272).sum := by decide
  have hdescent : baseEnd_3632272 < baseStart_3632272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632315 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 6]
def baseStart_3632315 : Nat := 118140960795 + 3632315 * 2 ^ 59
def prefixEnd_3632315 : Nat := 4983230072969 + 3 ^ 40 * 3632315 * 2
def baseEnd_3632315 : Nat := 1865123483536061284557793

theorem tailTrace_3632315 : CollatzResearch.WordTrace tailWord_3632315 prefixEnd_3632315 1865123483536061284557793 := by
  unfold tailWord_3632315
  simp only [CollatzResearch.WordTrace]
  refine ⟨132481411835750579858522399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88320941223833719905681599 132481411835750579858522399)
  ·
    refine ⟨198722117753625869787783599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132481411835750579858522399 198722117753625869787783599)
    ·
      refine ⟨298083176630438804681675399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198722117753625869787783599 298083176630438804681675399)
      ·
        refine ⟨447124764945658207022513099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298083176630438804681675399 447124764945658207022513099)
        ·
          refine ⟨670687147418487310533769649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447124764945658207022513099 670687147418487310533769649)
          ·
            refine ⟨503015360563865482900327237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670687147418487310533769649 503015360563865482900327237)
            ·
              refine ⟨94315380105724778043811357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 503015360563865482900327237 94315380105724778043811357)
              ·
                refine ⟨35368267539646791766429259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94315380105724778043811357 35368267539646791766429259)
                ·
                  refine ⟨53052401309470187649643889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35368267539646791766429259 53052401309470187649643889)
                  ·
                    refine ⟨39789300982102640737232917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53052401309470187649643889 39789300982102640737232917)
                    ·
                      refine ⟨1865123483536061284557793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39789300982102640737232917 1865123483536061284557793)
                      ·
                        rfl

theorem cell23_3632315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_3632315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632315 prefixEnd_3632315 := by exact prefixLift 3632315
  have htrace : WordTrace (prefixWord ++ tailWord_3632315) baseStart_3632315 baseEnd_3632315 := by
    simpa [prefixWord, tailWord_3632315, baseEnd_3632315] using wordTrace_append hprefix tailTrace_3632315
  have hstable : (prefixWord ++ tailWord_3632315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632315).length < 2 ^ (prefixWord ++ tailWord_3632315).sum := by decide
  have hdescent : baseEnd_3632315 < baseStart_3632315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632316 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 3, 4]
def baseStart_3632316 : Nat := 118140960795 + 3632316 * 2 ^ 59
def prefixEnd_3632316 : Nat := 4983230072969 + 3 ^ 40 * 3632316 * 2
def baseEnd_3632316 : Nat := 621707999005571926881763

theorem tailTrace_3632316 : CollatzResearch.WordTrace tailWord_3632316 prefixEnd_3632316 621707999005571926881763 := by
  unfold tailWord_3632316
  simp only [CollatzResearch.WordTrace]
  refine ⟨66240724154373478514654401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88320965539164638019539201 66240724154373478514654401)
  ·
    refine ⟨49680543115780108885990801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66240724154373478514654401 49680543115780108885990801)
    ·
      refine ⟨37260407336835081664493101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49680543115780108885990801 37260407336835081664493101)
      ·
        refine ⟨13972652751313155624184913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37260407336835081664493101 13972652751313155624184913)
        ·
          refine ⟨10479489563484866718138685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13972652751313155624184913 10479489563484866718138685)
          ·
            refine ⟨3929808586306825019302007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10479489563484866718138685 3929808586306825019302007)
            ·
              refine ⟨5894712879460237528953011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3929808586306825019302007 5894712879460237528953011)
              ·
                refine ⟨8842069319190356293429517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5894712879460237528953011 8842069319190356293429517)
                ·
                  refine ⟨3315775994696383610036069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8842069319190356293429517 3315775994696383610036069)
                  ·
                    refine ⟨621707999005571926881763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3315775994696383610036069 621707999005571926881763)
                    ·
                      rfl

theorem cell23_3632316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_3632316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632316 prefixEnd_3632316 := by exact prefixLift 3632316
  have htrace : WordTrace (prefixWord ++ tailWord_3632316) baseStart_3632316 baseEnd_3632316 := by
    simpa [prefixWord, tailWord_3632316, baseEnd_3632316] using wordTrace_append hprefix tailTrace_3632316
  have hstable : (prefixWord ++ tailWord_3632316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632316).length < 2 ^ (prefixWord ++ tailWord_3632316).sum := by decide
  have hdescent : baseEnd_3632316 < baseStart_3632316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632325 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 2, 9]
def baseStart_3632325 : Nat := 118140960795 + 3632325 * 2 ^ 59
def prefixEnd_3632325 : Nat := 4983230072969 + 3 ^ 40 * 3632325 * 2
def baseEnd_3632325 : Nat := 621709539447535415144249

theorem tailTrace_3632325 : CollatzResearch.WordTrace tailWord_3632325 prefixEnd_3632325 621709539447535415144249 := by
  unfold tailWord_3632325
  simp only [CollatzResearch.WordTrace]
  refine ⟨132481776565714351566386429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88321184377142901044257619 132481776565714351566386429)
  ·
    refine ⟨49680666212142881837394911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132481776565714351566386429 49680666212142881837394911)
    ·
      refine ⟨74520999318214322756092367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49680666212142881837394911 74520999318214322756092367)
      ·
        refine ⟨111781498977321484134138551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74520999318214322756092367 111781498977321484134138551)
        ·
          refine ⟨167672248465982226201207827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111781498977321484134138551 167672248465982226201207827)
          ·
            refine ⟨251508372698973339301811741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167672248465982226201207827 251508372698973339301811741)
            ·
              refine ⟨94315639762115002238179403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251508372698973339301811741 94315639762115002238179403)
              ·
                refine ⟨141473459643172503357269105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94315639762115002238179403 141473459643172503357269105)
                ·
                  refine ⟨106105094732379377517951829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141473459643172503357269105 106105094732379377517951829)
                  ·
                    refine ⟨621709539447535415144249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 106105094732379377517951829 621709539447535415144249)
                    ·
                      rfl

theorem cell23_3632325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_3632325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632325 prefixEnd_3632325 := by exact prefixLift 3632325
  have htrace : WordTrace (prefixWord ++ tailWord_3632325) baseStart_3632325 baseEnd_3632325 := by
    simpa [prefixWord, tailWord_3632325, baseEnd_3632325] using wordTrace_append hprefix tailTrace_3632325
  have hstable : (prefixWord ++ tailWord_3632325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632325).length < 2 ^ (prefixWord ++ tailWord_3632325).sum := by decide
  have hdescent : baseEnd_3632325 < baseStart_3632325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632335 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 7]
def baseStart_3632335 : Nat := 118140960795 + 3632335 * 2 ^ 59
def prefixEnd_3632335 : Nat := 4983230072969 + 3 ^ 40 * 3632335 * 2
def baseEnd_3632335 : Nat := 1865133753149151206307701

theorem tailTrace_3632335 : CollatzResearch.WordTrace tailWord_3632335 prefixEnd_3632335 1865133753149151206307701 := by
  unfold tailWord_3632335
  simp only [CollatzResearch.WordTrace]
  refine ⟨132482141295678123274250459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88321427530452082182833639 132482141295678123274250459)
  ·
    refine ⟨198723211943517184911375689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132482141295678123274250459 198723211943517184911375689)
    ·
      refine ⟨149042408957637888683531767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198723211943517184911375689 149042408957637888683531767)
      ·
        refine ⟨223563613436456833025297651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149042408957637888683531767 223563613436456833025297651)
        ·
          refine ⟨335345420154685249537946477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223563613436456833025297651 335345420154685249537946477)
          ·
            refine ⟨125754532558006968576729929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335345420154685249537946477 125754532558006968576729929)
            ·
              refine ⟨94315899418505226432547447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125754532558006968576729929 94315899418505226432547447)
              ·
                refine ⟨141473849127757839648821171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94315899418505226432547447 141473849127757839648821171)
                ·
                  refine ⟨212210773691636759473231757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141473849127757839648821171 212210773691636759473231757)
                  ·
                    refine ⟨79579040134363784802461909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212210773691636759473231757 79579040134363784802461909)
                    ·
                      refine ⟨1865133753149151206307701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79579040134363784802461909 1865133753149151206307701)
                      ·
                        rfl

theorem cell23_3632335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_3632335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632335 prefixEnd_3632335 := by exact prefixLift 3632335
  have htrace : WordTrace (prefixWord ++ tailWord_3632335) baseStart_3632335 baseEnd_3632335 := by
    simpa [prefixWord, tailWord_3632335, baseEnd_3632335] using wordTrace_append hprefix tailTrace_3632335
  have hstable : (prefixWord ++ tailWord_3632335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632335).length < 2 ^ (prefixWord ++ tailWord_3632335).sum := by decide
  have hdescent : baseEnd_3632335 < baseStart_3632335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632366 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_3632366 : Nat := 118140960795 + 3632366 * 2 ^ 59
def prefixEnd_3632366 : Nat := 4983230072969 + 3 ^ 40 * 3632366 * 2
def baseEnd_3632366 : Nat := 1865149671049440585020059

theorem tailTrace_3632366 : CollatzResearch.WordTrace tailWord_3632366 prefixEnd_3632366 1865149671049440585020059 := by
  unfold tailWord_3632366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16560408994820726946078619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88322181305710543712419301 16560408994820726946078619)
  ·
    refine ⟨24840613492231090419117929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16560408994820726946078619 24840613492231090419117929)
    ·
      refine ⟨18630460119173317814338447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24840613492231090419117929 18630460119173317814338447)
      ·
        refine ⟨27945690178759976721507671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18630460119173317814338447 27945690178759976721507671)
        ·
          refine ⟨41918535268139965082261507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27945690178759976721507671 41918535268139965082261507)
          ·
            refine ⟨62877802902209947623392261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41918535268139965082261507 62877802902209947623392261)
            ·
              refine ⟨11789588044164365179386049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62877802902209947623392261 11789588044164365179386049)
              ·
                refine ⟨8842191033123273884539537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11789588044164365179386049 8842191033123273884539537)
                ·
                  refine ⟨6631643274842455413404653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8842191033123273884539537 6631643274842455413404653)
                  ·
                    refine ⟨2486866228065920780026745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6631643274842455413404653 2486866228065920780026745)
                    ·
                      refine ⟨1865149671049440585020059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2486866228065920780026745 1865149671049440585020059)
                      ·
                        rfl

theorem cell23_3632366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_3632366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632366 prefixEnd_3632366 := by exact prefixLift 3632366
  have htrace : WordTrace (prefixWord ++ tailWord_3632366) baseStart_3632366 baseEnd_3632366 := by
    simpa [prefixWord, tailWord_3632366, baseEnd_3632366] using wordTrace_append hprefix tailTrace_3632366
  have hstable : (prefixWord ++ tailWord_3632366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632366).length < 2 ^ (prefixWord ++ tailWord_3632366).sum := by decide
  have hdescent : baseEnd_3632366 < baseStart_3632366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632389 : List Nat := [1, 3, 1, 1, 2, 1, 3, 5, 2, 4]
def baseStart_3632389 : Nat := 118140960795 + 3632389 * 2 ^ 59
def prefixEnd_3632389 : Nat := 4983230072969 + 3 ^ 40 * 3632389 * 2
def baseEnd_3632389 : Nat := 621720493701497998344151

theorem tailTrace_3632389 : CollatzResearch.WordTrace tailWord_3632389 prefixEnd_3632389 621720493701497998344151 := by
  unfold tailWord_3632389
  simp only [CollatzResearch.WordTrace]
  refine ⟨132484110837482490496716221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88322740558321660331144147 132484110837482490496716221)
  ·
    refine ⟨49681541564055933936268583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132484110837482490496716221 49681541564055933936268583)
    ·
      refine ⟨74522312346083900904402875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49681541564055933936268583 74522312346083900904402875)
      ·
        refine ⟨111783468519125851356604313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74522312346083900904402875 111783468519125851356604313)
        ·
          refine ⟨83837601389344388517453235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111783468519125851356604313 83837601389344388517453235)
          ·
            refine ⟨125756402084016582776179853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83837601389344388517453235 125756402084016582776179853)
            ·
              refine ⟨47158650781506218541067445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125756402084016582776179853 47158650781506218541067445)
              ·
                refine ⟨4421123510766207988225073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47158650781506218541067445 4421123510766207988225073)
                ·
                  refine ⟨3315842633074655991168805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4421123510766207988225073 3315842633074655991168805)
                  ·
                    refine ⟨621720493701497998344151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3315842633074655991168805 621720493701497998344151)
                    ·
                      rfl

theorem cell23_3632389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_3632389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632389 prefixEnd_3632389 := by exact prefixLift 3632389
  have htrace : WordTrace (prefixWord ++ tailWord_3632389) baseStart_3632389 baseEnd_3632389 := by
    simpa [prefixWord, tailWord_3632389, baseEnd_3632389] using wordTrace_append hprefix tailTrace_3632389
  have hstable : (prefixWord ++ tailWord_3632389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632389).length < 2 ^ (prefixWord ++ tailWord_3632389).sum := by decide
  have hdescent : baseEnd_3632389 < baseStart_3632389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632396 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 5, 2, 2]
def baseStart_3632396 : Nat := 118140960795 + 3632396 * 2 ^ 59
def prefixEnd_3632396 : Nat := 4983230072969 + 3 ^ 40 * 3632396 * 2
def baseEnd_3632396 : Nat := 1865165075469075467644921

theorem tailTrace_3632396 : CollatzResearch.WordTrace tailWord_3632396 prefixEnd_3632396 1865165075469075467644921 := by
  unfold tailWord_3632396
  simp only [CollatzResearch.WordTrace]
  refine ⟨66242183074228565346110521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88322910765638087128147361 66242183074228565346110521)
  ·
    refine ⟨49681637305671424009582891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66242183074228565346110521 49681637305671424009582891)
    ·
      refine ⟨74522455958507136014374337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49681637305671424009582891 74522455958507136014374337)
      ·
        refine ⟨55891841968880352010780753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74522455958507136014374337 55891841968880352010780753)
        ·
          refine ⟨41918881476660264008085565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55891841968880352010780753 41918881476660264008085565)
          ·
            refine ⟨15719580553747599003032087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41918881476660264008085565 15719580553747599003032087)
            ·
              refine ⟨23579370830621398504548131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15719580553747599003032087 23579370830621398504548131)
              ·
                refine ⟨35369056245932097756822197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23579370830621398504548131 35369056245932097756822197)
                ·
                  refine ⟨3315849023056134164702081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35369056245932097756822197 3315849023056134164702081)
                  ·
                    refine ⟨2486886767292100623526561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3315849023056134164702081 2486886767292100623526561)
                    ·
                      refine ⟨1865165075469075467644921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2486886767292100623526561 1865165075469075467644921)
                      ·
                        rfl

theorem cell23_3632396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_3632396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632396 prefixEnd_3632396 := by exact prefixLift 3632396
  have htrace : WordTrace (prefixWord ++ tailWord_3632396) baseStart_3632396 baseEnd_3632396 := by
    simpa [prefixWord, tailWord_3632396, baseEnd_3632396] using wordTrace_append hprefix tailTrace_3632396
  have hstable : (prefixWord ++ tailWord_3632396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632396).length < 2 ^ (prefixWord ++ tailWord_3632396).sum := by decide
  have hdescent : baseEnd_3632396 < baseStart_3632396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632413 : List Nat := [1, 4, 2, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_3632413 : Nat := 118140960795 + 3632413 * 2 ^ 59
def prefixEnd_3632413 : Nat := 4983230072969 + 3 ^ 40 * 3632413 * 2
def baseEnd_3632413 : Nat := 1865173804640201901132343

theorem tailTrace_3632413 : CollatzResearch.WordTrace tailWord_3632413 prefixEnd_3632413 1865173804640201901132343 := by
  unfold tailWord_3632413
  simp only [CollatzResearch.WordTrace]
  refine ⟨132484986189395542595589893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88323324126263695063726595 132484986189395542595589893)
  ·
    refine ⟨24840934910511664236673105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132484986189395542595589893 24840934910511664236673105)
    ·
      refine ⟨18630701182883748177504829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24840934910511664236673105 18630701182883748177504829)
      ·
        refine ⟨6986512943581405566564311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18630701182883748177504829 6986512943581405566564311)
        ·
          refine ⟨10479769415372108349846467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6986512943581405566564311 10479769415372108349846467)
          ·
            refine ⟨15719654123058162524769701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10479769415372108349846467 15719654123058162524769701)
            ·
              refine ⟨2947435148073405473394319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15719654123058162524769701 2947435148073405473394319)
              ·
                refine ⟨4421152722110108210091479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2947435148073405473394319 4421152722110108210091479)
                ·
                  refine ⟨6631729083165162315137219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4421152722110108210091479 6631729083165162315137219)
                  ·
                    refine ⟨9947593624747743472705829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6631729083165162315137219 9947593624747743472705829)
                    ·
                      refine ⟨1865173804640201901132343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9947593624747743472705829 1865173804640201901132343)
                      ·
                        rfl

theorem cell23_3632413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_3632413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632413 prefixEnd_3632413 := by exact prefixLift 3632413
  have htrace : WordTrace (prefixWord ++ tailWord_3632413) baseStart_3632413 baseEnd_3632413 := by
    simpa [prefixWord, tailWord_3632413, baseEnd_3632413] using wordTrace_append hprefix tailTrace_3632413
  have hstable : (prefixWord ++ tailWord_3632413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632413).length < 2 ^ (prefixWord ++ tailWord_3632413).sum := by decide
  have hdescent : baseEnd_3632413 < baseStart_3632413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632470 : List Nat := [5, 2, 3, 1, 1, 2, 9]
def baseStart_3632470 : Nat := 118140960795 + 3632470 * 2 ^ 59
def prefixEnd_3632470 : Nat := 4983230072969 + 3 ^ 40 * 3632470 * 2
def baseEnd_3632470 : Nat := 23027198432561829359501

theorem tailTrace_3632470 : CollatzResearch.WordTrace tailWord_3632470 prefixEnd_3632470 23027198432561829359501 := by
  unfold tailWord_3632470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280441571886815083150929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88324710100126027553609909 8280441571886815083150929)
  ·
    refine ⟨6210331178915111312363197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8280441571886815083150929 6210331178915111312363197)
    ·
      refine ⟨2328874192093166742136199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6210331178915111312363197 2328874192093166742136199)
      ·
        refine ⟨3493311288139750113204299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2328874192093166742136199 3493311288139750113204299)
        ·
          refine ⟨5239966932209625169806449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493311288139750113204299 5239966932209625169806449)
          ·
            refine ⟨3929975199157218877354837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5239966932209625169806449 3929975199157218877354837)
            ·
              refine ⟨23027198432561829359501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3929975199157218877354837 23027198432561829359501)
              ·
                rfl

theorem cell23_3632470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 9].length) (baseStart_3632470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632470 prefixEnd_3632470 := by exact prefixLift 3632470
  have htrace : WordTrace (prefixWord ++ tailWord_3632470) baseStart_3632470 baseEnd_3632470 := by
    simpa [prefixWord, tailWord_3632470, baseEnd_3632470] using wordTrace_append hprefix tailTrace_3632470
  have hstable : (prefixWord ++ tailWord_3632470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632470).length < 2 ^ (prefixWord ++ tailWord_3632470).sum := by decide
  have hdescent : baseEnd_3632470 < baseStart_3632470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632503 : List Nat := [1, 1, 3, 1, 1, 2, 5, 3, 2, 2, 2]
def baseStart_3632503 : Nat := 118140960795 + 3632503 * 2 ^ 59
def prefixEnd_3632503 : Nat := 4983230072969 + 3 ^ 40 * 3632503 * 2
def baseEnd_3632503 : Nat := 1865220017899106549006929

theorem tailTrace_3632503 : CollatzResearch.WordTrace tailWord_3632503 prefixEnd_3632503 1865220017899106549006929 := by
  unfold tailWord_3632503
  simp only [CollatzResearch.WordTrace]
  refine ⟨132488268759069487966366163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88325512506046325310910775 132488268759069487966366163)
  ·
    refine ⟨198732403138604231949549245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132488268759069487966366163 198732403138604231949549245)
    ·
      refine ⟨74524651176976586981080967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198732403138604231949549245 74524651176976586981080967)
      ·
        refine ⟨111786976765464880471621451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74524651176976586981080967 111786976765464880471621451)
        ·
          refine ⟨167680465148197320707432177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111786976765464880471621451 167680465148197320707432177)
          ·
            refine ⟨125760348861147990530574133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167680465148197320707432177 125760348861147990530574133)
            ·
              refine ⟨11790032705732624112241325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125760348861147990530574133 11790032705732624112241325)
              ·
                refine ⟨4421262264649734042090497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11790032705732624112241325 4421262264649734042090497)
                ·
                  refine ⟨3315946698487300531567873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4421262264649734042090497 3315946698487300531567873)
                  ·
                    refine ⟨2486960023865475398675905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3315946698487300531567873 2486960023865475398675905)
                    ·
                      refine ⟨1865220017899106549006929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2486960023865475398675905 1865220017899106549006929)
                      ·
                        rfl

theorem cell23_3632503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 2, 2].length) (baseStart_3632503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632503 prefixEnd_3632503 := by exact prefixLift 3632503
  have htrace : WordTrace (prefixWord ++ tailWord_3632503) baseStart_3632503 baseEnd_3632503 := by
    simpa [prefixWord, tailWord_3632503, baseEnd_3632503] using wordTrace_append hprefix tailTrace_3632503
  have hstable : (prefixWord ++ tailWord_3632503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632503).length < 2 ^ (prefixWord ++ tailWord_3632503).sum := by decide
  have hdescent : baseEnd_3632503 < baseStart_3632503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632512 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 8]
def baseStart_3632512 : Nat := 118140960795 + 3632512 * 2 ^ 59
def prefixEnd_3632512 : Nat := 4983230072969 + 3 ^ 40 * 3632512 * 2
def baseEnd_3632512 : Nat := 1865224639224997013794387

theorem tailTrace_3632512 : CollatzResearch.WordTrace tailWord_3632512 prefixEnd_3632512 1865224639224997013794387 := by
  unfold tailWord_3632512
  simp only [CollatzResearch.WordTrace]
  refine ⟨66244298508018441251721895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88325731344024588335629193 66244298508018441251721895)
  ·
    refine ⟨99366447762027661877582843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66244298508018441251721895 99366447762027661877582843)
    ·
      refine ⟨149049671643041492816374265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99366447762027661877582843 149049671643041492816374265)
      ·
        refine ⟨111787253732281119612280699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149049671643041492816374265 111787253732281119612280699)
        ·
          refine ⟨167680880598421679418421049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111787253732281119612280699 167680880598421679418421049)
          ·
            refine ⟨125760660448816259563815787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167680880598421679418421049 125760660448816259563815787)
            ·
              refine ⟨188640990673224389345723681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125760660448816259563815787 188640990673224389345723681)
              ·
                refine ⟨141480743004918292009292761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188640990673224389345723681 141480743004918292009292761)
                ·
                  refine ⟨106110557253688719006969571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141480743004918292009292761 106110557253688719006969571)
                  ·
                    refine ⟨159165835880533078510454357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106110557253688719006969571 159165835880533078510454357)
                    ·
                      refine ⟨1865224639224997013794387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 159165835880533078510454357 1865224639224997013794387)
                      ·
                        rfl

theorem cell23_3632512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_3632512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632512 prefixEnd_3632512 := by exact prefixLift 3632512
  have htrace : WordTrace (prefixWord ++ tailWord_3632512) baseStart_3632512 baseEnd_3632512 := by
    simpa [prefixWord, tailWord_3632512, baseEnd_3632512] using wordTrace_append hprefix tailTrace_3632512
  have hstable : (prefixWord ++ tailWord_3632512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632512).length < 2 ^ (prefixWord ++ tailWord_3632512).sum := by decide
  have hdescent : baseEnd_3632512 < baseStart_3632512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632543 : List Nat := [1, 1, 2, 5, 1, 2, 4, 2, 5]
def baseStart_3632543 : Nat := 118140960795 + 3632543 * 2 ^ 59
def prefixEnd_3632543 : Nat := 4983230072969 + 3 ^ 40 * 3632543 * 2
def baseEnd_3632543 : Nat := 207248950791698488056305

theorem tailTrace_3632543 : CollatzResearch.WordTrace tailWord_3632543 prefixEnd_3632543 207248950791698488056305 := by
  unfold tailWord_3632543
  simp only [CollatzResearch.WordTrace]
  refine ⟨132489727678924574797822283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88326485119283049865214855 132489727678924574797822283)
  ·
    refine ⟨198734591518386862196733425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132489727678924574797822283 198734591518386862196733425)
    ·
      refine ⟨149050943638790146647550069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198734591518386862196733425 149050943638790146647550069)
      ·
        refine ⟨13973525966136576248207819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149050943638790146647550069 13973525966136576248207819)
        ·
          refine ⟨20960288949204864372311729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13973525966136576248207819 20960288949204864372311729)
          ·
            refine ⟨15720216711903648279233797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20960288949204864372311729 15720216711903648279233797)
            ·
              refine ⟨2947540633481934052356337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15720216711903648279233797 2947540633481934052356337)
              ·
                refine ⟨2210655475111450539267253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2947540633481934052356337 2210655475111450539267253)
                ·
                  refine ⟨207248950791698488056305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2210655475111450539267253 207248950791698488056305)
                  ·
                    rfl

theorem cell23_3632543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 5].length) (baseStart_3632543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632543 prefixEnd_3632543 := by exact prefixLift 3632543
  have htrace : WordTrace (prefixWord ++ tailWord_3632543) baseStart_3632543 baseEnd_3632543 := by
    simpa [prefixWord, tailWord_3632543, baseEnd_3632543] using wordTrace_append hprefix tailTrace_3632543
  have hstable : (prefixWord ++ tailWord_3632543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632543).length < 2 ^ (prefixWord ++ tailWord_3632543).sum := by decide
  have hdescent : baseEnd_3632543 < baseStart_3632543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632559 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 4]
def baseStart_3632559 : Nat := 118140960795 + 3632559 * 2 ^ 59
def prefixEnd_3632559 : Nat := 4983230072969 + 3 ^ 40 * 3632559 * 2
def baseEnd_3632559 : Nat := 1865248772815758329906671

theorem tailTrace_3632559 : CollatzResearch.WordTrace tailWord_3632559 prefixEnd_3632559 1865248772815758329906671 := by
  unfold tailWord_3632559
  simp only [CollatzResearch.WordTrace]
  refine ⟨132490311246866609530404731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88326874164577739686936487 132490311246866609530404731)
  ·
    refine ⟨198735466870299914295607097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132490311246866609530404731 198735466870299914295607097)
    ·
      refine ⟨149051600152724935721705323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198735466870299914295607097 149051600152724935721705323)
      ·
        refine ⟨223577400229087403582557985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149051600152724935721705323 223577400229087403582557985)
        ·
          refine ⟨167683050171815552686918489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223577400229087403582557985 167683050171815552686918489)
          ·
            refine ⟨125762287628861664515188867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167683050171815552686918489 125762287628861664515188867)
            ·
              refine ⟨188643431443292496772783301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125762287628861664515188867 188643431443292496772783301)
              ·
                refine ⟨35370643395617343144896869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188643431443292496772783301 35370643395617343144896869)
                ·
                  refine ⟨6631995636678251839668163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35370643395617343144896869 6631995636678251839668163)
                  ·
                    refine ⟨9947993455017377759502245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6631995636678251839668163 9947993455017377759502245)
                    ·
                      refine ⟨1865248772815758329906671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9947993455017377759502245 1865248772815758329906671)
                      ·
                        rfl

theorem cell23_3632559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_3632559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632559 prefixEnd_3632559 := by exact prefixLift 3632559
  have htrace : WordTrace (prefixWord ++ tailWord_3632559) baseStart_3632559 baseEnd_3632559 := by
    simpa [prefixWord, tailWord_3632559, baseEnd_3632559] using wordTrace_append hprefix tailTrace_3632559
  have hstable : (prefixWord ++ tailWord_3632559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632559).length < 2 ^ (prefixWord ++ tailWord_3632559).sum := by decide
  have hdescent : baseEnd_3632559 < baseStart_3632559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632576 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 4]
def baseStart_3632576 : Nat := 118140960795 + 3632576 * 2 ^ 59
def prefixEnd_3632576 : Nat := 4983230072969 + 3 ^ 40 * 3632576 * 2
def baseEnd_3632576 : Nat := 1865257501986884763394093

theorem tailTrace_3632576 : CollatzResearch.WordTrace tailWord_3632576 prefixEnd_3632576 1865257501986884763394093 := by
  unfold tailWord_3632576
  simp only [CollatzResearch.WordTrace]
  refine ⟨66245465643902510716886791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88327287525203347622515721 66245465643902510716886791)
  ·
    refine ⟨99368198465853766075330187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66245465643902510716886791 99368198465853766075330187)
    ·
      refine ⟨149052297698780649112995281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99368198465853766075330187 149052297698780649112995281)
      ·
        refine ⟨111789223274085486834746461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149052297698780649112995281 111789223274085486834746461)
        ·
          refine ⟨41920958727782057563029923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111789223274085486834746461 41920958727782057563029923)
          ·
            refine ⟨62881438091673086344544885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41920958727782057563029923 62881438091673086344544885)
            ·
              refine ⟨5895134821094351844801083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62881438091673086344544885 5895134821094351844801083)
              ·
                refine ⟨8842702231641527767201625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895134821094351844801083 8842702231641527767201625)
                ·
                  refine ⟨6632026673731145825401219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8842702231641527767201625 6632026673731145825401219)
                  ·
                    refine ⟨9948040010596718738101829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6632026673731145825401219 9948040010596718738101829)
                    ·
                      refine ⟨1865257501986884763394093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9948040010596718738101829 1865257501986884763394093)
                      ·
                        rfl

theorem cell23_3632576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_3632576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632576 prefixEnd_3632576 := by exact prefixLift 3632576
  have htrace : WordTrace (prefixWord ++ tailWord_3632576) baseStart_3632576 baseEnd_3632576 := by
    simpa [prefixWord, tailWord_3632576, baseEnd_3632576] using wordTrace_append hprefix tailTrace_3632576
  have hstable : (prefixWord ++ tailWord_3632576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632576).length < 2 ^ (prefixWord ++ tailWord_3632576).sum := by decide
  have hdescent : baseEnd_3632576 < baseStart_3632576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632666 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_3632666 : Nat := 118140960795 + 3632666 * 2 ^ 59
def prefixEnd_3632666 : Nat := 4983230072969 + 3 ^ 40 * 3632666 * 2
def baseEnd_3632666 : Nat := 1865303715245789411268679

theorem tailTrace_3632666 : CollatzResearch.WordTrace tailWord_3632666 prefixEnd_3632666 1865303715245789411268679 := by
  unfold tailWord_3632666
  simp only [CollatzResearch.WordTrace]
  refine ⟨33123553464369741701137463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88329475904985977869699901 33123553464369741701137463)
  ·
    refine ⟨49685330196554612551706195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33123553464369741701137463 49685330196554612551706195)
    ·
      refine ⟨74527995294831918827559293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49685330196554612551706195 74527995294831918827559293)
      ·
        refine ⟨27947998235561969560334735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74527995294831918827559293 27947998235561969560334735)
        ·
          refine ⟨41921997353342954340502103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27947998235561969560334735 41921997353342954340502103)
          ·
            refine ⟨62882996030014431510753155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41921997353342954340502103 62882996030014431510753155)
            ·
              refine ⟨94324494045021647266129733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62882996030014431510753155 94324494045021647266129733)
              ·
                refine ⟨17685842633441558862399325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94324494045021647266129733 17685842633441558862399325)
                ·
                  refine ⟨6632190987540584573399747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17685842633441558862399325 6632190987540584573399747)
                  ·
                    refine ⟨9948286481310876860099621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6632190987540584573399747 9948286481310876860099621)
                    ·
                      refine ⟨1865303715245789411268679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9948286481310876860099621 1865303715245789411268679)
                      ·
                        rfl

theorem cell23_3632666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_3632666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632666 prefixEnd_3632666 := by exact prefixLift 3632666
  have htrace : WordTrace (prefixWord ++ tailWord_3632666) baseStart_3632666 baseEnd_3632666 := by
    simpa [prefixWord, tailWord_3632666, baseEnd_3632666] using wordTrace_append hprefix tailTrace_3632666
  have hstable : (prefixWord ++ tailWord_3632666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632666).length < 2 ^ (prefixWord ++ tailWord_3632666).sum := by decide
  have hdescent : baseEnd_3632666 < baseStart_3632666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632696 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_3632696 : Nat := 118140960795 + 3632696 * 2 ^ 59
def prefixEnd_3632696 : Nat := 4983230072969 + 3 ^ 40 * 3632696 * 2
def baseEnd_3632696 : Nat := 1865319119665424293893541

theorem tailTrace_3632696 : CollatzResearch.WordTrace tailWord_3632696 prefixEnd_3632696 1865319119665424293893541 := by
  unfold tailWord_3632696
  simp only [CollatzResearch.WordTrace]
  refine ⟨66247654023685140964070971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88330205364913521285427961 66247654023685140964070971)
  ·
    refine ⟨99371481035527711446106457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66247654023685140964070971 99371481035527711446106457)
    ·
      refine ⟨74528610776645783584579843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99371481035527711446106457 74528610776645783584579843)
      ·
        refine ⟨111792916164968675376869765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74528610776645783584579843 111792916164968675376869765)
        ·
          refine ⟨20961171780931626633163081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111792916164968675376869765 20961171780931626633163081)
          ·
            refine ⟨15720878835698719974872311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20961171780931626633163081 15720878835698719974872311)
            ·
              refine ⟨23581318253548079962308467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15720878835698719974872311 23581318253548079962308467)
              ·
                refine ⟨35371977380322119943462701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23581318253548079962308467 35371977380322119943462701)
                ·
                  refine ⟨13264491517620794978798513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35371977380322119943462701 13264491517620794978798513)
                  ·
                    refine ⟨9948368638215596234098885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13264491517620794978798513 9948368638215596234098885)
                    ·
                      refine ⟨1865319119665424293893541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9948368638215596234098885 1865319119665424293893541)
                      ·
                        rfl

theorem cell23_3632696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_3632696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632696 prefixEnd_3632696 := by exact prefixLift 3632696
  have htrace : WordTrace (prefixWord ++ tailWord_3632696) baseStart_3632696 baseEnd_3632696 := by
    simpa [prefixWord, tailWord_3632696, baseEnd_3632696] using wordTrace_append hprefix tailTrace_3632696
  have hstable : (prefixWord ++ tailWord_3632696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632696).length < 2 ^ (prefixWord ++ tailWord_3632696).sum := by decide
  have hdescent : baseEnd_3632696 < baseStart_3632696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632703 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 5]
def baseStart_3632703 : Nat := 118140960795 + 3632703 * 2 ^ 59
def prefixEnd_3632703 : Nat := 4983230072969 + 3 ^ 40 * 3632703 * 2
def baseEnd_3632703 : Nat := 1865322714030005766506009

theorem tailTrace_3632703 : CollatzResearch.WordTrace tailWord_3632703 prefixEnd_3632703 1865322714030005766506009 := by
  unfold tailWord_3632703
  simp only [CollatzResearch.WordTrace]
  refine ⟨132495563358344922123646763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88330375572229948082431175 132495563358344922123646763)
  ·
    refine ⟨198743345037517383185470145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132495563358344922123646763 198743345037517383185470145)
    ·
      refine ⟨149057508778138037389102609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198743345037517383185470145 149057508778138037389102609)
      ·
        refine ⟨111793131583603528041826957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149057508778138037389102609 111793131583603528041826957)
        ·
          refine ⟨41922424343851323015685109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111793131583603528041826957 41922424343851323015685109)
          ·
            refine ⟨3930227282236061532720479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41922424343851323015685109 3930227282236061532720479)
            ·
              refine ⟨5895340923354092299080719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930227282236061532720479 5895340923354092299080719)
              ·
                refine ⟨8843011385031138448621079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895340923354092299080719 8843011385031138448621079)
                ·
                  refine ⟨13264517077546707672931619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8843011385031138448621079 13264517077546707672931619)
                  ·
                    refine ⟨19896775616320061509397429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13264517077546707672931619 19896775616320061509397429)
                    ·
                      refine ⟨1865322714030005766506009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19896775616320061509397429 1865322714030005766506009)
                      ·
                        rfl

theorem cell23_3632703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_3632703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632703 prefixEnd_3632703 := by exact prefixLift 3632703
  have htrace : WordTrace (prefixWord ++ tailWord_3632703) baseStart_3632703 baseEnd_3632703 := by
    simpa [prefixWord, tailWord_3632703, baseEnd_3632703] using wordTrace_append hprefix tailTrace_3632703
  have hstable : (prefixWord ++ tailWord_3632703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632703).length < 2 ^ (prefixWord ++ tailWord_3632703).sum := by decide
  have hdescent : baseEnd_3632703 < baseStart_3632703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632711 : List Nat := [1, 1, 4, 1, 6, 1, 2, 2, 1, 1, 3]
def baseStart_3632711 : Nat := 118140960795 + 3632711 * 2 ^ 59
def prefixEnd_3632711 : Nat := 4983230072969 + 3 ^ 40 * 3632711 * 2
def baseEnd_3632711 : Nat := 1865326821875241735205973

theorem tailTrace_3632711 : CollatzResearch.WordTrace tailWord_3632711 prefixEnd_3632711 1865326821875241735205973 := by
  unfold tailWord_3632711
  simp only [CollatzResearch.WordTrace]
  refine ⟨132495855142315939489937987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88330570094877292993291991 132495855142315939489937987)
  ·
    refine ⟨198743782713473909234906981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132495855142315939489937987 198743782713473909234906981)
    ·
      refine ⟨37264459258776357981545059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198743782713473909234906981 37264459258776357981545059)
      ·
        refine ⟨55896688888164536972317589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37264459258776357981545059 55896688888164536972317589)
        ·
          refine ⟨2620157291632712670577387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55896688888164536972317589 2620157291632712670577387)
          ·
            refine ⟨3930235937449069005866081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620157291632712670577387 3930235937449069005866081)
            ·
              refine ⟨2947676953086801754399561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3930235937449069005866081 2947676953086801754399561)
              ·
                refine ⟨2210757714815101315799671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2947676953086801754399561 2210757714815101315799671)
                ·
                  refine ⟨3316136572222651973699507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210757714815101315799671 3316136572222651973699507)
                  ·
                    refine ⟨4974204858333977960549261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3316136572222651973699507 4974204858333977960549261)
                    ·
                      refine ⟨1865326821875241735205973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4974204858333977960549261 1865326821875241735205973)
                      ·
                        rfl

theorem cell23_3632711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_3632711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632711 prefixEnd_3632711 := by exact prefixLift 3632711
  have htrace : WordTrace (prefixWord ++ tailWord_3632711) baseStart_3632711 baseEnd_3632711 := by
    simpa [prefixWord, tailWord_3632711, baseEnd_3632711] using wordTrace_append hprefix tailTrace_3632711
  have hstable : (prefixWord ++ tailWord_3632711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632711).length < 2 ^ (prefixWord ++ tailWord_3632711).sum := by decide
  have hdescent : baseEnd_3632711 < baseStart_3632711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632830 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 7]
def baseStart_3632830 : Nat := 118140960795 + 3632830 * 2 ^ 59
def prefixEnd_3632830 : Nat := 4983230072969 + 3 ^ 40 * 3632830 * 2
def baseEnd_3632830 : Nat := 207265325119236307735325

theorem tailTrace_3632830 : CollatzResearch.WordTrace tailWord_3632830 prefixEnd_3632830 207265325119236307735325 := by
  unfold tailWord_3632830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16562524428610602851689993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88333463619256548542346629 16562524428610602851689993)
  ·
    refine ⟨12421893321457952138767495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16562524428610602851689993 12421893321457952138767495)
    ·
      refine ⟨18632839982186928208151243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12421893321457952138767495 18632839982186928208151243)
      ·
        refine ⟨27949259973280392312226865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18632839982186928208151243 27949259973280392312226865)
        ·
          refine ⟨20961944979960294234170149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27949259973280392312226865 20961944979960294234170149)
          ·
            refine ⟨3930364683742555168906903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20961944979960294234170149 3930364683742555168906903)
            ·
              refine ⟨5895547025613832753360355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930364683742555168906903 5895547025613832753360355)
              ·
                refine ⟨8843320538420749130040533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895547025613832753360355 8843320538420749130040533)
                ·
                  refine ⟨207265325119236307735325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8843320538420749130040533 207265325119236307735325)
                  ·
                    rfl

theorem cell23_3632830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_3632830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632830 prefixEnd_3632830 := by exact prefixLift 3632830
  have htrace : WordTrace (prefixWord ++ tailWord_3632830) baseStart_3632830 baseEnd_3632830 := by
    simpa [prefixWord, tailWord_3632830, baseEnd_3632830] using wordTrace_append hprefix tailTrace_3632830
  have hstable : (prefixWord ++ tailWord_3632830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632830).length < 2 ^ (prefixWord ++ tailWord_3632830).sum := by decide
  have hdescent : baseEnd_3632830 < baseStart_3632830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632884 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_3632884 : Nat := 118140960795 + 3632884 * 2 ^ 59
def prefixEnd_3632884 : Nat := 4983230072969 + 3 ^ 40 * 3632884 * 2
def baseEnd_3632884 : Nat := 1865415654028469558342677

theorem tailTrace_3632884 : CollatzResearch.WordTrace tailWord_3632884 prefixEnd_3632884 1865415654028469558342677 := by
  unfold tailWord_3632884
  simp only [CollatzResearch.WordTrace]
  refine ⟨66251082485344595017992853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88334776647126126690657137 66251082485344595017992853)
  ·
    refine ⟨3105519491500527891468415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66251082485344595017992853 3105519491500527891468415)
    ·
      refine ⟨4658279237250791837202623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3105519491500527891468415 4658279237250791837202623)
      ·
        refine ⟨6987418855876187755803935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4658279237250791837202623 6987418855876187755803935)
        ·
          refine ⟨10481128283814281633705903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6987418855876187755803935 10481128283814281633705903)
          ·
            refine ⟨15721692425721422450558855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10481128283814281633705903 15721692425721422450558855)
            ·
              refine ⟨23582538638582133675838283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15721692425721422450558855 23582538638582133675838283)
              ·
                refine ⟨35373807957873200513757425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23582538638582133675838283 35373807957873200513757425)
                ·
                  refine ⟨26530355968404900385318069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35373807957873200513757425 26530355968404900385318069)
                  ·
                    refine ⟨2487220872037959411123569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26530355968404900385318069 2487220872037959411123569)
                    ·
                      refine ⟨1865415654028469558342677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487220872037959411123569 1865415654028469558342677)
                      ·
                        rfl

theorem cell23_3632884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_3632884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632884 prefixEnd_3632884 := by exact prefixLift 3632884
  have htrace : WordTrace (prefixWord ++ tailWord_3632884) baseStart_3632884 baseEnd_3632884 := by
    simpa [prefixWord, tailWord_3632884, baseEnd_3632884] using wordTrace_append hprefix tailTrace_3632884
  have hstable : (prefixWord ++ tailWord_3632884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632884).length < 2 ^ (prefixWord ++ tailWord_3632884).sum := by decide
  have hdescent : baseEnd_3632884 < baseStart_3632884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632914 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_3632914 : Nat := 118140960795 + 3632914 * 2 ^ 59
def prefixEnd_3632914 : Nat := 4983230072969 + 3 ^ 40 * 3632914 * 2
def baseEnd_3632914 : Nat := 1865431058448104440967539

theorem tailTrace_3632914 : CollatzResearch.WordTrace tailWord_3632914 prefixEnd_3632914 1865431058448104440967539 := by
  unfold tailWord_3632914
  simp only [CollatzResearch.WordTrace]
  refine ⟨33125814790145126289894449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88335506107053670106385197 33125814790145126289894449)
  ·
    refine ⟨24844361092608844717420837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33125814790145126289894449 24844361092608844717420837)
    ·
      refine ⟨4658317704864158384516407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24844361092608844717420837 4658317704864158384516407)
      ·
        refine ⟨6987476557296237576774611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4658317704864158384516407 6987476557296237576774611)
        ·
          refine ⟨10481214835944356365161917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6987476557296237576774611 10481214835944356365161917)
          ·
            refine ⟨3930455563479133636935719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10481214835944356365161917 3930455563479133636935719)
            ·
              refine ⟨5895683345218700455403579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930455563479133636935719 5895683345218700455403579)
              ·
                refine ⟨8843525017828050683105369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895683345218700455403579 8843525017828050683105369)
                ·
                  refine ⟨6632643763371038012329027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8843525017828050683105369 6632643763371038012329027)
                  ·
                    refine ⟨9948965645056557018493541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6632643763371038012329027 9948965645056557018493541)
                    ·
                      refine ⟨1865431058448104440967539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9948965645056557018493541 1865431058448104440967539)
                      ·
                        rfl

theorem cell23_3632914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_3632914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632914 prefixEnd_3632914 := by exact prefixLift 3632914
  have htrace : WordTrace (prefixWord ++ tailWord_3632914) baseStart_3632914 baseEnd_3632914 := by
    simpa [prefixWord, tailWord_3632914, baseEnd_3632914] using wordTrace_append hprefix tailTrace_3632914
  have hstable : (prefixWord ++ tailWord_3632914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632914).length < 2 ^ (prefixWord ++ tailWord_3632914).sum := by decide
  have hdescent : baseEnd_3632914 < baseStart_3632914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632917 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_3632917 : Nat := 118140960795 + 3632917 * 2 ^ 59
def prefixEnd_3632917 : Nat := 4983230072969 + 3 ^ 40 * 3632917 * 2
def baseEnd_3632917 : Nat := 1865432598890067929230025

theorem tailTrace_3632917 : CollatzResearch.WordTrace tailWord_3632917 prefixEnd_3632917 1865432598890067929230025 := by
  unfold tailWord_3632917
  simp only [CollatzResearch.WordTrace]
  refine ⟨132503368579569636671937005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88335579053046424447958003 132503368579569636671937005)
  ·
    refine ⟨49688763217338613751976377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132503368579569636671937005 49688763217338613751976377)
    ·
      refine ⟨37266572413003960313982283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49688763217338613751976377 37266572413003960313982283)
      ·
        refine ⟨55899858619505940470973425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37266572413003960313982283 55899858619505940470973425)
        ·
          refine ⟨41924893964629455353230069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55899858619505940470973425 41924893964629455353230069)
          ·
            refine ⟨3930458809184011439365319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41924893964629455353230069 3930458809184011439365319)
            ·
              refine ⟨5895688213776017159047979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930458809184011439365319 5895688213776017159047979)
              ·
                refine ⟨8843532320664025738571969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895688213776017159047979 8843532320664025738571969)
                ·
                  refine ⟨6632649240498019303928977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8843532320664025738571969 6632649240498019303928977)
                  ·
                    refine ⟨4974486930373514477946733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6632649240498019303928977 4974486930373514477946733)
                    ·
                      refine ⟨1865432598890067929230025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4974486930373514477946733 1865432598890067929230025)
                      ·
                        rfl

theorem cell23_3632917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_3632917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632917 prefixEnd_3632917 := by exact prefixLift 3632917
  have htrace : WordTrace (prefixWord ++ tailWord_3632917) baseStart_3632917 baseEnd_3632917 := by
    simpa [prefixWord, tailWord_3632917, baseEnd_3632917] using wordTrace_append hprefix tailTrace_3632917
  have hstable : (prefixWord ++ tailWord_3632917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632917).length < 2 ^ (prefixWord ++ tailWord_3632917).sum := by decide
  have hdescent : baseEnd_3632917 < baseStart_3632917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632957 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 1, 5, 2]
def baseStart_3632957 : Nat := 118140960795 + 3632957 * 2 ^ 59
def prefixEnd_3632957 : Nat := 4983230072969 + 3 ^ 40 * 3632957 * 2
def baseEnd_3632957 : Nat := 1865453138116247772729841

theorem tailTrace_3632957 : CollatzResearch.WordTrace tailWord_3632957 prefixEnd_3632957 1865453138116247772729841 := by
  unfold tailWord_3632957
  simp only [CollatzResearch.WordTrace]
  refine ⟨132504827499424723503393125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88336551666283149002262083 132504827499424723503393125)
  ·
    refine ⟨24844655156142135656886211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132504827499424723503393125 24844655156142135656886211)
    ·
      refine ⟨37266982734213203485329317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24844655156142135656886211 37266982734213203485329317)
      ·
        refine ⟨6987559262664975653499247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37266982734213203485329317 6987559262664975653499247)
        ·
          refine ⟨10481338893997463480248871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6987559262664975653499247 10481338893997463480248871)
          ·
            refine ⟨15722008340996195220373307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10481338893997463480248871 15722008340996195220373307)
            ·
              refine ⟨23583012511494292830559961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15722008340996195220373307 23583012511494292830559961)
              ·
                refine ⟨17687259383620719622919971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23583012511494292830559961 17687259383620719622919971)
                ·
                  refine ⟨26530889075431079434379957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17687259383620719622919971 26530889075431079434379957)
                  ·
                    refine ⟨2487270850821663696973121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26530889075431079434379957 2487270850821663696973121)
                    ·
                      refine ⟨1865453138116247772729841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487270850821663696973121 1865453138116247772729841)
                      ·
                        rfl

theorem cell23_3632957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_3632957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632957 prefixEnd_3632957 := by exact prefixLift 3632957
  have htrace : WordTrace (prefixWord ++ tailWord_3632957) baseStart_3632957 baseEnd_3632957 := by
    simpa [prefixWord, tailWord_3632957, baseEnd_3632957] using wordTrace_append hprefix tailTrace_3632957
  have hstable : (prefixWord ++ tailWord_3632957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632957).length < 2 ^ (prefixWord ++ tailWord_3632957).sum := by decide
  have hdescent : baseEnd_3632957 < baseStart_3632957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632970 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 2, 6, 2]
def baseStart_3632970 : Nat := 118140960795 + 3632970 * 2 ^ 59
def prefixEnd_3632970 : Nat := 4983230072969 + 3 ^ 40 * 3632970 * 2
def baseEnd_3632970 : Nat := 1865459813364756221867281

theorem tailTrace_3632970 : CollatzResearch.WordTrace tailWord_3632970 prefixEnd_3632970 1865459813364756221867281 := by
  unfold tailWord_3632970
  simp only [CollatzResearch.WordTrace]
  refine ⟨33126325412094406680904091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88336867765585084482410909 33126325412094406680904091)
  ·
    refine ⟨49689488118141610021356137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33126325412094406680904091 49689488118141610021356137)
    ·
      refine ⟨37267116088606207516017103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49689488118141610021356137 37267116088606207516017103)
      ·
        refine ⟨55900674132909311274025655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37267116088606207516017103 55900674132909311274025655)
        ·
          refine ⟨83851011199363966911038483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55900674132909311274025655 83851011199363966911038483)
          ·
            refine ⟨125776516799045950366557725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83851011199363966911038483 125776516799045950366557725)
            ·
              refine ⟨47166193799642231387459147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125776516799045950366557725 47166193799642231387459147)
              ·
                refine ⟨70749290699463347081188721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47166193799642231387459147 70749290699463347081188721)
                ·
                  refine ⟨53061968024597510310891541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70749290699463347081188721 53061968024597510310891541)
                  ·
                    refine ⟨2487279751153008295823041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53061968024597510310891541 2487279751153008295823041)
                    ·
                      refine ⟨1865459813364756221867281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487279751153008295823041 1865459813364756221867281)
                      ·
                        rfl

theorem cell23_3632970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_3632970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632970 prefixEnd_3632970 := by exact prefixLift 3632970
  have htrace : WordTrace (prefixWord ++ tailWord_3632970) baseStart_3632970 baseEnd_3632970 := by
    simpa [prefixWord, tailWord_3632970, baseEnd_3632970] using wordTrace_append hprefix tailTrace_3632970
  have hstable : (prefixWord ++ tailWord_3632970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632970).length < 2 ^ (prefixWord ++ tailWord_3632970).sum := by decide
  have hdescent : baseEnd_3632970 < baseStart_3632970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3632981 : List Nat := [1, 3, 2, 2, 2, 4, 1, 3, 1, 1, 3]
def baseStart_3632981 : Nat := 118140960795 + 3632981 * 2 ^ 59
def prefixEnd_3632981 : Nat := 4983230072969 + 3 ^ 40 * 3632981 * 2
def baseEnd_3632981 : Nat := 1865465461651955678829731

theorem tailTrace_3632981 : CollatzResearch.WordTrace tailWord_3632981 prefixEnd_3632981 1865465461651955678829731 := by
  unfold tailWord_3632981
  simp only [CollatzResearch.WordTrace]
  refine ⟨132505702851337775602266797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88337135234225183734844531 132505702851337775602266797)
  ·
    refine ⟨49689638569251665850850049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132505702851337775602266797 49689638569251665850850049)
    ·
      refine ⟨37267228926938749388137537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49689638569251665850850049 37267228926938749388137537)
      ·
        refine ⟨27950421695204062041103153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37267228926938749388137537 27950421695204062041103153)
        ·
          refine ⟨20962816271403046530827365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27950421695204062041103153 20962816271403046530827365)
          ·
            refine ⟨3930528050888071224530131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20962816271403046530827365 3930528050888071224530131)
            ·
              refine ⟨5895792076332106836795197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930528050888071224530131 5895792076332106836795197)
              ·
                refine ⟨2210922028624540063798199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5895792076332106836795197 2210922028624540063798199)
                ·
                  refine ⟨3316383042936810095697299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210922028624540063798199 3316383042936810095697299)
                  ·
                    refine ⟨4974574564405215143545949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3316383042936810095697299 4974574564405215143545949)
                    ·
                      refine ⟨1865465461651955678829731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4974574564405215143545949 1865465461651955678829731)
                      ·
                        rfl

theorem cell23_3632981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_3632981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3632981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3632981 prefixEnd_3632981 := by exact prefixLift 3632981
  have htrace : WordTrace (prefixWord ++ tailWord_3632981) baseStart_3632981 baseEnd_3632981 := by
    simpa [prefixWord, tailWord_3632981, baseEnd_3632981] using wordTrace_append hprefix tailTrace_3632981
  have hstable : (prefixWord ++ tailWord_3632981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3632981).length < 2 ^ (prefixWord ++ tailWord_3632981).sum := by decide
  have hdescent : baseEnd_3632981 < baseStart_3632981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3632981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633004 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 3, 2, 2]
def baseStart_3633004 : Nat := 118140960795 + 3633004 * 2 ^ 59
def prefixEnd_3633004 : Nat := 4983230072969 + 3 ^ 40 * 3633004 * 2
def baseEnd_3633004 : Nat := 1865477271707009088842125

theorem tailTrace_3633004 : CollatzResearch.WordTrace tailWord_3633004 prefixEnd_3633004 1865477271707009088842125 := by
  unfold tailWord_3633004
  simp only [CollatzResearch.WordTrace]
  refine ⟨66253270865127225265177033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88337694486836300353569377 66253270865127225265177033)
  ·
    refine ⟨49689953148845418948882775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66253270865127225265177033 49689953148845418948882775)
    ·
      refine ⟨74534929723268128423324163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49689953148845418948882775 74534929723268128423324163)
      ·
        refine ⟨111802394584902192634986245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74534929723268128423324163 111802394584902192634986245)
        ·
          refine ⟨20962948984669161119059921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111802394584902192634986245 20962948984669161119059921)
          ·
            refine ⟨15722211738501870839294941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20962948984669161119059921 15722211738501870839294941)
            ·
              refine ⟨5895829401938201564735603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15722211738501870839294941 5895829401938201564735603)
              ·
                refine ⟨8843744102907302347103405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5895829401938201564735603 8843744102907302347103405)
                ·
                  refine ⟨3316404038590238380163777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8843744102907302347103405 3316404038590238380163777)
                  ·
                    refine ⟨2487303028942678785122833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3316404038590238380163777 2487303028942678785122833)
                    ·
                      refine ⟨1865477271707009088842125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487303028942678785122833 1865477271707009088842125)
                      ·
                        rfl

theorem cell23_3633004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 2, 2].length) (baseStart_3633004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633004 prefixEnd_3633004 := by exact prefixLift 3633004
  have htrace : WordTrace (prefixWord ++ tailWord_3633004) baseStart_3633004 baseEnd_3633004 := by
    simpa [prefixWord, tailWord_3633004, baseEnd_3633004] using wordTrace_append hprefix tailTrace_3633004
  have hstable : (prefixWord ++ tailWord_3633004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633004).length < 2 ^ (prefixWord ++ tailWord_3633004).sum := by decide
  have hdescent : baseEnd_3633004 < baseStart_3633004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633055 : List Nat := [1, 1, 2, 5, 3, 2, 2, 2, 1, 2, 2]
def baseStart_3633055 : Nat := 118140960795 + 3633055 * 2 ^ 59
def prefixEnd_3633055 : Nat := 4983230072969 + 3 ^ 40 * 3633055 * 2
def baseEnd_3633055 : Nat := 1865503459220388389304391

theorem tailTrace_3633055 : CollatzResearch.WordTrace tailWord_3633055 prefixEnd_3633055 1865503459220388389304391 := by
  unfold tailWord_3633055
  simp only [CollatzResearch.WordTrace]
  refine ⟨132508401853069686240460619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88338934568713124160307079 132508401853069686240460619)
  ·
    refine ⟨198762602779604529360690929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132508401853069686240460619 198762602779604529360690929)
    ·
      refine ⟨149071952084703397020518197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198762602779604529360690929 149071952084703397020518197)
      ·
        refine ⟨13975495507940943470673581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149071952084703397020518197 13975495507940943470673581)
        ·
          refine ⟨5240810815477853801502593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13975495507940943470673581 5240810815477853801502593)
          ·
            refine ⟨3930608111608390351126945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5240810815477853801502593 3930608111608390351126945)
            ·
              refine ⟨2947956083706292763345209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3930608111608390351126945 2947956083706292763345209)
              ·
                refine ⟨2210967062779719572508907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2947956083706292763345209 2210967062779719572508907)
                ·
                  refine ⟨3316450594169579358763361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210967062779719572508907 3316450594169579358763361)
                  ·
                    refine ⟨2487337945627184519072521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3316450594169579358763361 2487337945627184519072521)
                    ·
                      refine ⟨1865503459220388389304391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487337945627184519072521 1865503459220388389304391)
                      ·
                        rfl

theorem cell23_3633055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_3633055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633055 prefixEnd_3633055 := by exact prefixLift 3633055
  have htrace : WordTrace (prefixWord ++ tailWord_3633055) baseStart_3633055 baseEnd_3633055 := by
    simpa [prefixWord, tailWord_3633055, baseEnd_3633055] using wordTrace_append hprefix tailTrace_3633055
  have hstable : (prefixWord ++ tailWord_3633055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633055).length < 2 ^ (prefixWord ++ tailWord_3633055).sum := by decide
  have hdescent : baseEnd_3633055 < baseStart_3633055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633060 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_3633060 : Nat := 118140960795 + 3633060 * 2 ^ 59
def prefixEnd_3633060 : Nat := 4983230072969 + 3 ^ 40 * 3633060 * 2
def baseEnd_3633060 : Nat := 1865506026623660869741867

theorem tailTrace_3633060 : CollatzResearch.WordTrace tailWord_3633060 prefixEnd_3633060 1865506026623660869741867 := by
  unfold tailWord_3633060
  simp only [CollatzResearch.WordTrace]
  refine ⟨66254292109025786047196317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88339056145367714729595089 66254292109025786047196317)
  ·
    refine ⟨24845359540884669767698619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66254292109025786047196317 24845359540884669767698619)
    ·
      refine ⟨37268039311327004651547929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24845359540884669767698619 37268039311327004651547929)
      ·
        refine ⟨27951029483495253488660947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37268039311327004651547929 27951029483495253488660947)
        ·
          refine ⟨41926544225242880232991421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27951029483495253488660947 41926544225242880232991421)
          ·
            refine ⟨15722454084466080087371783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41926544225242880232991421 15722454084466080087371783)
            ·
              refine ⟨23583681126699120131057675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15722454084466080087371783 23583681126699120131057675)
              ·
                refine ⟨35375521690048680196586513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23583681126699120131057675 35375521690048680196586513)
                ·
                  refine ⟨26531641267536510147439885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35375521690048680196586513 26531641267536510147439885)
                  ·
                    refine ⟨9949365475326191305289957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26531641267536510147439885 9949365475326191305289957)
                    ·
                      refine ⟨1865506026623660869741867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9949365475326191305289957 1865506026623660869741867)
                      ·
                        rfl

theorem cell23_3633060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_3633060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633060 prefixEnd_3633060 := by exact prefixLift 3633060
  have htrace : WordTrace (prefixWord ++ tailWord_3633060) baseStart_3633060 baseEnd_3633060 := by
    simpa [prefixWord, tailWord_3633060, baseEnd_3633060] using wordTrace_append hprefix tailTrace_3633060
  have hstable : (prefixWord ++ tailWord_3633060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633060).length < 2 ^ (prefixWord ++ tailWord_3633060).sum := by decide
  have hdescent : baseEnd_3633060 < baseStart_3633060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633080 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 2, 4, 3]
def baseStart_3633080 : Nat := 118140960795 + 3633080 * 2 ^ 59
def prefixEnd_3633080 : Nat := 4983230072969 + 3 ^ 40 * 3633080 * 2
def baseEnd_3633080 : Nat := 1865516296236750791491775

theorem tailTrace_3633080 : CollatzResearch.WordTrace tailWord_3633080 prefixEnd_3633080 1865516296236750791491775 := by
  unfold tailWord_3633080
  simp only [CollatzResearch.WordTrace]
  refine ⟨66254656838989557755060347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88339542451986077006747129 66254656838989557755060347)
  ·
    refine ⟨99381985258484336632590521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66254656838989557755060347 99381985258484336632590521)
    ·
      refine ⟨74536488943863252474442891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99381985258484336632590521 74536488943863252474442891)
      ·
        refine ⟨111804733415794878711664337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74536488943863252474442891 111804733415794878711664337)
        ·
          refine ⟨83853550061846159033748253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111804733415794878711664337 83853550061846159033748253)
          ·
            refine ⟨31445081273192309637655595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83853550061846159033748253 31445081273192309637655595)
            ·
              refine ⟨47167621909788464456483393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31445081273192309637655595 47167621909788464456483393)
              ·
                refine ⟨35375716432341348342362545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47167621909788464456483393 35375716432341348342362545)
                ·
                  refine ⟨26531787324256011256771909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35375716432341348342362545 26531787324256011256771909)
                  ·
                    refine ⟨4974710123298002110644733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26531787324256011256771909 4974710123298002110644733)
                    ·
                      refine ⟨1865516296236750791491775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4974710123298002110644733 1865516296236750791491775)
                      ·
                        rfl

theorem cell23_3633080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_3633080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633080 prefixEnd_3633080 := by exact prefixLift 3633080
  have htrace : WordTrace (prefixWord ++ tailWord_3633080) baseStart_3633080 baseEnd_3633080 := by
    simpa [prefixWord, tailWord_3633080, baseEnd_3633080] using wordTrace_append hprefix tailTrace_3633080
  have hstable : (prefixWord ++ tailWord_3633080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633080).length < 2 ^ (prefixWord ++ tailWord_3633080).sum := by decide
  have hdescent : baseEnd_3633080 < baseStart_3633080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633083 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 9]
def baseStart_3633083 : Nat := 118140960795 + 3633083 * 2 ^ 59
def prefixEnd_3633083 : Nat := 4983230072969 + 3 ^ 40 * 3633083 * 2
def baseEnd_3633083 : Nat := 207279759630968253306029

theorem tailTrace_3633083 : CollatzResearch.WordTrace tailWord_3633083 prefixEnd_3633083 207279759630968253306029 := by
  unfold tailWord_3633083
  simp only [CollatzResearch.WordTrace]
  refine ⟨132509423096968247022479903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88339615397978831348319935 132509423096968247022479903)
  ·
    refine ⟨198764134645452370533719855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132509423096968247022479903 198764134645452370533719855)
    ·
      refine ⟨298146201968178555800579783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198764134645452370533719855 298146201968178555800579783)
      ·
        refine ⟨447219302952267833700869675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298146201968178555800579783 447219302952267833700869675)
        ·
          refine ⟨670828954428401750551304513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447219302952267833700869675 670828954428401750551304513)
          ·
            refine ⟨503121715821301312913478385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670828954428401750551304513 503121715821301312913478385)
            ·
              refine ⟨377341286865975984685108789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503121715821301312913478385 377341286865975984685108789)
              ·
                refine ⟨35375745643685248564228949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 377341286865975984685108789 35375745643685248564228949)
                ·
                  refine ⟨207279759630968253306029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35375745643685248564228949 207279759630968253306029)
                  ·
                    rfl

theorem cell23_3633083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 9].length) (baseStart_3633083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633083 prefixEnd_3633083 := by exact prefixLift 3633083
  have htrace : WordTrace (prefixWord ++ tailWord_3633083) baseStart_3633083 baseEnd_3633083 := by
    simpa [prefixWord, tailWord_3633083, baseEnd_3633083] using wordTrace_append hprefix tailTrace_3633083
  have hstable : (prefixWord ++ tailWord_3633083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633083).length < 2 ^ (prefixWord ++ tailWord_3633083).sum := by decide
  have hdescent : baseEnd_3633083 < baseStart_3633083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633130 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 3, 7]
def baseStart_3633130 : Nat := 118140960795 + 3633130 * 2 ^ 59
def prefixEnd_3633130 : Nat := 4983230072969 + 3 ^ 40 * 3633130 * 2
def baseEnd_3633130 : Nat := 621847323423158531955515

theorem tailTrace_3633130 : CollatzResearch.WordTrace tailWord_3633130 prefixEnd_3633130 621847323423158531955515 := by
  unfold tailWord_3633130
  simp only [CollatzResearch.WordTrace]
  refine ⟨33127784331949493512360211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88340758218531982699627229 33127784331949493512360211)
  ·
    refine ⟨49691676497924240268540317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33127784331949493512360211 49691676497924240268540317)
    ·
      refine ⟨18634378686721590100702619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49691676497924240268540317 18634378686721590100702619)
      ·
        refine ⟨27951568030082385151053929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18634378686721590100702619 27951568030082385151053929)
        ·
          refine ⟨20963676022561788863290447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27951568030082385151053929 20963676022561788863290447)
          ·
            refine ⟨31445514033842683294935671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20963676022561788863290447 31445514033842683294935671)
            ·
              refine ⟨47168271050764024942403507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31445514033842683294935671 47168271050764024942403507)
              ·
                refine ⟨70752406576146037413605261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47168271050764024942403507 70752406576146037413605261)
                ·
                  refine ⟨26532152466054764030101973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70752406576146037413605261 26532152466054764030101973)
                  ·
                    refine ⟨621847323423158531955515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26532152466054764030101973 621847323423158531955515)
                    ·
                      rfl

theorem cell23_3633130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_3633130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633130 prefixEnd_3633130 := by exact prefixLift 3633130
  have htrace : WordTrace (prefixWord ++ tailWord_3633130) baseStart_3633130 baseEnd_3633130 := by
    simpa [prefixWord, tailWord_3633130, baseEnd_3633130] using wordTrace_append hprefix tailTrace_3633130
  have hstable : (prefixWord ++ tailWord_3633130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633130).length < 2 ^ (prefixWord ++ tailWord_3633130).sum := by decide
  have hdescent : baseEnd_3633130 < baseStart_3633130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633187 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 3]
def baseStart_3633187 : Nat := 118140960795 + 3633187 * 2 ^ 59
def prefixEnd_3633187 : Nat := 4983230072969 + 3 ^ 40 * 3633187 * 2
def baseEnd_3633187 : Nat := 1865571238666781872853783

theorem tailTrace_3633187 : CollatzResearch.WordTrace tailWord_3633187 prefixEnd_3633187 1865571238666781872853783 := by
  unfold tailWord_3633187
  simp only [CollatzResearch.WordTrace]
  refine ⟨132513216288591472784265815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88342144192394315189510543 132513216288591472784265815)
  ·
    refine ⟨198769824432887209176398723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132513216288591472784265815 198769824432887209176398723)
    ·
      refine ⟨298154736649330813764598085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198769824432887209176398723 298154736649330813764598085)
      ·
        refine ⟨55904013121749527580862141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298154736649330813764598085 55904013121749527580862141)
        ·
          refine ⟨20964004920656072842823303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55904013121749527580862141 20964004920656072842823303)
          ·
            refine ⟨31446007380984109264234955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20964004920656072842823303 31446007380984109264234955)
            ·
              refine ⟨47169011071476163896352433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31446007380984109264234955 47169011071476163896352433)
              ·
                refine ⟨35376758303607122922264325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47169011071476163896352433 35376758303607122922264325)
                ·
                  refine ⟨6633142181926335547924561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35376758303607122922264325 6633142181926335547924561)
                  ·
                    refine ⟨4974856636444751660943421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6633142181926335547924561 4974856636444751660943421)
                    ·
                      refine ⟨1865571238666781872853783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4974856636444751660943421 1865571238666781872853783)
                      ·
                        rfl

theorem cell23_3633187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_3633187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633187 prefixEnd_3633187 := by exact prefixLift 3633187
  have htrace : WordTrace (prefixWord ++ tailWord_3633187) baseStart_3633187 baseEnd_3633187 := by
    simpa [prefixWord, tailWord_3633187, baseEnd_3633187] using wordTrace_append hprefix tailTrace_3633187
  have hstable : (prefixWord ++ tailWord_3633187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633187).length < 2 ^ (prefixWord ++ tailWord_3633187).sum := by decide
  have hdescent : baseEnd_3633187 < baseStart_3633187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633210 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_3633210 : Nat := 118140960795 + 3633210 * 2 ^ 59
def prefixEnd_3633210 : Nat := 4983230072969 + 3 ^ 40 * 3633210 * 2
def baseEnd_3633210 : Nat := 1865583048721835282866177

theorem tailTrace_3633210 : CollatzResearch.WordTrace tailWord_3633210 prefixEnd_3633210 1865583048721835282866177 := by
  unfold tailWord_3633210
  simp only [CollatzResearch.WordTrace]
  refine ⟨33128513791877036928088271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88342703445005431808235389 33128513791877036928088271)
  ·
    refine ⟨49692770687815555392132407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33128513791877036928088271 49692770687815555392132407)
    ·
      refine ⟨74539156031723333088198611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49692770687815555392132407 74539156031723333088198611)
      ·
        refine ⟨111808734047584999632297917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74539156031723333088198611 111808734047584999632297917)
        ·
          refine ⟨41928275267844374862111719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111808734047584999632297917 41928275267844374862111719)
          ·
            refine ⟨62892412901766562293167579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41928275267844374862111719 62892412901766562293167579)
            ·
              refine ⟨94338619352649843439751369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62892412901766562293167579 94338619352649843439751369)
              ·
                refine ⟨70753964514487382579813527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94338619352649843439751369 70753964514487382579813527)
                ·
                  refine ⟨106130946771731073869720291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70753964514487382579813527 106130946771731073869720291)
                  ·
                    refine ⟨159196420157596610804580437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106130946771731073869720291 159196420157596610804580437)
                    ·
                      refine ⟨1865583048721835282866177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 159196420157596610804580437 1865583048721835282866177)
                      ·
                        rfl

theorem cell23_3633210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_3633210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633210 prefixEnd_3633210 := by exact prefixLift 3633210
  have htrace : WordTrace (prefixWord ++ tailWord_3633210) baseStart_3633210 baseEnd_3633210 := by
    simpa [prefixWord, tailWord_3633210, baseEnd_3633210] using wordTrace_append hprefix tailTrace_3633210
  have hstable : (prefixWord ++ tailWord_3633210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633210).length < 2 ^ (prefixWord ++ tailWord_3633210).sum := by decide
  have hdescent : baseEnd_3633210 < baseStart_3633210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633237 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 3, 5]
def baseStart_3633237 : Nat := 118140960795 + 3633237 * 2 ^ 59
def prefixEnd_3633237 : Nat := 4983230072969 + 3 ^ 40 * 3633237 * 2
def baseEnd_3633237 : Nat := 621865637566502225742851

theorem tailTrace_3633237 : CollatzResearch.WordTrace tailWord_3633237 prefixEnd_3633237 621865637566502225742851 := by
  unfold tailWord_3633237
  simp only [CollatzResearch.WordTrace]
  refine ⟨132515039938410331323585965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88343359958940220882390643 132515039938410331323585965)
  ·
    refine ⟨49693139976903874246344737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132515039938410331323585965 49693139976903874246344737)
    ·
      refine ⟨37269854982677905684758553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49693139976903874246344737 37269854982677905684758553)
      ·
        refine ⟨27952391237008429263568915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37269854982677905684758553 27952391237008429263568915)
        ·
          refine ⟨41928586855512643895353373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27952391237008429263568915 41928586855512643895353373)
          ·
            refine ⟨15723220070817241460757515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41928586855512643895353373 15723220070817241460757515)
            ·
              refine ⟨23584830106225862191136273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15723220070817241460757515 23584830106225862191136273)
              ·
                refine ⟨17688622579669396643352205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23584830106225862191136273 17688622579669396643352205)
                ·
                  refine ⟨6633233467376023741257077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17688622579669396643352205 6633233467376023741257077)
                  ·
                    refine ⟨621865637566502225742851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6633233467376023741257077 621865637566502225742851)
                    ·
                      rfl

theorem cell23_3633237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_3633237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633237 prefixEnd_3633237 := by exact prefixLift 3633237
  have htrace : WordTrace (prefixWord ++ tailWord_3633237) baseStart_3633237 baseEnd_3633237 := by
    simpa [prefixWord, tailWord_3633237, baseEnd_3633237] using wordTrace_append hprefix tailTrace_3633237
  have hstable : (prefixWord ++ tailWord_3633237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633237).length < 2 ^ (prefixWord ++ tailWord_3633237).sum := by decide
  have hdescent : baseEnd_3633237 < baseStart_3633237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633257 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 3, 1, 4]
def baseStart_3633257 : Nat := 118140960795 + 3633257 * 2 ^ 59
def prefixEnd_3633257 : Nat := 4983230072969 + 3 ^ 40 * 3633257 * 2
def baseEnd_3633257 : Nat := 1865607182312596598978461

theorem tailTrace_3633257 : CollatzResearch.WordTrace tailWord_3633257 prefixEnd_3633257 1865607182312596598978461 := by
  unfold tailWord_3633257
  simp only [CollatzResearch.WordTrace]
  refine ⟨132515769398337874739314025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88343846265558583159542683 132515769398337874739314025)
  ·
    refine ⟨99386827048753406054485519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132515769398337874739314025 99386827048753406054485519)
    ·
      refine ⟨149080240573130109081728279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99386827048753406054485519 149080240573130109081728279)
      ·
        refine ⟨223620360859695163622592419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149080240573130109081728279 223620360859695163622592419)
        ·
          refine ⟨335430541289542745433888629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223620360859695163622592419 335430541289542745433888629)
          ·
            refine ⟨31446613245894632384427059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 335430541289542745433888629 31446613245894632384427059)
            ·
              refine ⟨47169919868841948576640589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31446613245894632384427059 47169919868841948576640589)
              ·
                refine ⟨17688719950815730716240221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47169919868841948576640589 17688719950815730716240221)
                ·
                  refine ⟨6633269981555899018590083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17688719950815730716240221 6633269981555899018590083)
                  ·
                    refine ⟨9949904972333848527885125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6633269981555899018590083 9949904972333848527885125)
                    ·
                      refine ⟨1865607182312596598978461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9949904972333848527885125 1865607182312596598978461)
                      ·
                        rfl

theorem cell23_3633257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_3633257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633257 prefixEnd_3633257 := by exact prefixLift 3633257
  have htrace : WordTrace (prefixWord ++ tailWord_3633257) baseStart_3633257 baseEnd_3633257 := by
    simpa [prefixWord, tailWord_3633257, baseEnd_3633257] using wordTrace_append hprefix tailTrace_3633257
  have hstable : (prefixWord ++ tailWord_3633257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633257).length < 2 ^ (prefixWord ++ tailWord_3633257).sum := by decide
  have hdescent : baseEnd_3633257 < baseStart_3633257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633271 : List Nat := [1, 1, 3, 1, 1, 7, 2, 1, 1, 5]
def baseStart_3633271 : Nat := 118140960795 + 3633271 * 2 ^ 59
def prefixEnd_3633271 : Nat := 4983230072969 + 3 ^ 40 * 3633271 * 2
def baseEnd_3633271 : Nat := 621871457013919848067799

theorem tailTrace_3633271 : CollatzResearch.WordTrace tailWord_3633271 prefixEnd_3633271 621871457013919848067799 := by
  unfold tailWord_3633271
  simp only [CollatzResearch.WordTrace]
  refine ⟨132516280020287155130323667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88344186680191436753549111 132516280020287155130323667)
  ·
    refine ⟨198774420030430732695485501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132516280020287155130323667 198774420030430732695485501)
    ·
      refine ⟨74540407511411524760807063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198774420030430732695485501 74540407511411524760807063)
      ·
        refine ⟨111810611267117287141210595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74540407511411524760807063 111810611267117287141210595)
        ·
          refine ⟨167715916900675930711815893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111810611267117287141210595 167715916900675930711815893)
          ·
            refine ⟨3930841802359592126058185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 167715916900675930711815893 3930841802359592126058185)
            ·
              refine ⟨2948131351769694094543639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3930841802359592126058185 2948131351769694094543639)
              ·
                refine ⟨4422197027654541141815459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948131351769694094543639 4422197027654541141815459)
                ·
                  refine ⟨6633295541481811712723189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4422197027654541141815459 6633295541481811712723189)
                  ·
                    refine ⟨621871457013919848067799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6633295541481811712723189 621871457013919848067799)
                    ·
                      rfl

theorem cell23_3633271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_3633271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633271 prefixEnd_3633271 := by exact prefixLift 3633271
  have htrace : WordTrace (prefixWord ++ tailWord_3633271) baseStart_3633271 baseEnd_3633271 := by
    simpa [prefixWord, tailWord_3633271, baseEnd_3633271] using wordTrace_append hprefix tailTrace_3633271
  have hstable : (prefixWord ++ tailWord_3633271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633271).length < 2 ^ (prefixWord ++ tailWord_3633271).sum := by decide
  have hdescent : baseEnd_3633271 < baseStart_3633271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633284 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_3633284 : Nat := 118140960795 + 3633284 * 2 ^ 59
def prefixEnd_3633284 : Nat := 4983230072969 + 3 ^ 40 * 3633284 * 2
def baseEnd_3633284 : Nat := 621873682096755997780279

theorem tailTrace_3633284 : CollatzResearch.WordTrace tailWord_3633284 prefixEnd_3633284 621873682096755997780279 := by
  unfold tailWord_3633284
  simp only [CollatzResearch.WordTrace]
  refine ⟨66258377084620029175273453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88344502779493372233697937 66258377084620029175273453)
  ·
    refine ⟨24846891406732510940727545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66258377084620029175273453 24846891406732510940727545)
    ·
      refine ⟨18635168555049383205545659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24846891406732510940727545 18635168555049383205545659)
      ·
        refine ⟨27952752832574074808318489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18635168555049383205545659 27952752832574074808318489)
        ·
          refine ⟨20964564624430556106238867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27952752832574074808318489 20964564624430556106238867)
          ·
            refine ⟨31446846936645834159358301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20964564624430556106238867 31446846936645834159358301)
            ·
              refine ⟨11792567601242187809759363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31446846936645834159358301 11792567601242187809759363)
              ·
                refine ⟨17688851401863281714639045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11792567601242187809759363 17688851401863281714639045)
                ·
                  refine ⟨3316659637849365321494821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17688851401863281714639045 3316659637849365321494821)
                  ·
                    refine ⟨621873682096755997780279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3316659637849365321494821 621873682096755997780279)
                    ·
                      rfl

theorem cell23_3633284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_3633284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633284 prefixEnd_3633284 := by exact prefixLift 3633284
  have htrace : WordTrace (prefixWord ++ tailWord_3633284) baseStart_3633284 baseEnd_3633284 := by
    simpa [prefixWord, tailWord_3633284, baseEnd_3633284] using wordTrace_append hprefix tailTrace_3633284
  have hstable : (prefixWord ++ tailWord_3633284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633284).length < 2 ^ (prefixWord ++ tailWord_3633284).sum := by decide
  have hdescent : baseEnd_3633284 < baseStart_3633284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633287 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_3633287 : Nat := 118140960795 + 3633287 * 2 ^ 59
def prefixEnd_3633287 : Nat := 4983230072969 + 3 ^ 40 * 3633287 * 2
def baseEnd_3633287 : Nat := 1865622586732231481603323

theorem tailTrace_3633287 : CollatzResearch.WordTrace tailWord_3633287 prefixEnd_3633287 1865622586732231481603323 := by
  unfold tailWord_3633287
  simp only [CollatzResearch.WordTrace]
  refine ⟨132516863588229189862906115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88344575725486126575270743 132516863588229189862906115)
  ·
    refine ⟨198775295382343784794359173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132516863588229189862906115 198775295382343784794359173)
    ·
      refine ⟨37270367884189459648942345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198775295382343784794359173 37270367884189459648942345)
      ·
        refine ⟨27952775913142094736706759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37270367884189459648942345 27952775913142094736706759)
        ·
          refine ⟨41929163869713142105060139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27952775913142094736706759 41929163869713142105060139)
          ·
            refine ⟨62893745804569713157590209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41929163869713142105060139 62893745804569713157590209)
            ·
              refine ⟨47170309353427284868192657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62893745804569713157590209 47170309353427284868192657)
              ·
                refine ⟨35377732015070463651144493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47170309353427284868192657 35377732015070463651144493)
                ·
                  refine ⟨13266649505651423869179185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35377732015070463651144493 13266649505651423869179185)
                  ·
                    refine ⟨9949987129238567901884389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13266649505651423869179185 9949987129238567901884389)
                    ·
                      refine ⟨1865622586732231481603323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9949987129238567901884389 1865622586732231481603323)
                      ·
                        rfl

theorem cell23_3633287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_3633287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633287 prefixEnd_3633287 := by exact prefixLift 3633287
  have htrace : WordTrace (prefixWord ++ tailWord_3633287) baseStart_3633287 baseEnd_3633287 := by
    simpa [prefixWord, tailWord_3633287, baseEnd_3633287] using wordTrace_append hprefix tailTrace_3633287
  have hstable : (prefixWord ++ tailWord_3633287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633287).length < 2 ^ (prefixWord ++ tailWord_3633287).sum := by decide
  have hdescent : baseEnd_3633287 < baseStart_3633287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633301 : List Nat := [1, 3, 2, 1, 1, 1, 7, 1, 2, 4]
def baseStart_3633301 : Nat := 118140960795 + 3633301 * 2 ^ 59
def prefixEnd_3633301 : Nat := 4983230072969 + 3 ^ 40 * 3633301 * 2
def baseEnd_3633301 : Nat := 621876591820464808942753

theorem tailTrace_3633301 : CollatzResearch.WordTrace tailWord_3633301 prefixEnd_3633301 621876591820464808942753 := by
  unfold tailWord_3633301
  simp only [CollatzResearch.WordTrace]
  refine ⟨132517374210178470253915757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88344916140118980169277171 132517374210178470253915757)
  ·
    refine ⟨49694015328816926345218409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132517374210178470253915757 49694015328816926345218409)
    ·
      refine ⟨37270511496612694758913807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49694015328816926345218409 37270511496612694758913807)
      ·
        refine ⟨55905767244919042138370711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37270511496612694758913807 55905767244919042138370711)
        ·
          refine ⟨83858650867378563207556067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55905767244919042138370711 83858650867378563207556067)
          ·
            refine ⟨125787976301067844811334101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83858650867378563207556067 125787976301067844811334101)
            ·
              refine ⟨2948155694556277612765643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 125787976301067844811334101 2948155694556277612765643)
              ·
                refine ⟨4422233541834416419148465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948155694556277612765643 4422233541834416419148465)
                ·
                  refine ⟨3316675156375812314361349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4422233541834416419148465 3316675156375812314361349)
                  ·
                    refine ⟨621876591820464808942753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3316675156375812314361349 621876591820464808942753)
                    ·
                      rfl

theorem cell23_3633301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_3633301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633301 prefixEnd_3633301 := by exact prefixLift 3633301
  have htrace : WordTrace (prefixWord ++ tailWord_3633301) baseStart_3633301 baseEnd_3633301 := by
    simpa [prefixWord, tailWord_3633301, baseEnd_3633301] using wordTrace_append hprefix tailTrace_3633301
  have hstable : (prefixWord ++ tailWord_3633301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633301).length < 2 ^ (prefixWord ++ tailWord_3633301).sum := by decide
  have hdescent : baseEnd_3633301 < baseStart_3633301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633304 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 1, 1, 6]
def baseStart_3633304 : Nat := 118140960795 + 3633304 * 2 ^ 59
def prefixEnd_3633304 : Nat := 4983230072969 + 3 ^ 40 * 3633304 * 2
def baseEnd_3633304 : Nat := 1865631315903357915090745

theorem tailTrace_3633304 : CollatzResearch.WordTrace tailWord_3633304 prefixEnd_3633304 1865631315903357915090745 := by
  unfold tailWord_3633304
  simp only [CollatzResearch.WordTrace]
  refine ⟨66258741814583800883137483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88344989086111734510849977 66258741814583800883137483)
  ·
    refine ⟨99388112721875701324706225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66258741814583800883137483 99388112721875701324706225)
    ·
      refine ⟨74541084541406775993529669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99388112721875701324706225 74541084541406775993529669)
      ·
        refine ⟨13976453351513770498786813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74541084541406775993529669 13976453351513770498786813)
        ·
          refine ⟨5241170006817663937045055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13976453351513770498786813 5241170006817663937045055)
          ·
            refine ⟨7861755010226495905567583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5241170006817663937045055 7861755010226495905567583)
            ·
              refine ⟨11792632515339743858351375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7861755010226495905567583 11792632515339743858351375)
              ·
                refine ⟨17688948773009615787527063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11792632515339743858351375 17688948773009615787527063)
                ·
                  refine ⟨26533423159514423681290595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17688948773009615787527063 26533423159514423681290595)
                  ·
                    refine ⟨39800134739271635521935893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26533423159514423681290595 39800134739271635521935893)
                    ·
                      refine ⟨1865631315903357915090745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39800134739271635521935893 1865631315903357915090745)
                      ·
                        rfl

theorem cell23_3633304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_3633304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633304 prefixEnd_3633304 := by exact prefixLift 3633304
  have htrace : WordTrace (prefixWord ++ tailWord_3633304) baseStart_3633304 baseEnd_3633304 := by
    simpa [prefixWord, tailWord_3633304, baseEnd_3633304] using wordTrace_append hprefix tailTrace_3633304
  have hstable : (prefixWord ++ tailWord_3633304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633304).length < 2 ^ (prefixWord ++ tailWord_3633304).sum := by decide
  have hdescent : baseEnd_3633304 < baseStart_3633304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633307 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 3]
def baseStart_3633307 : Nat := 118140960795 + 3633307 * 2 ^ 59
def prefixEnd_3633307 : Nat := 4983230072969 + 3 ^ 40 * 3633307 * 2
def baseEnd_3633307 : Nat := 1865632856345321403353231

theorem tailTrace_3633307 : CollatzResearch.WordTrace tailWord_3633307 prefixEnd_3633307 1865632856345321403353231 := by
  unfold tailWord_3633307
  simp only [CollatzResearch.WordTrace]
  refine ⟨132517593048156733278634175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88345062032104488852422783 132517593048156733278634175)
  ·
    refine ⟨198776389572235099917951263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132517593048156733278634175 198776389572235099917951263)
    ·
      refine ⟨298164584358352649876926895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198776389572235099917951263 298164584358352649876926895)
      ·
        refine ⟨447246876537528974815390343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298164584358352649876926895 447246876537528974815390343)
        ·
          refine ⟨670870314806293462223085515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447246876537528974815390343 670870314806293462223085515)
          ·
            refine ⟨1006305472209440193334628273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670870314806293462223085515 1006305472209440193334628273)
            ·
              refine ⟨754729104157080145000971205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006305472209440193334628273 754729104157080145000971205)
              ·
                refine ⟨141511707029452527187682101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 754729104157080145000971205 141511707029452527187682101)
                ·
                  refine ⟨13266722534011174423845197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141511707029452527187682101 13266722534011174423845197)
                  ·
                    refine ⟨4975020950254190408941949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13266722534011174423845197 4975020950254190408941949)
                    ·
                      refine ⟨1865632856345321403353231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4975020950254190408941949 1865632856345321403353231)
                      ·
                        rfl

theorem cell23_3633307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 3].length) (baseStart_3633307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633307 prefixEnd_3633307 := by exact prefixLift 3633307
  have htrace : WordTrace (prefixWord ++ tailWord_3633307) baseStart_3633307 baseEnd_3633307 := by
    simpa [prefixWord, tailWord_3633307, baseEnd_3633307] using wordTrace_append hprefix tailTrace_3633307
  have hstable : (prefixWord ++ tailWord_3633307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633307).length < 2 ^ (prefixWord ++ tailWord_3633307).sum := by decide
  have hdescent : baseEnd_3633307 < baseStart_3633307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633311 : List Nat := [1, 1, 2, 6, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3633311 : Nat := 118140960795 + 3633311 * 2 ^ 59
def prefixEnd_3633311 : Nat := 4983230072969 + 3 ^ 40 * 3633311 * 2
def baseEnd_3633311 : Nat := 1865634910267939387703213

theorem tailTrace_3633311 : CollatzResearch.WordTrace tailWord_3633311 prefixEnd_3633311 1865634910267939387703213 := by
  unfold tailWord_3633311
  simp only [CollatzResearch.WordTrace]
  refine ⟨132517738940142241961779787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88345159293428161307853191 132517738940142241961779787)
  ·
    refine ⟨198776608410213362942669681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132517738940142241961779787 198776608410213362942669681)
    ·
      refine ⟨149082456307660022207002261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198776608410213362942669681 149082456307660022207002261)
      ·
        refine ⟨6988240139421563540953231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149082456307660022207002261 6988240139421563540953231)
        ·
          refine ⟨10482360209132345311429847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6988240139421563540953231 10482360209132345311429847)
          ·
            refine ⟨15723540313698517967144771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10482360209132345311429847 15723540313698517967144771)
            ·
              refine ⟨23585310470547776950717157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15723540313698517967144771 23585310470547776950717157)
              ·
                refine ⟨4422245713227708178259467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23585310470547776950717157 4422245713227708178259467)
                ·
                  refine ⟨6633368569841562267389201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4422245713227708178259467 6633368569841562267389201)
                  ·
                    refine ⟨4975026427381171700541901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6633368569841562267389201 4975026427381171700541901)
                    ·
                      refine ⟨1865634910267939387703213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4975026427381171700541901 1865634910267939387703213)
                      ·
                        rfl

theorem cell23_3633311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3633311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633311 prefixEnd_3633311 := by exact prefixLift 3633311
  have htrace : WordTrace (prefixWord ++ tailWord_3633311) baseStart_3633311 baseEnd_3633311 := by
    simpa [prefixWord, tailWord_3633311, baseEnd_3633311] using wordTrace_append hprefix tailTrace_3633311
  have hstable : (prefixWord ++ tailWord_3633311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633311).length < 2 ^ (prefixWord ++ tailWord_3633311).sum := by decide
  have hdescent : baseEnd_3633311 < baseStart_3633311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633314 : List Nat := [3, 3, 1, 3, 1, 2, 1, 9]
def baseStart_3633314 : Nat := 118140960795 + 3633314 * 2 ^ 59
def prefixEnd_3633314 : Nat := 4983230072969 + 3 ^ 40 * 3633314 * 2
def baseEnd_3633314 : Nat := 69097646322588995406137

theorem tailTrace_3633314 : CollatzResearch.WordTrace tailWord_3633314 prefixEnd_3633314 69097646322588995406137 := by
  unfold tailWord_3633314
  simp only [CollatzResearch.WordTrace]
  refine ⟨33129462089782843368534749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88345232239420915649425997 33129462089782843368534749)
  ·
    refine ⟨12423548283668566263200531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33129462089782843368534749 12423548283668566263200531)
    ·
      refine ⟨18635322425502849394800797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12423548283668566263200531 18635322425502849394800797)
      ·
        refine ⟨6988245909563568523050299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18635322425502849394800797 6988245909563568523050299)
        ·
          refine ⟨10482368864345352784575449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6988245909563568523050299 10482368864345352784575449)
          ·
            refine ⟨7861776648259014588431587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10482368864345352784575449 7861776648259014588431587)
            ·
              refine ⟨11792664972388521882647381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7861776648259014588431587 11792664972388521882647381)
              ·
                refine ⟨69097646322588995406137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11792664972388521882647381 69097646322588995406137)
                ·
                  rfl

theorem cell23_3633314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 9].length) (baseStart_3633314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633314 prefixEnd_3633314 := by exact prefixLift 3633314
  have htrace : WordTrace (prefixWord ++ tailWord_3633314) baseStart_3633314 baseEnd_3633314 := by
    simpa [prefixWord, tailWord_3633314, baseEnd_3633314] using wordTrace_append hprefix tailTrace_3633314
  have hstable : (prefixWord ++ tailWord_3633314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633314).length < 2 ^ (prefixWord ++ tailWord_3633314).sum := by decide
  have hdescent : baseEnd_3633314 < baseStart_3633314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633337 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3633337 : Nat := 118140960795 + 3633337 * 2 ^ 59
def prefixEnd_3633337 : Nat := 4983230072969 + 3 ^ 40 * 3633337 * 2
def baseEnd_3633337 : Nat := 1865648260764956285978093

theorem tailTrace_3633337 : CollatzResearch.WordTrace tailWord_3633337 prefixEnd_3633337 1865648260764956285978093 := by
  unfold tailWord_3633337
  simp only [CollatzResearch.WordTrace]
  refine ⟨132518687238048048402226265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88345791492032032268150843 132518687238048048402226265)
  ·
    refine ⟨99389015428536036301669699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132518687238048048402226265 99389015428536036301669699)
    ·
      refine ⟨149083523142804054452504549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99389015428536036301669699 149083523142804054452504549)
      ·
        refine ⟨27953160589275760209844603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149083523142804054452504549 27953160589275760209844603)
        ·
          refine ⟨41929740883913640314766905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27953160589275760209844603 41929740883913640314766905)
          ·
            refine ⟨31447305662935230236075179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41929740883913640314766905 31447305662935230236075179)
            ·
              refine ⟨47170958494402845354112769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31447305662935230236075179 47170958494402845354112769)
              ·
                refine ⟨35378218870802134015584577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47170958494402845354112769 35378218870802134015584577)
                ·
                  refine ⟨26533664153101600511688433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35378218870802134015584577 26533664153101600511688433)
                  ·
                    refine ⟨19900248114826200383766325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26533664153101600511688433 19900248114826200383766325)
                    ·
                      refine ⟨1865648260764956285978093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19900248114826200383766325 1865648260764956285978093)
                      ·
                        rfl

theorem cell23_3633337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3633337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633337 prefixEnd_3633337 := by exact prefixLift 3633337
  have htrace : WordTrace (prefixWord ++ tailWord_3633337) baseStart_3633337 baseEnd_3633337 := by
    simpa [prefixWord, tailWord_3633337, baseEnd_3633337] using wordTrace_append hprefix tailTrace_3633337
  have hstable : (prefixWord ++ tailWord_3633337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633337).length < 2 ^ (prefixWord ++ tailWord_3633337).sum := by decide
  have hdescent : baseEnd_3633337 < baseStart_3633337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633341 : List Nat := [1, 4, 1, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_3633341 : Nat := 118140960795 + 3633341 * 2 ^ 59
def prefixEnd_3633341 : Nat := 4983230072969 + 3 ^ 40 * 3633341 * 2
def baseEnd_3633341 : Nat := 1865650314687574270328075

theorem tailTrace_3633341 : CollatzResearch.WordTrace tailWord_3633341 prefixEnd_3633341 1865650314687574270328075 := by
  unfold tailWord_3633341
  simp only [CollatzResearch.WordTrace]
  refine ⟨132518833130033557085371877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88345888753355704723581251 132518833130033557085371877)
  ·
    refine ⟨24847281211881291953507227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132518833130033557085371877 24847281211881291953507227)
    ·
      refine ⟨37270921817821937930260841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24847281211881291953507227 37270921817821937930260841)
      ·
        refine ⟨27953191363366453447695631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37270921817821937930260841 27953191363366453447695631)
        ·
          refine ⟨41929787045049680171543447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27953191363366453447695631 41929787045049680171543447)
          ·
            refine ⟨62894680567574520257315171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41929787045049680171543447 62894680567574520257315171)
            ·
              refine ⟨94342020851361780385972757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62894680567574520257315171 94342020851361780385972757)
              ·
                refine ⟨4422282227407583455592473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94342020851361780385972757 4422282227407583455592473)
                ·
                  refine ⟨3316711670555687591694355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4422282227407583455592473 3316711670555687591694355)
                  ·
                    refine ⟨4975067505833531387541533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3316711670555687591694355 4975067505833531387541533)
                    ·
                      refine ⟨1865650314687574270328075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4975067505833531387541533 1865650314687574270328075)
                      ·
                        rfl

theorem cell23_3633341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_3633341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633341 prefixEnd_3633341 := by exact prefixLift 3633341
  have htrace : WordTrace (prefixWord ++ tailWord_3633341) baseStart_3633341 baseEnd_3633341 := by
    simpa [prefixWord, tailWord_3633341, baseEnd_3633341] using wordTrace_append hprefix tailTrace_3633341
  have hstable : (prefixWord ++ tailWord_3633341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633341).length < 2 ^ (prefixWord ++ tailWord_3633341).sum := by decide
  have hdescent : baseEnd_3633341 < baseStart_3633341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633342 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_3633342 : Nat := 118140960795 + 3633342 * 2 ^ 59
def prefixEnd_3633342 : Nat := 4983230072969 + 3 ^ 40 * 3633342 * 2
def baseEnd_3633342 : Nat := 1865650828168228766415571

theorem tailTrace_3633342 : CollatzResearch.WordTrace tailWord_3633342 prefixEnd_3633342 1865650828168228766415571 := by
  unfold tailWord_3633342
  simp only [CollatzResearch.WordTrace]
  refine ⟨16564858700378741782019785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88345913068686622837438853 16564858700378741782019785)
  ·
    refine ⟨12423644025284056336514839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16564858700378741782019785 12423644025284056336514839)
    ·
      refine ⟨18635466037926084504772259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12423644025284056336514839 18635466037926084504772259)
      ·
        refine ⟨27953199056889126757158389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18635466037926084504772259 27953199056889126757158389)
        ·
          refine ⟨2620612411583355633483599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27953199056889126757158389 2620612411583355633483599)
          ·
            refine ⟨3930918617375033450225399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620612411583355633483599 3930918617375033450225399)
            ·
              refine ⟨5896377926062550175338099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930918617375033450225399 5896377926062550175338099)
              ·
                refine ⟨8844566889093825263007149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5896377926062550175338099 8844566889093825263007149)
                ·
                  refine ⟨3316712583410184473627681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8844566889093825263007149 3316712583410184473627681)
                  ·
                    refine ⟨2487534437557638355220761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3316712583410184473627681 2487534437557638355220761)
                    ·
                      refine ⟨1865650828168228766415571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487534437557638355220761 1865650828168228766415571)
                      ·
                        rfl

theorem cell23_3633342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_3633342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633342 prefixEnd_3633342 := by exact prefixLift 3633342
  have htrace : WordTrace (prefixWord ++ tailWord_3633342) baseStart_3633342 baseEnd_3633342 := by
    simpa [prefixWord, tailWord_3633342, baseEnd_3633342] using wordTrace_append hprefix tailTrace_3633342
  have hstable : (prefixWord ++ tailWord_3633342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633342).length < 2 ^ (prefixWord ++ tailWord_3633342).sum := by decide
  have hdescent : baseEnd_3633342 < baseStart_3633342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633358 : List Nat := [4, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_3633358 : Nat := 118140960795 + 3633358 * 2 ^ 59
def prefixEnd_3633358 : Nat := 4983230072969 + 3 ^ 40 * 3633358 * 2
def baseEnd_3633358 : Nat := 1865659043858700703815497

theorem tailTrace_3633358 : CollatzResearch.WordTrace tailWord_3633358 prefixEnd_3633358 1865659043858700703815497 := by
  unfold tailWord_3633358
  simp only [CollatzResearch.WordTrace]
  refine ⟨16564931646371496123592591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88346302113981312659160485 16564931646371496123592591)
  ·
    refine ⟨24847397469557244185388887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16564931646371496123592591 24847397469557244185388887)
    ·
      refine ⟨37271096204335866278083331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24847397469557244185388887 37271096204335866278083331)
      ·
        refine ⟨55906644306503799417124997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37271096204335866278083331 55906644306503799417124997)
        ·
          refine ⟨10482495807469462390710937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55906644306503799417124997 10482495807469462390710937)
          ·
            refine ⟨7861871855602096793033203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10482495807469462390710937 7861871855602096793033203)
            ·
              refine ⟨11792807783403145189549805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7861871855602096793033203 11792807783403145189549805)
              ·
                refine ⟨4422302918776179446081177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11792807783403145189549805 4422302918776179446081177)
                ·
                  refine ⟨3316727189082134584560883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4422302918776179446081177 3316727189082134584560883)
                  ·
                    refine ⟨4975090783623201876841325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3316727189082134584560883 4975090783623201876841325)
                    ·
                      refine ⟨1865659043858700703815497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4975090783623201876841325 1865659043858700703815497)
                      ·
                        rfl

theorem cell23_3633358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_3633358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633358 prefixEnd_3633358 := by exact prefixLift 3633358
  have htrace : WordTrace (prefixWord ++ tailWord_3633358) baseStart_3633358 baseEnd_3633358 := by
    simpa [prefixWord, tailWord_3633358, baseEnd_3633358] using wordTrace_append hprefix tailTrace_3633358
  have hstable : (prefixWord ++ tailWord_3633358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633358).length < 2 ^ (prefixWord ++ tailWord_3633358).sum := by decide
  have hdescent : baseEnd_3633358 < baseStart_3633358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633368 : List Nat := [2, 1, 2, 2, 4, 1, 3, 2, 1, 3, 2]
def baseStart_3633368 : Nat := 118140960795 + 3633368 * 2 ^ 59
def prefixEnd_3633368 : Nat := 4983230072969 + 3 ^ 40 * 3633368 * 2
def baseEnd_3633368 : Nat := 1865664178665245664690451

theorem tailTrace_3633368 : CollatzResearch.WordTrace tailWord_3633368 prefixEnd_3633368 1865664178665245664690451 := by
  unfold tailWord_3633368
  simp only [CollatzResearch.WordTrace]
  refine ⟨66259908950467870348302379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88346545267290493797736505 66259908950467870348302379)
  ·
    refine ⟨99389863425701805522453569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66259908950467870348302379 99389863425701805522453569)
    ·
      refine ⟨74542397569276354141840177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99389863425701805522453569 74542397569276354141840177)
      ·
        refine ⟨55906798176957265606380133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74542397569276354141840177 55906798176957265606380133)
        ·
          refine ⟨10482524658179487301196275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55906798176957265606380133 10482524658179487301196275)
          ·
            refine ⟨15723786987269230951794413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10482524658179487301196275 15723786987269230951794413)
            ·
              refine ⟨5896420120225961606922905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15723786987269230951794413 5896420120225961606922905)
              ·
                refine ⟨4422315090169471205192179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5896420120225961606922905 4422315090169471205192179)
                ·
                  refine ⟨6633472635254206807788269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4422315090169471205192179 6633472635254206807788269)
                  ·
                    refine ⟨2487552238220327552920601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6633472635254206807788269 2487552238220327552920601)
                    ·
                      refine ⟨1865664178665245664690451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487552238220327552920601 1865664178665245664690451)
                      ·
                        rfl

theorem cell23_3633368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_3633368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633368 prefixEnd_3633368 := by exact prefixLift 3633368
  have htrace : WordTrace (prefixWord ++ tailWord_3633368) baseStart_3633368 baseEnd_3633368 := by
    simpa [prefixWord, tailWord_3633368, baseEnd_3633368] using wordTrace_append hprefix tailTrace_3633368
  have hstable : (prefixWord ++ tailWord_3633368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633368).length < 2 ^ (prefixWord ++ tailWord_3633368).sum := by decide
  have hdescent : baseEnd_3633368 < baseStart_3633368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633381 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 3, 4, 2]
def baseStart_3633381 : Nat := 118140960795 + 3633381 * 2 ^ 59
def prefixEnd_3633381 : Nat := 4983230072969 + 3 ^ 40 * 3633381 * 2
def baseEnd_3633381 : Nat := 1865670853913754113827891

theorem tailTrace_3633381 : CollatzResearch.WordTrace tailWord_3633381 prefixEnd_3633381 1865670853913754113827891 := by
  unfold tailWord_3633381
  simp only [CollatzResearch.WordTrace]
  refine ⟨132520292049888643916827997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88346861366592429277885331 132520292049888643916827997)
  ·
    refine ⟨49695109518708241468810499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132520292049888643916827997 49695109518708241468810499)
    ·
      refine ⟨74542664278062362203215749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49695109518708241468810499 74542664278062362203215749)
      ·
        refine ⟨13976749552136692913102953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74542664278062362203215749 13976749552136692913102953)
        ·
          refine ⟨10482562164102519684827215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13976749552136692913102953 10482562164102519684827215)
          ·
            refine ⟨15723843246153779527240823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10482562164102519684827215 15723843246153779527240823)
            ·
              refine ⟨23585764869230669290861235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15723843246153779527240823 23585764869230669290861235)
              ·
                refine ⟨35378647303846003936291853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23585764869230669290861235 35378647303846003936291853)
                ·
                  refine ⟨13266992738942251476109445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35378647303846003936291853 13266992738942251476109445)
                  ·
                    refine ⟨2487561138551672151770521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13266992738942251476109445 2487561138551672151770521)
                    ·
                      refine ⟨1865670853913754113827891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487561138551672151770521 1865670853913754113827891)
                      ·
                        rfl

theorem cell23_3633381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_3633381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633381 prefixEnd_3633381 := by exact prefixLift 3633381
  have htrace : WordTrace (prefixWord ++ tailWord_3633381) baseStart_3633381 baseEnd_3633381 := by
    simpa [prefixWord, tailWord_3633381, baseEnd_3633381] using wordTrace_append hprefix tailTrace_3633381
  have hstable : (prefixWord ++ tailWord_3633381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633381).length < 2 ^ (prefixWord ++ tailWord_3633381).sum := by decide
  have hdescent : baseEnd_3633381 < baseStart_3633381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633384 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3633384 : Nat := 118140960795 + 3633384 * 2 ^ 59
def prefixEnd_3633384 : Nat := 4983230072969 + 3 ^ 40 * 3633384 * 2
def baseEnd_3633384 : Nat := 1865672394355717602090377

theorem tailTrace_3633384 : CollatzResearch.WordTrace tailWord_3633384 prefixEnd_3633384 1865672394355717602090377 := by
  unfold tailWord_3633384
  simp only [CollatzResearch.WordTrace]
  refine ⟨66260200734438887714593603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88346934312585183619458137 66260200734438887714593603)
  ·
    refine ⟨99390301101658331571890405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66260200734438887714593603 99390301101658331571890405)
    ·
      refine ⟨18635681456560937169729451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99390301101658331571890405 18635681456560937169729451)
      ·
        refine ⟨27953522184841405754594177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18635681456560937169729451 27953522184841405754594177)
        ·
          refine ⟨20965141638631054315945633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27953522184841405754594177 20965141638631054315945633)
          ·
            refine ⟨15723856228973290736959225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20965141638631054315945633 15723856228973290736959225)
            ·
              refine ⟨11792892171729968052719419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15723856228973290736959225 11792892171729968052719419)
              ·
                refine ⟨17689338257594952079079129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11792892171729968052719419 17689338257594952079079129)
                ·
                  refine ⟨13267003693196214059309347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17689338257594952079079129 13267003693196214059309347)
                  ·
                    refine ⟨19900505539794321088964021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13267003693196214059309347 19900505539794321088964021)
                    ·
                      refine ⟨1865672394355717602090377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19900505539794321088964021 1865672394355717602090377)
                      ·
                        rfl

theorem cell23_3633384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3633384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633384 prefixEnd_3633384 := by exact prefixLift 3633384
  have htrace : WordTrace (prefixWord ++ tailWord_3633384) baseStart_3633384 baseEnd_3633384 := by
    simpa [prefixWord, tailWord_3633384, baseEnd_3633384] using wordTrace_append hprefix tailTrace_3633384
  have hstable : (prefixWord ++ tailWord_3633384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633384).length < 2 ^ (prefixWord ++ tailWord_3633384).sum := by decide
  have hdescent : baseEnd_3633384 < baseStart_3633384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633398 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_3633398 : Nat := 118140960795 + 3633398 * 2 ^ 59
def prefixEnd_3633398 : Nat := 4983230072969 + 3 ^ 40 * 3633398 * 2
def baseEnd_3633398 : Nat := 1865679583084880547315313

theorem tailTrace_3633398 : CollatzResearch.WordTrace tailWord_3633398 prefixEnd_3633398 1865679583084880547315313 := by
  unfold tailWord_3633398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8282557005676690988762303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88347274727218037213464565 8282557005676690988762303)
  ·
    refine ⟨12423835508515036483143455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8282557005676690988762303 12423835508515036483143455)
    ·
      refine ⟨18635753262772554724715183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12423835508515036483143455 18635753262772554724715183)
      ·
        refine ⟨27953629894158832087072775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18635753262772554724715183 27953629894158832087072775)
        ·
          refine ⟨41930444841238248130609163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27953629894158832087072775 41930444841238248130609163)
          ·
            refine ⟨62895667261857372195913745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41930444841238248130609163 62895667261857372195913745)
            ·
              refine ⟨47171750446393029146935309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62895667261857372195913745 47171750446393029146935309)
              ·
                refine ⟨17689406417397385930100741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47171750446393029146935309 17689406417397385930100741)
                ·
                  refine ⟨3316763703262009861893889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17689406417397385930100741 3316763703262009861893889)
                  ·
                    refine ⟨2487572777446507396420417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3316763703262009861893889 2487572777446507396420417)
                    ·
                      refine ⟨1865679583084880547315313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487572777446507396420417 1865679583084880547315313)
                      ·
                        rfl

theorem cell23_3633398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_3633398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633398 prefixEnd_3633398 := by exact prefixLift 3633398
  have htrace : WordTrace (prefixWord ++ tailWord_3633398) baseStart_3633398 baseEnd_3633398 := by
    simpa [prefixWord, tailWord_3633398, baseEnd_3633398] using wordTrace_append hprefix tailTrace_3633398
  have hstable : (prefixWord ++ tailWord_3633398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633398).length < 2 ^ (prefixWord ++ tailWord_3633398).sum := by decide
  have hdescent : baseEnd_3633398 < baseStart_3633398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633415 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3633415 : Nat := 118140960795 + 3633415 * 2 ^ 59
def prefixEnd_3633415 : Nat := 4983230072969 + 3 ^ 40 * 3633415 * 2
def baseEnd_3633415 : Nat := 1865688312256006980802735

theorem tailTrace_3633415 : CollatzResearch.WordTrace tailWord_3633415 prefixEnd_3633415 1865688312256006980802735 := by
  unfold tailWord_3633415
  simp only [CollatzResearch.WordTrace]
  refine ⟨132521532131765467723565699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88347688087843645149043799 132521532131765467723565699)
  ·
    refine ⟨198782298197648201585348549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132521532131765467723565699 198782298197648201585348549)
    ·
      refine ⟨37271680912059037797252853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198782298197648201585348549 37271680912059037797252853)
      ·
        refine ⟨3494220085505534793492455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37271680912059037797252853 3494220085505534793492455)
        ·
          refine ⟨5241330128258302190238683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3494220085505534793492455 5241330128258302190238683)
          ·
            refine ⟨7861995192387453285358025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5241330128258302190238683 7861995192387453285358025)
            ·
              refine ⟨5896496394290589964018519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7861995192387453285358025 5896496394290589964018519)
              ·
                refine ⟨8844744591435884946027779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5896496394290589964018519 8844744591435884946027779)
                ·
                  refine ⟨13267116887153827419041669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8844744591435884946027779 13267116887153827419041669)
                  ·
                    refine ⟨2487584416341342641070313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13267116887153827419041669 2487584416341342641070313)
                    ·
                      refine ⟨1865688312256006980802735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487584416341342641070313 1865688312256006980802735)
                      ·
                        rfl

theorem cell23_3633415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3633415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633415 prefixEnd_3633415 := by exact prefixLift 3633415
  have htrace : WordTrace (prefixWord ++ tailWord_3633415) baseStart_3633415 baseEnd_3633415 := by
    simpa [prefixWord, tailWord_3633415, baseEnd_3633415] using wordTrace_append hprefix tailTrace_3633415
  have hstable : (prefixWord ++ tailWord_3633415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633415).length < 2 ^ (prefixWord ++ tailWord_3633415).sum := by decide
  have hdescent : baseEnd_3633415 < baseStart_3633415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633427 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 7]
def baseStart_3633427 : Nat := 118140960795 + 3633427 * 2 ^ 59
def prefixEnd_3633427 : Nat := 4983230072969 + 3 ^ 40 * 3633427 * 2
def baseEnd_3633427 : Nat := 1865694474023860933852679

theorem tailTrace_3633427 : CollatzResearch.WordTrace tailWord_3633427 prefixEnd_3633427 1865694474023860933852679 := by
  unfold tailWord_3633427
  simp only [CollatzResearch.WordTrace]
  refine ⟨132521969807721993773002535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88347979871814662515335023 132521969807721993773002535)
  ·
    refine ⟨198782954711582990659503803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132521969807721993773002535 198782954711582990659503803)
    ·
      refine ⟨298174432067374485989255705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198782954711582990659503803 298174432067374485989255705)
      ·
        refine ⟨223630824050530864491941779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298174432067374485989255705 223630824050530864491941779)
        ·
          refine ⟨335446236075796296737912669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223630824050530864491941779 335446236075796296737912669)
          ·
            refine ⟨125792338528423611276717251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335446236075796296737912669 125792338528423611276717251)
            ·
              refine ⟨188688507792635416915075877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125792338528423611276717251 188688507792635416915075877)
              ·
                refine ⟨35379095211119140671576727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188688507792635416915075877 35379095211119140671576727)
                ·
                  refine ⟨53068642816678711007365091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35379095211119140671576727 53068642816678711007365091)
                  ·
                    refine ⟨79602964225018066511047637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53068642816678711007365091 79602964225018066511047637)
                    ·
                      refine ⟨1865694474023860933852679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79602964225018066511047637 1865694474023860933852679)
                      ·
                        rfl

theorem cell23_3633427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_3633427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633427 prefixEnd_3633427 := by exact prefixLift 3633427
  have htrace : WordTrace (prefixWord ++ tailWord_3633427) baseStart_3633427 baseEnd_3633427 := by
    simpa [prefixWord, tailWord_3633427, baseEnd_3633427] using wordTrace_append hprefix tailTrace_3633427
  have hstable : (prefixWord ++ tailWord_3633427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633427).length < 2 ^ (prefixWord ++ tailWord_3633427).sum := by decide
  have hdescent : baseEnd_3633427 < baseStart_3633427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633467 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 10]
def baseStart_3633467 : Nat := 118140960795 + 3633467 * 2 ^ 59
def prefixEnd_3633467 : Nat := 4983230072969 + 3 ^ 40 * 3633467 * 2
def baseEnd_3633467 : Nat := 1865715013250040777352495

theorem tailTrace_3633467 : CollatzResearch.WordTrace tailWord_3633467 prefixEnd_3633467 1865715013250040777352495 := by
  unfold tailWord_3633467
  simp only [CollatzResearch.WordTrace]
  refine ⟨132523428727577080604458655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88348952485051387069639103 132523428727577080604458655)
  ·
    refine ⟨198785143091365620906687983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132523428727577080604458655 198785143091365620906687983)
    ·
      refine ⟨298177714637048431360031975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198785143091365620906687983 298177714637048431360031975)
      ·
        refine ⟨447266571955572647040047963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298177714637048431360031975 447266571955572647040047963)
        ·
          refine ⟨670899857933358970560071945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447266571955572647040047963 670899857933358970560071945)
          ·
            refine ⟨503174893450019227920053959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670899857933358970560071945 503174893450019227920053959)
            ·
              refine ⟨754762340175028841880080939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503174893450019227920053959 754762340175028841880080939)
              ·
                refine ⟨1132143510262543262820121409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754762340175028841880080939 1132143510262543262820121409)
                ·
                  refine ⟨849107632696907447115091057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1132143510262543262820121409 849107632696907447115091057)
                  ·
                    refine ⟨636830724522680585336318293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 849107632696907447115091057 636830724522680585336318293)
                    ·
                      refine ⟨1865715013250040777352495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 636830724522680585336318293 1865715013250040777352495)
                      ·
                        rfl

theorem cell23_3633467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_3633467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633467 prefixEnd_3633467 := by exact prefixLift 3633467
  have htrace : WordTrace (prefixWord ++ tailWord_3633467) baseStart_3633467 baseEnd_3633467 := by
    simpa [prefixWord, tailWord_3633467, baseEnd_3633467] using wordTrace_append hprefix tailTrace_3633467
  have hstable : (prefixWord ++ tailWord_3633467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633467).length < 2 ^ (prefixWord ++ tailWord_3633467).sum := by decide
  have hdescent : baseEnd_3633467 < baseStart_3633467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633471 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 2, 4, 2]
def baseStart_3633471 : Nat := 118140960795 + 3633471 * 2 ^ 59
def prefixEnd_3633471 : Nat := 4983230072969 + 3 ^ 40 * 3633471 * 2
def baseEnd_3633471 : Nat := 1865717067172658761702477

theorem tailTrace_3633471 : CollatzResearch.WordTrace tailWord_3633471 prefixEnd_3633471 1865717067172658761702477 := by
  unfold tailWord_3633471
  simp only [CollatzResearch.WordTrace]
  refine ⟨132523574619562589287604267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88349049746375059525069511 132523574619562589287604267)
  ·
    refine ⟨198785361929343883931406401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132523574619562589287604267 198785361929343883931406401)
    ·
      refine ⟨149089021447007912948554801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198785361929343883931406401 149089021447007912948554801)
      ·
        refine ⟨111816766085255934711416101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149089021447007912948554801 111816766085255934711416101)
        ·
          refine ⟨20965643640985487758390519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111816766085255934711416101 20965643640985487758390519)
          ·
            refine ⟨31448465461478231637585779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20965643640985487758390519 31448465461478231637585779)
            ·
              refine ⟨47172698192217347456378669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31448465461478231637585779 47172698192217347456378669)
              ·
                refine ⟨17689761822081505296142001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47172698192217347456378669 17689761822081505296142001)
                ·
                  refine ⟨13267321366561128972106501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17689761822081505296142001 13267321366561128972106501)
                  ·
                    refine ⟨2487622756230211682269969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13267321366561128972106501 2487622756230211682269969)
                    ·
                      refine ⟨1865717067172658761702477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487622756230211682269969 1865717067172658761702477)
                      ·
                        rfl

theorem cell23_3633471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 4, 2].length) (baseStart_3633471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633471 prefixEnd_3633471 := by exact prefixLift 3633471
  have htrace : WordTrace (prefixWord ++ tailWord_3633471) baseStart_3633471 baseEnd_3633471 := by
    simpa [prefixWord, tailWord_3633471, baseEnd_3633471] using wordTrace_append hprefix tailTrace_3633471
  have hstable : (prefixWord ++ tailWord_3633471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633471).length < 2 ^ (prefixWord ++ tailWord_3633471).sum := by decide
  have hdescent : baseEnd_3633471 < baseStart_3633471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633484 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_3633484 : Nat := 118140960795 + 3633484 * 2 ^ 59
def prefixEnd_3633484 : Nat := 4983230072969 + 3 ^ 40 * 3633484 * 2
def baseEnd_3633484 : Nat := 1865723742421167210839917

theorem tailTrace_3633484 : CollatzResearch.WordTrace tailWord_3633484 prefixEnd_3633484 1865723742421167210839917 := by
  unfold tailWord_3633484
  simp only [CollatzResearch.WordTrace]
  refine ⟨66262024384257746253913753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88349365845676995005218337 66262024384257746253913753)
  ·
    refine ⟨49696518288193309690435315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66262024384257746253913753 49696518288193309690435315)
    ·
      refine ⟨74544777432289964535652973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49696518288193309690435315 74544777432289964535652973)
      ·
        refine ⟨27954291537108736700869865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74544777432289964535652973 27954291537108736700869865)
        ·
          refine ⟨20965718652831552525652399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27954291537108736700869865 20965718652831552525652399)
          ·
            refine ⟨31448577979247328788478599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20965718652831552525652399 31448577979247328788478599)
            ·
              refine ⟨47172866968870993182717899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31448577979247328788478599 47172866968870993182717899)
              ·
                refine ⟨70759300453306489774076849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47172866968870993182717899 70759300453306489774076849)
                ·
                  refine ⟨53069475339979867330557637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70759300453306489774076849 53069475339979867330557637)
                  ·
                    refine ⟨9950526626246225124479557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53069475339979867330557637 9950526626246225124479557)
                    ·
                      refine ⟨1865723742421167210839917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9950526626246225124479557 1865723742421167210839917)
                      ·
                        rfl

theorem cell23_3633484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_3633484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633484 prefixEnd_3633484 := by exact prefixLift 3633484
  have htrace : WordTrace (prefixWord ++ tailWord_3633484) baseStart_3633484 baseEnd_3633484 := by
    simpa [prefixWord, tailWord_3633484, baseEnd_3633484] using wordTrace_append hprefix tailTrace_3633484
  have hstable : (prefixWord ++ tailWord_3633484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633484).length < 2 ^ (prefixWord ++ tailWord_3633484).sum := by decide
  have hdescent : baseEnd_3633484 < baseStart_3633484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633548 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 2, 3, 2]
def baseStart_3633548 : Nat := 118140960795 + 3633548 * 2 ^ 59
def prefixEnd_3633548 : Nat := 4983230072969 + 3 ^ 40 * 3633548 * 2
def baseEnd_3633548 : Nat := 1865756605183054960439623

theorem tailTrace_3633548 : CollatzResearch.WordTrace tailWord_3633548 prefixEnd_3633548 1865756605183054960439623 := by
  unfold tailWord_3633548
  simp only [CollatzResearch.WordTrace]
  refine ⟨66263191520141815719078649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88350922026855754292104865 66263191520141815719078649)
  ·
    refine ⟨49697393640106361789308987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66263191520141815719078649 49697393640106361789308987)
    ·
      refine ⟨74546090460159542683963481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49697393640106361789308987 74546090460159542683963481)
      ·
        refine ⟨55909567845119657012972611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74546090460159542683963481 55909567845119657012972611)
        ·
          refine ⟨83864351767679485519458917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55909567845119657012972611 83864351767679485519458917)
          ·
            refine ⟨15724565956439903534898547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83864351767679485519458917 15724565956439903534898547)
            ·
              refine ⟨23586848934659855302347821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15724565956439903534898547 23586848934659855302347821)
              ·
                refine ⟨8845068350497445738380433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23586848934659855302347821 8845068350497445738380433)
                ·
                  refine ⟨6633801262873084303785325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8845068350497445738380433 6633801262873084303785325)
                  ·
                    refine ⟨2487675473577406613919497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6633801262873084303785325 2487675473577406613919497)
                    ·
                      refine ⟨1865756605183054960439623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487675473577406613919497 1865756605183054960439623)
                      ·
                        rfl

theorem cell23_3633548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_3633548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633548 prefixEnd_3633548 := by exact prefixLift 3633548
  have htrace : WordTrace (prefixWord ++ tailWord_3633548) baseStart_3633548 baseEnd_3633548 := by
    simpa [prefixWord, tailWord_3633548, baseEnd_3633548] using wordTrace_append hprefix tailTrace_3633548
  have hstable : (prefixWord ++ tailWord_3633548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633548).length < 2 ^ (prefixWord ++ tailWord_3633548).sum := by decide
  have hdescent : baseEnd_3633548 < baseStart_3633548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633572 : List Nat := [2, 3, 1, 2, 1, 1, 6, 2, 1, 1, 3]
def baseStart_3633572 : Nat := 118140960795 + 3633572 * 2 ^ 59
def prefixEnd_3633572 : Nat := 4983230072969 + 3 ^ 40 * 3633572 * 2
def baseEnd_3633572 : Nat := 1865768928718762866539513

theorem tailTrace_3633572 : CollatzResearch.WordTrace tailWord_3633572 prefixEnd_3633572 1865768928718762866539513 := by
  unfold tailWord_3633572
  simp only [CollatzResearch.WordTrace]
  refine ⟨66263629196098341768515485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88351505594797789024687313 66263629196098341768515485)
  ·
    refine ⟨24848860948536878163193307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66263629196098341768515485 24848860948536878163193307)
    ·
      refine ⟨37273291422805317244789961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24848860948536878163193307 37273291422805317244789961)
      ·
        refine ⟨27954968567103987933592471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37273291422805317244789961 27954968567103987933592471)
        ·
          refine ⟨41932452850655981900388707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27954968567103987933592471 41932452850655981900388707)
          ·
            refine ⟨62898679275983972850583061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41932452850655981900388707 62898679275983972850583061)
            ·
              refine ⟨2948375591061748727371081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62898679275983972850583061 2948375591061748727371081)
              ·
                refine ⟨2211281693296311545528311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2948375591061748727371081 2211281693296311545528311)
                ·
                  refine ⟨3316922539944467318292467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211281693296311545528311 3316922539944467318292467)
                  ·
                    refine ⟨4975383809916700977438701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3316922539944467318292467 4975383809916700977438701)
                    ·
                      refine ⟨1865768928718762866539513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4975383809916700977438701 1865768928718762866539513)
                      ·
                        rfl

theorem cell23_3633572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_3633572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633572 prefixEnd_3633572 := by exact prefixLift 3633572
  have htrace : WordTrace (prefixWord ++ tailWord_3633572) baseStart_3633572 baseEnd_3633572 := by
    simpa [prefixWord, tailWord_3633572, baseEnd_3633572] using wordTrace_append hprefix tailTrace_3633572
  have hstable : (prefixWord ++ tailWord_3633572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633572).length < 2 ^ (prefixWord ++ tailWord_3633572).sum := by decide
  have hdescent : baseEnd_3633572 < baseStart_3633572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633591 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_3633591 : Nat := 118140960795 + 3633591 * 2 ^ 59
def prefixEnd_3633591 : Nat := 4983230072969 + 3 ^ 40 * 3633591 * 2
def baseEnd_3633591 : Nat := 1865778684851198292201925

theorem tailTrace_3633591 : CollatzResearch.WordTrace tailWord_3633591 prefixEnd_3633591 1865778684851198292201925 := by
  unfold tailWord_3633591
  simp only [CollatzResearch.WordTrace]
  refine ⟨132527951379127849781972627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88351967586085233187981751 132527951379127849781972627)
  ·
    refine ⟨198791927068691774672958941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132527951379127849781972627 198791927068691774672958941)
    ·
      refine ⟨74546972650759415502359603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198791927068691774672958941 74546972650759415502359603)
      ·
        refine ⟨111820458976139123253539405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74546972650759415502359603 111820458976139123253539405)
        ·
          refine ⟨41932672116052171220077277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111820458976139123253539405 41932672116052171220077277)
          ·
            refine ⟨15724752043519564207528979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41932672116052171220077277 15724752043519564207528979)
            ·
              refine ⟨23587128065279346311293469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15724752043519564207528979 23587128065279346311293469)
              ·
                refine ⟨8845173024479754866735051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23587128065279346311293469 8845173024479754866735051)
                ·
                  refine ⟨13267759536719632300102577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8845173024479754866735051 13267759536719632300102577)
                  ·
                    refine ⟨9950819652539724225076933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13267759536719632300102577 9950819652539724225076933)
                    ·
                      refine ⟨1865778684851198292201925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9950819652539724225076933 1865778684851198292201925)
                      ·
                        rfl

theorem cell23_3633591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_3633591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633591 prefixEnd_3633591 := by exact prefixLift 3633591
  have htrace : WordTrace (prefixWord ++ tailWord_3633591) baseStart_3633591 baseEnd_3633591 := by
    simpa [prefixWord, tailWord_3633591, baseEnd_3633591] using wordTrace_append hprefix tailTrace_3633591
  have hstable : (prefixWord ++ tailWord_3633591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633591).length < 2 ^ (prefixWord ++ tailWord_3633591).sum := by decide
  have hdescent : baseEnd_3633591 < baseStart_3633591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633594 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_3633594 : Nat := 118140960795 + 3633594 * 2 ^ 59
def prefixEnd_3633594 : Nat := 4983230072969 + 3 ^ 40 * 3633594 * 2
def baseEnd_3633594 : Nat := 1865780225293161780464411

theorem tailTrace_3633594 : CollatzResearch.WordTrace tailWord_3633594 prefixEnd_3633594 1865780225293161780464411 := by
  unfold tailWord_3633594
  simp only [CollatzResearch.WordTrace]
  refine ⟨33132015199529245323582959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88352040532077987529554557 33132015199529245323582959)
  ·
    refine ⟨49698022799293867985374439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33132015199529245323582959 49698022799293867985374439)
    ·
      refine ⟨74547034198940801978061659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49698022799293867985374439 74547034198940801978061659)
      ·
        refine ⟨111820551298411202967092489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74547034198940801978061659 111820551298411202967092489)
        ·
          refine ⟨83865413473808402225319367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111820551298411202967092489 83865413473808402225319367)
          ·
            refine ⟨125798120210712603337979051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83865413473808402225319367 125798120210712603337979051)
            ·
              refine ⟨188697180316068905006968577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125798120210712603337979051 188697180316068905006968577)
              ·
                refine ⟨141522885237051678755226433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188697180316068905006968577 141522885237051678755226433)
                ·
                  refine ⟨106142163927788759066419825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141522885237051678755226433 106142163927788759066419825)
                  ·
                    refine ⟨79606622945841569299814869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106142163927788759066419825 79606622945841569299814869)
                    ·
                      refine ⟨1865780225293161780464411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79606622945841569299814869 1865780225293161780464411)
                      ·
                        rfl

theorem cell23_3633594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_3633594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633594 prefixEnd_3633594 := by exact prefixLift 3633594
  have htrace : WordTrace (prefixWord ++ tailWord_3633594) baseStart_3633594 baseEnd_3633594 := by
    simpa [prefixWord, tailWord_3633594, baseEnd_3633594] using wordTrace_append hprefix tailTrace_3633594
  have hstable : (prefixWord ++ tailWord_3633594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633594).length < 2 ^ (prefixWord ++ tailWord_3633594).sum := by decide
  have hdescent : baseEnd_3633594 < baseStart_3633594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633598 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_3633598 : Nat := 118140960795 + 3633598 * 2 ^ 59
def prefixEnd_3633598 : Nat := 4983230072969 + 3 ^ 40 * 3633598 * 2
def baseEnd_3633598 : Nat := 1865782279215779764814393

theorem tailTrace_3633598 : CollatzResearch.WordTrace tailWord_3633598 prefixEnd_3633598 1865782279215779764814393 := by
  unfold tailWord_3633598
  simp only [CollatzResearch.WordTrace]
  refine ⟨16566025836262811247184681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88352137793401659984984965 16566025836262811247184681)
  ·
    refine ⟨12424519377197108435388511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16566025836262811247184681 12424519377197108435388511)
    ·
      refine ⟨18636779065795662653082767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12424519377197108435388511 18636779065795662653082767)
      ·
        refine ⟨27955168598693493979624151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18636779065795662653082767 27955168598693493979624151)
        ·
          refine ⟨41932752898040240969436227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27955168598693493979624151 41932752898040240969436227)
          ·
            refine ⟨62899129347060361454154341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41932752898040240969436227 62899129347060361454154341)
            ·
              refine ⟨11793586752573817772653939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62899129347060361454154341 11793586752573817772653939)
              ·
                refine ⟨17690380128860726658980909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11793586752573817772653939 17690380128860726658980909)
                ·
                  refine ⟨6633892548322772497117841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17690380128860726658980909 6633892548322772497117841)
                  ·
                    refine ⟨4975419411242079372838381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6633892548322772497117841 4975419411242079372838381)
                    ·
                      refine ⟨1865782279215779764814393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4975419411242079372838381 1865782279215779764814393)
                      ·
                        rfl

theorem cell23_3633598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_3633598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633598 prefixEnd_3633598 := by exact prefixLift 3633598
  have htrace : WordTrace (prefixWord ++ tailWord_3633598) baseStart_3633598 baseEnd_3633598 := by
    simpa [prefixWord, tailWord_3633598, baseEnd_3633598] using wordTrace_append hprefix tailTrace_3633598
  have hstable : (prefixWord ++ tailWord_3633598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633598).length < 2 ^ (prefixWord ++ tailWord_3633598).sum := by decide
  have hdescent : baseEnd_3633598 < baseStart_3633598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633612 : List Nat := [2, 2, 1, 4, 3, 2, 2, 1, 1, 1, 4]
def baseStart_3633612 : Nat := 118140960795 + 3633612 * 2 ^ 59
def prefixEnd_3633612 : Nat := 4983230072969 + 3 ^ 40 * 3633612 * 2
def baseEnd_3633612 : Nat := 1865789467944942710039329

theorem tailTrace_3633612 : CollatzResearch.WordTrace tailWord_3633612 prefixEnd_3633612 1865789467944942710039329 := by
  unfold tailWord_3633612
  simp only [CollatzResearch.WordTrace]
  refine ⟨66264358656025885184243545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88352478208034513578991393 66264358656025885184243545)
  ·
    refine ⟨49698268992019413888182659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66264358656025885184243545 49698268992019413888182659)
    ·
      refine ⟨74547403488029120832273989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49698268992019413888182659 74547403488029120832273989)
      ·
        refine ⟨13977638154005460156051373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74547403488029120832273989 13977638154005460156051373)
        ·
          refine ⟨5241614307752047558519265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13977638154005460156051373 5241614307752047558519265)
          ·
            refine ⟨3931210730814035668889449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5241614307752047558519265 3931210730814035668889449)
            ·
              refine ⟨2948408048110526751667087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3931210730814035668889449 2948408048110526751667087)
              ·
                refine ⟨4422612072165790127500631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948408048110526751667087 4422612072165790127500631)
                ·
                  refine ⟨6633918108248685191250947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4422612072165790127500631 6633918108248685191250947)
                  ·
                    refine ⟨9950877162373027786876421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6633918108248685191250947 9950877162373027786876421)
                    ·
                      refine ⟨1865789467944942710039329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9950877162373027786876421 1865789467944942710039329)
                      ·
                        rfl

theorem cell23_3633612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_3633612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633612 prefixEnd_3633612 := by exact prefixLift 3633612
  have htrace : WordTrace (prefixWord ++ tailWord_3633612) baseStart_3633612 baseEnd_3633612 := by
    simpa [prefixWord, tailWord_3633612, baseEnd_3633612] using wordTrace_append hprefix tailTrace_3633612
  have hstable : (prefixWord ++ tailWord_3633612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633612).length < 2 ^ (prefixWord ++ tailWord_3633612).sum := by decide
  have hdescent : baseEnd_3633612 < baseStart_3633612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633618 : List Nat := [3, 2, 2, 4, 1, 1, 10]
def baseStart_3633618 : Nat := 118140960795 + 3633618 * 2 ^ 59
def prefixEnd_3633618 : Nat := 4983230072969 + 3 ^ 40 * 3633618 * 2
def baseEnd_3633618 : Nat := 23034475911467526994621

theorem tailTrace_3633618 : CollatzResearch.WordTrace tailWord_3633618 prefixEnd_3633618 23034475911467526994621 := by
  unfold tailWord_3633618
  simp only [CollatzResearch.WordTrace]
  refine ⟨33132234037507508348301377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88352624100020022262137005 33132234037507508348301377)
  ·
    refine ⟨24849175528130631261226033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33132234037507508348301377 24849175528130631261226033)
    ·
      refine ⟨18636881646097973445919525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24849175528130631261226033 18636881646097973445919525)
      ·
        refine ⟨3494415308643370021109911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18636881646097973445919525 3494415308643370021109911)
        ·
          refine ⟨5241622962965055031664867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3494415308643370021109911 5241622962965055031664867)
          ·
            refine ⟨7862434444447582547497301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5241622962965055031664867 7862434444447582547497301)
            ·
              refine ⟨23034475911467526994621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7862434444447582547497301 23034475911467526994621)
              ·
                rfl

theorem cell23_3633618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 10].length) (baseStart_3633618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633618 prefixEnd_3633618 := by exact prefixLift 3633618
  have htrace : WordTrace (prefixWord ++ tailWord_3633618) baseStart_3633618 baseEnd_3633618 := by
    simpa [prefixWord, tailWord_3633618, baseEnd_3633618] using wordTrace_append hprefix tailTrace_3633618
  have hstable : (prefixWord ++ tailWord_3633618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633618).length < 2 ^ (prefixWord ++ tailWord_3633618).sum := by decide
  have hdescent : baseEnd_3633618 < baseStart_3633618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633645 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3633645 : Nat := 118140960795 + 3633645 * 2 ^ 59
def prefixEnd_3633645 : Nat := 4983230072969 + 3 ^ 40 * 3633645 * 2
def baseEnd_3633645 : Nat := 1865806412806541080926677

theorem tailTrace_3633645 : CollatzResearch.WordTrace tailWord_3633645 prefixEnd_3633645 1865806412806541080926677 := by
  unfold tailWord_3633645
  simp only [CollatzResearch.WordTrace]
  refine ⟨132529920920932217004438389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88353280613954811336292259 132529920920932217004438389)
  ·
    refine ⟨12424680086337395344166099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132529920920932217004438389 12424680086337395344166099)
    ·
      refine ⟨18637020129506093016249149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12424680086337395344166099 18637020129506093016249149)
      ·
        refine ⟨6988882548564784881093431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18637020129506093016249149 6988882548564784881093431)
        ·
          refine ⟨10483323822847177321640147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6988882548564784881093431 10483323822847177321640147)
          ·
            refine ⟨15724985734270765982460221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10483323822847177321640147 15724985734270765982460221)
            ·
              refine ⟨5896869650351537243422583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15724985734270765982460221 5896869650351537243422583)
              ·
                refine ⟨8845304475527305865133875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5896869650351537243422583 8845304475527305865133875)
                ·
                  refine ⟨13267956713290958797700813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8845304475527305865133875 13267956713290958797700813)
                  ·
                    refine ⟨4975483767484109549137805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13267956713290958797700813 4975483767484109549137805)
                    ·
                      refine ⟨1865806412806541080926677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4975483767484109549137805 1865806412806541080926677)
                      ·
                        rfl

theorem cell23_3633645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3633645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633645 prefixEnd_3633645 := by exact prefixLift 3633645
  have htrace : WordTrace (prefixWord ++ tailWord_3633645) baseStart_3633645 baseEnd_3633645 := by
    simpa [prefixWord, tailWord_3633645, baseEnd_3633645] using wordTrace_append hprefix tailTrace_3633645
  have hstable : (prefixWord ++ tailWord_3633645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633645).length < 2 ^ (prefixWord ++ tailWord_3633645).sum := by decide
  have hdescent : baseEnd_3633645 < baseStart_3633645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633681 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_3633681 : Nat := 118140960795 + 3633681 * 2 ^ 59
def prefixEnd_3633681 : Nat := 4983230072969 + 3 ^ 40 * 3633681 * 2
def baseEnd_3633681 : Nat := 1865824898110102940076511

theorem tailTrace_3633681 : CollatzResearch.WordTrace tailWord_3633681 prefixEnd_3633681 1865824898110102940076511 := by
  unfold tailWord_3633681
  simp only [CollatzResearch.WordTrace]
  refine ⟨132531233948801795152748897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88354155965867863435165931 132531233948801795152748897)
  ·
    refine ⟨99398425461601346364561673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132531233948801795152748897 99398425461601346364561673)
    ·
      refine ⟨74548819096201009773421255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99398425461601346364561673 74548819096201009773421255)
      ·
        refine ⟨111823228644301514660131883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74548819096201009773421255 111823228644301514660131883)
        ·
          refine ⟨167734842966452271990197825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111823228644301514660131883 167734842966452271990197825)
          ·
            refine ⟨125801132224839203992648369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167734842966452271990197825 125801132224839203992648369)
            ·
              refine ⟨94350849168629402994486277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125801132224839203992648369 94350849168629402994486277)
              ·
                refine ⟨17690784219118013061466177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94350849168629402994486277 17690784219118013061466177)
                ·
                  refine ⟨13268088164338509796099633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17690784219118013061466177 13268088164338509796099633)
                  ·
                    refine ⟨9951066123253882347074725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13268088164338509796099633 9951066123253882347074725)
                    ·
                      refine ⟨1865824898110102940076511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9951066123253882347074725 1865824898110102940076511)
                      ·
                        rfl

theorem cell23_3633681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_3633681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633681 prefixEnd_3633681 := by exact prefixLift 3633681
  have htrace : WordTrace (prefixWord ++ tailWord_3633681) baseStart_3633681 baseEnd_3633681 := by
    simpa [prefixWord, tailWord_3633681, baseEnd_3633681] using wordTrace_append hprefix tailTrace_3633681
  have hstable : (prefixWord ++ tailWord_3633681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633681).length < 2 ^ (prefixWord ++ tailWord_3633681).sum := by decide
  have hdescent : baseEnd_3633681 < baseStart_3633681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633685 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 4, 2, 2]
def baseStart_3633685 : Nat := 118140960795 + 3633685 * 2 ^ 59
def prefixEnd_3633685 : Nat := 4983230072969 + 3 ^ 40 * 3633685 * 2
def baseEnd_3633685 : Nat := 1865826952032720924426493

theorem tailTrace_3633685 : CollatzResearch.WordTrace tailWord_3633685 prefixEnd_3633685 1865826952032720924426493 := by
  unfold tailWord_3633685
  simp only [CollatzResearch.WordTrace]
  refine ⟨132531379840787303835894509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88354253227191535890596339 132531379840787303835894509)
  ·
    refine ⟨49699267440295238938460441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132531379840787303835894509 49699267440295238938460441)
    ·
      refine ⟨37274450580221429203845331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49699267440295238938460441 37274450580221429203845331)
      ·
        refine ⟨55911675870332143805767997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37274450580221429203845331 55911675870332143805767997)
        ·
          refine ⟨20966878451374553927162999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55911675870332143805767997 20966878451374553927162999)
          ·
            refine ⟨31450317677061830890744499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20966878451374553927162999 31450317677061830890744499)
            ·
              refine ⟨47175476515592746336116749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31450317677061830890744499 47175476515592746336116749)
              ·
                refine ⟨17690803693347279876043781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47175476515592746336116749 17690803693347279876043781)
                ·
                  refine ⟨3317025692502614976758209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17690803693347279876043781 3317025692502614976758209)
                  ·
                    refine ⟨2487769269376961232568657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3317025692502614976758209 2487769269376961232568657)
                    ·
                      refine ⟨1865826952032720924426493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487769269376961232568657 1865826952032720924426493)
                      ·
                        rfl

theorem cell23_3633685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_3633685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633685 prefixEnd_3633685 := by exact prefixLift 3633685
  have htrace : WordTrace (prefixWord ++ tailWord_3633685) baseStart_3633685 baseEnd_3633685 := by
    simpa [prefixWord, tailWord_3633685, baseEnd_3633685] using wordTrace_append hprefix tailTrace_3633685
  have hstable : (prefixWord ++ tailWord_3633685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633685).length < 2 ^ (prefixWord ++ tailWord_3633685).sum := by decide
  have hdescent : baseEnd_3633685 < baseStart_3633685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633696 : List Nat := [2, 1, 1, 6, 3, 1, 2, 1, 2, 1, 3]
def baseStart_3633696 : Nat := 118140960795 + 3633696 * 2 ^ 59
def prefixEnd_3633696 : Nat := 4983230072969 + 3 ^ 40 * 3633696 * 2
def baseEnd_3633696 : Nat := 1865832600319920381388943

theorem tailTrace_3633696 : CollatzResearch.WordTrace tailWord_3633696 prefixEnd_3633696 1865832600319920381388943 := by
  unfold tailWord_3633696
  simp only [CollatzResearch.WordTrace]
  refine ⟨66265890521873726357272471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88354520695831635143029961 66265890521873726357272471)
  ·
    refine ⟨99398835782810589535908707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66265890521873726357272471 99398835782810589535908707)
    ·
      refine ⟨149098253674215884303863061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99398835782810589535908707 149098253674215884303863061)
      ·
        refine ⟨6988980640978869576743581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149098253674215884303863061 6988980640978869576743581)
        ·
          refine ⟨2620867740367076091278843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6988980640978869576743581 2620867740367076091278843)
          ·
            refine ⟨3931301610550614136918265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620867740367076091278843 3931301610550614136918265)
            ·
              refine ⟨2948476207912960602688699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3931301610550614136918265 2948476207912960602688699)
              ·
                refine ⟨4422714311869440904033049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948476207912960602688699 4422714311869440904033049)
                ·
                  refine ⟨3317035733902080678024787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4422714311869440904033049 3317035733902080678024787)
                  ·
                    refine ⟨4975553600853121017037181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3317035733902080678024787 4975553600853121017037181)
                    ·
                      refine ⟨1865832600319920381388943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4975553600853121017037181 1865832600319920381388943)
                      ·
                        rfl

theorem cell23_3633696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_3633696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633696 prefixEnd_3633696 := by exact prefixLift 3633696
  have htrace : WordTrace (prefixWord ++ tailWord_3633696) baseStart_3633696 baseEnd_3633696 := by
    simpa [prefixWord, tailWord_3633696, baseEnd_3633696] using wordTrace_append hprefix tailTrace_3633696
  have hstable : (prefixWord ++ tailWord_3633696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633696).length < 2 ^ (prefixWord ++ tailWord_3633696).sum := by decide
  have hdescent : baseEnd_3633696 < baseStart_3633696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633738 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 2, 5]
def baseStart_3633738 : Nat := 118140960795 + 3633738 * 2 ^ 59
def prefixEnd_3633738 : Nat := 4983230072969 + 3 ^ 40 * 3633738 * 2
def baseEnd_3633738 : Nat := 621951388835803072354583

theorem tailTrace_3633738 : CollatzResearch.WordTrace tailWord_3633738 prefixEnd_3633738 621951388835803072354583 := by
  unfold tailWord_3633738
  simp only [CollatzResearch.WordTrace]
  refine ⟨33133328227398823471893467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88355541939730195925049245 33133328227398823471893467)
  ·
    refine ⟨49699992341098235207840201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33133328227398823471893467 49699992341098235207840201)
    ·
      refine ⟨37274994255823676405880151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49699992341098235207840201 37274994255823676405880151)
      ·
        refine ⟨55912491383735514608820227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37274994255823676405880151 55912491383735514608820227)
        ·
          refine ⟨83868737075603271913230341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55912491383735514608820227 83868737075603271913230341)
          ·
            refine ⟨15725388201675613483730689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83868737075603271913230341 15725388201675613483730689)
            ·
              refine ⟨11794041151256710112798017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15725388201675613483730689 11794041151256710112798017)
              ·
                refine ⟨8845530863442532584598513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11794041151256710112798017 8845530863442532584598513)
                ·
                  refine ⟨6634148147581899438448885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8845530863442532584598513 6634148147581899438448885)
                  ·
                    refine ⟨621951388835803072354583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6634148147581899438448885 621951388835803072354583)
                    ·
                      rfl

theorem cell23_3633738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_3633738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633738 prefixEnd_3633738 := by exact prefixLift 3633738
  have htrace : WordTrace (prefixWord ++ tailWord_3633738) baseStart_3633738 baseEnd_3633738 := by
    simpa [prefixWord, tailWord_3633738, baseEnd_3633738] using wordTrace_append hprefix tailTrace_3633738
  have hstable : (prefixWord ++ tailWord_3633738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633738).length < 2 ^ (prefixWord ++ tailWord_3633738).sum := by decide
  have hdescent : baseEnd_3633738 < baseStart_3633738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633748 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_3633748 : Nat := 118140960795 + 3633748 * 2 ^ 59
def prefixEnd_3633748 : Nat := 4983230072969 + 3 ^ 40 * 3633748 * 2
def baseEnd_3633748 : Nat := 1865859301313954177938703

theorem tailTrace_3633748 : CollatzResearch.WordTrace tailWord_3633748 prefixEnd_3633748 1865859301313954177938703 := by
  unfold tailWord_3633748
  simp only [CollatzResearch.WordTrace]
  refine ⟨66266838819779532797718949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88355785093039377063625265 66266838819779532797718949)
  ·
    refine ⟨12425032278708662399572303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66266838819779532797718949 12425032278708662399572303)
    ·
      refine ⟨18637548418062993599358455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12425032278708662399572303 18637548418062993599358455)
      ·
        refine ⟨27956322627094490399037683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18637548418062993599358455 27956322627094490399037683)
        ·
          refine ⟨41934483940641735598556525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27956322627094490399037683 41934483940641735598556525)
          ·
            refine ⟨15725431477740650849458697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41934483940641735598556525 15725431477740650849458697)
            ·
              refine ⟨11794073608305488137094023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15725431477740650849458697 11794073608305488137094023)
              ·
                refine ⟨17691110412458232205641035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11794073608305488137094023 17691110412458232205641035)
                ·
                  refine ⟨26536665618687348308461553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17691110412458232205641035 26536665618687348308461553)
                  ·
                    refine ⟨19902499214015511231346165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26536665618687348308461553 19902499214015511231346165)
                    ·
                      refine ⟨1865859301313954177938703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19902499214015511231346165 1865859301313954177938703)
                      ·
                        rfl

theorem cell23_3633748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_3633748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633748 prefixEnd_3633748 := by exact prefixLift 3633748
  have htrace : WordTrace (prefixWord ++ tailWord_3633748) baseStart_3633748 baseEnd_3633748 := by
    simpa [prefixWord, tailWord_3633748, baseEnd_3633748] using wordTrace_append hprefix tailTrace_3633748
  have hstable : (prefixWord ++ tailWord_3633748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633748).length < 2 ^ (prefixWord ++ tailWord_3633748).sum := by decide
  have hdescent : baseEnd_3633748 < baseStart_3633748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633771 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 4]
def baseStart_3633771 : Nat := 118140960795 + 3633771 * 2 ^ 59
def prefixEnd_3633771 : Nat := 4983230072969 + 3 ^ 40 * 3633771 * 2
def baseEnd_3633771 : Nat := 1865871111369007587951097

theorem tailTrace_3633771 : CollatzResearch.WordTrace tailWord_3633771 prefixEnd_3633771 1865871111369007587951097 := by
  unfold tailWord_3633771
  simp only [CollatzResearch.WordTrace]
  refine ⟨132534516518475740523525167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88356344345650493682350111 132534516518475740523525167)
  ·
    refine ⟨198801774777713610785287751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132534516518475740523525167 198801774777713610785287751)
    ·
      refine ⟨298202662166570416177931627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198801774777713610785287751 298202662166570416177931627)
      ·
        refine ⟨447303993249855624266897441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298202662166570416177931627 447303993249855624266897441)
        ·
          refine ⟨335477994937391718200173081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447303993249855624266897441 335477994937391718200173081)
          ·
            refine ⟨251608496203043788650129811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335477994937391718200173081 251608496203043788650129811)
            ·
              refine ⟨377412744304565682975194717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251608496203043788650129811 377412744304565682975194717)
              ·
                refine ⟨141529779114212131115698019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377412744304565682975194717 141529779114212131115698019)
                ·
                  refine ⟨212294668671318196673547029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141529779114212131115698019 212294668671318196673547029)
                  ·
                    refine ⟨9951312593968040469072517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 212294668671318196673547029 9951312593968040469072517)
                    ·
                      refine ⟨1865871111369007587951097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9951312593968040469072517 1865871111369007587951097)
                      ·
                        rfl

theorem cell23_3633771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 4].length) (baseStart_3633771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633771 prefixEnd_3633771 := by exact prefixLift 3633771
  have htrace : WordTrace (prefixWord ++ tailWord_3633771) baseStart_3633771 baseEnd_3633771 := by
    simpa [prefixWord, tailWord_3633771, baseEnd_3633771] using wordTrace_append hprefix tailTrace_3633771
  have hstable : (prefixWord ++ tailWord_3633771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633771).length < 2 ^ (prefixWord ++ tailWord_3633771).sum := by decide
  have hdescent : baseEnd_3633771 < baseStart_3633771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633802 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 3, 4]
def baseStart_3633802 : Nat := 118140960795 + 3633802 * 2 ^ 59
def prefixEnd_3633802 : Nat := 4983230072969 + 3 ^ 40 * 3633802 * 2
def baseEnd_3633802 : Nat := 621962343089765655554485

theorem tailTrace_3633802 : CollatzResearch.WordTrace tailWord_3633802 prefixEnd_3633802 621962343089765655554485 := by
  unfold tailWord_3633802
  simp only [CollatzResearch.WordTrace]
  refine ⟨33133911795340858204475915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88357098120908955211935773 33133911795340858204475915)
  ·
    refine ⟨49700867693011287306713873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33133911795340858204475915 49700867693011287306713873)
    ·
      refine ⟨37275650769758465480035405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49700867693011287306713873 37275650769758465480035405)
      ·
        refine ⟨13978369038659424555013277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37275650769758465480035405 13978369038659424555013277)
        ·
          refine ⟨5241888389497284208129979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13978369038659424555013277 5241888389497284208129979)
          ·
            refine ⟨7862832584245926312194969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5241888389497284208129979 7862832584245926312194969)
            ·
              refine ⟨5897124438184444734146227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7862832584245926312194969 5897124438184444734146227)
              ·
                refine ⟨8845686657276667101219341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5897124438184444734146227 8845686657276667101219341)
                ·
                  refine ⟨3317132496478750162957253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8845686657276667101219341 3317132496478750162957253)
                  ·
                    refine ⟨621962343089765655554485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3317132496478750162957253 621962343089765655554485)
                    ·
                      rfl

theorem cell23_3633802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_3633802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633802 prefixEnd_3633802 := by exact prefixLift 3633802
  have htrace : WordTrace (prefixWord ++ tailWord_3633802) baseStart_3633802 baseEnd_3633802 := by
    simpa [prefixWord, tailWord_3633802, baseEnd_3633802] using wordTrace_append hprefix tailTrace_3633802
  have hstable : (prefixWord ++ tailWord_3633802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633802).length < 2 ^ (prefixWord ++ tailWord_3633802).sum := by decide
  have hdescent : baseEnd_3633802 < baseStart_3633802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633815 : List Nat := [1, 1, 3, 3, 2, 1, 5, 1, 6]
def baseStart_3633815 : Nat := 118140960795 + 3633815 * 2 ^ 59
def prefixEnd_3633815 : Nat := 4983230072969 + 3 ^ 40 * 3633815 * 2
def baseEnd_3633815 : Nat := 207321522724200601755655

theorem tailTrace_3633815 : CollatzResearch.WordTrace tailWord_3633815 prefixEnd_3633815 207321522724200601755655 := by
  unfold tailWord_3633815
  simp only [CollatzResearch.WordTrace]
  refine ⟨132536121330316336038126899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88357414220210890692084599 132536121330316336038126899)
  ·
    refine ⟨198804181995474504057190349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132536121330316336038126899 198804181995474504057190349)
    ·
      refine ⟨74551568248302939021446381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198804181995474504057190349 74551568248302939021446381)
      ·
        refine ⟨27956838093113602133042393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74551568248302939021446381 27956838093113602133042393)
        ·
          refine ⟨20967628569835201599781795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27956838093113602133042393 20967628569835201599781795)
          ·
            refine ⟨31451442854752802399672693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20967628569835201599781795 31451442854752802399672693)
            ·
              refine ⟨2948572767633075224969315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31451442854752802399672693 2948572767633075224969315)
              ·
                refine ⟨4422859151449612837453973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948572767633075224969315 4422859151449612837453973)
                ·
                  refine ⟨207321522724200601755655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4422859151449612837453973 207321522724200601755655)
                  ·
                    rfl

theorem cell23_3633815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 6].length) (baseStart_3633815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633815 prefixEnd_3633815 := by exact prefixLift 3633815
  have htrace : WordTrace (prefixWord ++ tailWord_3633815) baseStart_3633815 baseEnd_3633815 := by
    simpa [prefixWord, tailWord_3633815, baseEnd_3633815] using wordTrace_append hprefix tailTrace_3633815
  have hstable : (prefixWord ++ tailWord_3633815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633815).length < 2 ^ (prefixWord ++ tailWord_3633815).sum := by decide
  have hdescent : baseEnd_3633815 < baseStart_3633815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633848 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_3633848 : Nat := 118140960795 + 3633848 * 2 ^ 59
def prefixEnd_3633848 : Nat := 4983230072969 + 3 ^ 40 * 3633848 * 2
def baseEnd_3633848 : Nat := 1865910649379403786688243

theorem tailTrace_3633848 : CollatzResearch.WordTrace tailWord_3633848 prefixEnd_3633848 1865910649379403786688243 := by
  unfold tailWord_3633848
  simp only [CollatzResearch.WordTrace]
  refine ⟨66268662469598391337039099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88358216626131188449385465 66268662469598391337039099)
  ·
    refine ⟨99402993704397587005558649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66268662469598391337039099 99402993704397587005558649)
    ·
      refine ⟨74552245278298190254168987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99402993704397587005558649 74552245278298190254168987)
      ·
        refine ⟨111828367917447285381253481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74552245278298190254168987 111828367917447285381253481)
        ·
          refine ⟨83871275938085464035940111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111828367917447285381253481 83871275938085464035940111)
          ·
            refine ⟨125806913907128196053910167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83871275938085464035940111 125806913907128196053910167)
            ·
              refine ⟨188710370860692294080865251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125806913907128196053910167 188710370860692294080865251)
              ·
                refine ⟨283065556291038441121297877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188710370860692294080865251 283065556291038441121297877)
                ·
                  refine ⟨6634348975571213463780419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 283065556291038441121297877 6634348975571213463780419)
                  ·
                    refine ⟨9951523463356820195670629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6634348975571213463780419 9951523463356820195670629)
                    ·
                      refine ⟨1865910649379403786688243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9951523463356820195670629 1865910649379403786688243)
                      ·
                        rfl

theorem cell23_3633848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_3633848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633848 prefixEnd_3633848 := by exact prefixLift 3633848
  have htrace : WordTrace (prefixWord ++ tailWord_3633848) baseStart_3633848 baseEnd_3633848 := by
    simpa [prefixWord, tailWord_3633848, baseEnd_3633848] using wordTrace_append hprefix tailTrace_3633848
  have hstable : (prefixWord ++ tailWord_3633848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633848).length < 2 ^ (prefixWord ++ tailWord_3633848).sum := by decide
  have hdescent : baseEnd_3633848 < baseStart_3633848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633852 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 2, 3, 2]
def baseStart_3633852 : Nat := 118140960795 + 3633852 * 2 ^ 59
def prefixEnd_3633852 : Nat := 4983230072969 + 3 ^ 40 * 3633852 * 2
def baseEnd_3633852 : Nat := 1865912703302021771038225

theorem tailTrace_3633852 : CollatzResearch.WordTrace tailWord_3633852 prefixEnd_3633852 1865912703302021771038225 := by
  unfold tailWord_3633852
  simp only [CollatzResearch.WordTrace]
  refine ⟨66268735415591145678611905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88358313887454860904815873 66268735415591145678611905)
  ·
    refine ⟨49701551561693359258958929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66268735415591145678611905 49701551561693359258958929)
    ·
      refine ⟨37276163671270019444219197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49701551561693359258958929 37276163671270019444219197)
      ·
        refine ⟨13978561376726257291582199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37276163671270019444219197 13978561376726257291582199)
        ·
          refine ⟨20967842065089385937373299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13978561376726257291582199 20967842065089385937373299)
          ·
            refine ⟨31451763097634078906059949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20967842065089385937373299 31451763097634078906059949)
            ·
              refine ⟨11794411161612779589772481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31451763097634078906059949 11794411161612779589772481)
              ·
                refine ⟨8845808371209584692329361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11794411161612779589772481 8845808371209584692329361)
                ·
                  refine ⟨6634356278407188519247021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8845808371209584692329361 6634356278407188519247021)
                  ·
                    refine ⟨2487883604402695694717633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6634356278407188519247021 2487883604402695694717633)
                    ·
                      refine ⟨1865912703302021771038225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487883604402695694717633 1865912703302021771038225)
                      ·
                        rfl

theorem cell23_3633852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_3633852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633852 prefixEnd_3633852 := by exact prefixLift 3633852
  have htrace : WordTrace (prefixWord ++ tailWord_3633852) baseStart_3633852 baseEnd_3633852 := by
    simpa [prefixWord, tailWord_3633852, baseEnd_3633852] using wordTrace_append hprefix tailTrace_3633852
  have hstable : (prefixWord ++ tailWord_3633852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633852).length < 2 ^ (prefixWord ++ tailWord_3633852).sum := by decide
  have hdescent : baseEnd_3633852 < baseStart_3633852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633882 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2]
def baseStart_3633882 : Nat := 118140960795 + 3633882 * 2 ^ 59
def prefixEnd_3633882 : Nat := 4983230072969 + 3 ^ 40 * 3633882 * 2
def baseEnd_3633882 : Nat := 1865928107721656653663087

theorem tailTrace_3633882 : CollatzResearch.WordTrace tailWord_3633882 prefixEnd_3633882 1865928107721656653663087 := by
  unfold tailWord_3633882
  simp only [CollatzResearch.WordTrace]
  refine ⟨33134641255268401620203975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88359043347382404320543933 33134641255268401620203975)
  ·
    refine ⟨49701961882902602430305963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33134641255268401620203975 49701961882902602430305963)
    ·
      refine ⟨74552942824353903645458945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49701961882902602430305963 74552942824353903645458945)
      ·
        refine ⟨55914707118265427734094209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74552942824353903645458945 55914707118265427734094209)
        ·
          refine ⟨41936030338699070800570657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55914707118265427734094209 41936030338699070800570657)
          ·
            refine ⟨31452022754024303100427993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41936030338699070800570657 31452022754024303100427993)
            ·
              refine ⟨23589017065518227325320995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31452022754024303100427993 23589017065518227325320995)
              ·
                refine ⟨35383525598277340987981493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23589017065518227325320995 35383525598277340987981493)
                ·
                  refine ⟨3317205524838500717623265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35383525598277340987981493 3317205524838500717623265)
                  ·
                    refine ⟨2487904143628875538217449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3317205524838500717623265 2487904143628875538217449)
                    ·
                      refine ⟨1865928107721656653663087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487904143628875538217449 1865928107721656653663087)
                      ·
                        rfl

theorem cell23_3633882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_3633882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633882 prefixEnd_3633882 := by exact prefixLift 3633882
  have htrace : WordTrace (prefixWord ++ tailWord_3633882) baseStart_3633882 baseEnd_3633882 := by
    simpa [prefixWord, tailWord_3633882, baseEnd_3633882] using wordTrace_append hprefix tailTrace_3633882
  have hstable : (prefixWord ++ tailWord_3633882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633882).length < 2 ^ (prefixWord ++ tailWord_3633882).sum := by decide
  have hdescent : baseEnd_3633882 < baseStart_3633882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633899 : List Nat := [1, 1, 1, 1, 2, 4, 1, 7, 1, 2, 2]
def baseStart_3633899 : Nat := 118140960795 + 3633899 * 2 ^ 59
def prefixEnd_3633899 : Nat := 4983230072969 + 3 ^ 40 * 3633899 * 2
def baseEnd_3633899 : Nat := 1865936836892783087150509

theorem tailTrace_3633899 : CollatzResearch.WordTrace tailWord_3633899 prefixEnd_3633899 1865936836892783087150509 := by
  unfold tailWord_3633899
  simp only [CollatzResearch.WordTrace]
  refine ⟨132539185062012018384184751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88359456708008012256123167 132539185062012018384184751)
  ·
    refine ⟨198808777593018027576277127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132539185062012018384184751 198808777593018027576277127)
    ·
      refine ⟨298213166389527041364415691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198808777593018027576277127 298213166389527041364415691)
      ·
        refine ⟨447319749584290562046623537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298213166389527041364415691 447319749584290562046623537)
        ·
          refine ⟨335489812188217921534967653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447319749584290562046623537 335489812188217921534967653)
          ·
            refine ⟨62904339785290860287806435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 335489812188217921534967653 62904339785290860287806435)
            ·
              refine ⟨94356509677936290431709653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62904339785290860287806435 94356509677936290431709653)
              ·
                refine ⟨2211480695576631806993195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 94356509677936290431709653 2211480695576631806993195)
                ·
                  refine ⟨3317221043364947710489793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211480695576631806993195 3317221043364947710489793)
                  ·
                    refine ⟨2487915782523710782867345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3317221043364947710489793 2487915782523710782867345)
                    ·
                      refine ⟨1865936836892783087150509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487915782523710782867345 1865936836892783087150509)
                      ·
                        rfl

theorem cell23_3633899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 1, 2, 2].length) (baseStart_3633899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633899 prefixEnd_3633899 := by exact prefixLift 3633899
  have htrace : WordTrace (prefixWord ++ tailWord_3633899) baseStart_3633899 baseEnd_3633899 := by
    simpa [prefixWord, tailWord_3633899, baseEnd_3633899] using wordTrace_append hprefix tailTrace_3633899
  have hstable : (prefixWord ++ tailWord_3633899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633899).length < 2 ^ (prefixWord ++ tailWord_3633899).sum := by decide
  have hdescent : baseEnd_3633899 < baseStart_3633899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633902 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_3633902 : Nat := 118140960795 + 3633902 * 2 ^ 59
def prefixEnd_3633902 : Nat := 4983230072969 + 3 ^ 40 * 3633902 * 2
def baseEnd_3633902 : Nat := 1865938377334746575412995

theorem tailTrace_3633902 : CollatzResearch.WordTrace tailWord_3633902 prefixEnd_3633902 1865938377334746575412995 := by
  unfold tailWord_3633902
  simp only [CollatzResearch.WordTrace]
  refine ⟨16567411810125143737067995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88359529654000766597695973 16567411810125143737067995)
  ·
    refine ⟨24851117715187715605601993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16567411810125143737067995 24851117715187715605601993)
    ·
      refine ⟨18638338286390786704201495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24851117715187715605601993 18638338286390786704201495)
      ·
        refine ⟨27957507429586180056302243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18638338286390786704201495 27957507429586180056302243)
        ·
          refine ⟨41936261144379270084453365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27957507429586180056302243 41936261144379270084453365)
          ·
            refine ⟨3931524482285556570417503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41936261144379270084453365 3931524482285556570417503)
            ·
              refine ⟨5897286723428334855626255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3931524482285556570417503 5897286723428334855626255)
              ·
                refine ⟨8845930085142502283439383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5897286723428334855626255 8845930085142502283439383)
                ·
                  refine ⟨13268895127713753425159075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8845930085142502283439383 13268895127713753425159075)
                  ·
                    refine ⟨19903342691570630137738613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13268895127713753425159075 19903342691570630137738613)
                    ·
                      refine ⟨1865938377334746575412995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19903342691570630137738613 1865938377334746575412995)
                      ·
                        rfl

theorem cell23_3633902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_3633902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633902 prefixEnd_3633902 := by exact prefixLift 3633902
  have htrace : WordTrace (prefixWord ++ tailWord_3633902) baseStart_3633902 baseEnd_3633902 := by
    simpa [prefixWord, tailWord_3633902, baseEnd_3633902] using wordTrace_append hprefix tailTrace_3633902
  have hstable : (prefixWord ++ tailWord_3633902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633902).length < 2 ^ (prefixWord ++ tailWord_3633902).sum := by decide
  have hdescent : baseEnd_3633902 < baseStart_3633902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633915 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 8, 1, 3]
def baseStart_3633915 : Nat := 118140960795 + 3633915 * 2 ^ 59
def prefixEnd_3633915 : Nat := 4983230072969 + 3 ^ 40 * 3633915 * 2
def baseEnd_3633915 : Nat := 1865945052583255024550435

theorem tailTrace_3633915 : CollatzResearch.WordTrace tailWord_3633915 prefixEnd_3633915 1865945052583255024550435 := by
  unfold tailWord_3633915
  simp only [CollatzResearch.WordTrace]
  refine ⟨132539768629954053116767199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88359845753302702077844799 132539768629954053116767199)
  ·
    refine ⟨198809652944931079675150799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132539768629954053116767199 198809652944931079675150799)
    ·
      refine ⟨298214479417396619512726199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198809652944931079675150799 298214479417396619512726199)
      ·
        refine ⟨447321719126094929269089299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298214479417396619512726199 447321719126094929269089299)
        ·
          refine ⟨670982578689142393903633949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447321719126094929269089299 670982578689142393903633949)
          ·
            refine ⟨251618467008428397713862731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 670982578689142393903633949 251618467008428397713862731)
            ·
              refine ⟨377427700512642596570794097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251618467008428397713862731 377427700512642596570794097)
              ·
                refine ⟨283070775384481947428095573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377427700512642596570794097 283070775384481947428095573)
                ·
                  refine ⟨3317235649036897821422995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 283070775384481947428095573 3317235649036897821422995)
                  ·
                    refine ⟨4975853473555346732134493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3317235649036897821422995 4975853473555346732134493)
                    ·
                      refine ⟨1865945052583255024550435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4975853473555346732134493 1865945052583255024550435)
                      ·
                        rfl

theorem cell23_3633915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 1, 3].length) (baseStart_3633915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633915 prefixEnd_3633915 := by exact prefixLift 3633915
  have htrace : WordTrace (prefixWord ++ tailWord_3633915) baseStart_3633915 baseEnd_3633915 := by
    simpa [prefixWord, tailWord_3633915, baseEnd_3633915] using wordTrace_append hprefix tailTrace_3633915
  have hstable : (prefixWord ++ tailWord_3633915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633915).length < 2 ^ (prefixWord ++ tailWord_3633915).sum := by decide
  have hdescent : baseEnd_3633915 < baseStart_3633915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633916 : List Nat := [2, 2, 2, 1, 3, 3, 1, 4, 1, 2, 2]
def baseStart_3633916 : Nat := 118140960795 + 3633916 * 2 ^ 59
def prefixEnd_3633916 : Nat := 4983230072969 + 3 ^ 40 * 3633916 * 2
def baseEnd_3633916 : Nat := 1865945566063909520637931

theorem tailTrace_3633916 : CollatzResearch.WordTrace tailWord_3633916 prefixEnd_3633916 1865945566063909520637931 := by
  unfold tailWord_3633916
  simp only [CollatzResearch.WordTrace]
  refine ⟨66269902551475215143776801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88359870068633620191702401 66269902551475215143776801)
  ·
    refine ⟨49702426913606411357832601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66269902551475215143776801 49702426913606411357832601)
    ·
      refine ⟨37276820185204808518374451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49702426913606411357832601 37276820185204808518374451)
      ·
        refine ⟨55915230277807212777561677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37276820185204808518374451 55915230277807212777561677)
        ·
          refine ⟨20968211354177704791585629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55915230277807212777561677 20968211354177704791585629)
          ·
            refine ⟨7863079257816639296844611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20968211354177704791585629 7863079257816639296844611)
            ·
              refine ⟨11794618886724958945266917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7863079257816639296844611 11794618886724958945266917)
              ·
                refine ⟨2211491041260929802237547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11794618886724958945266917 2211491041260929802237547)
                ·
                  refine ⟨3317236561891394703356321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211491041260929802237547 3317236561891394703356321)
                  ·
                    refine ⟨2487927421418546027517241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3317236561891394703356321 2487927421418546027517241)
                    ·
                      refine ⟨1865945566063909520637931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2487927421418546027517241 1865945566063909520637931)
                      ·
                        rfl

theorem cell23_3633916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_3633916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633916 prefixEnd_3633916 := by exact prefixLift 3633916
  have htrace : WordTrace (prefixWord ++ tailWord_3633916) baseStart_3633916 baseEnd_3633916 := by
    simpa [prefixWord, tailWord_3633916, baseEnd_3633916] using wordTrace_append hprefix tailTrace_3633916
  have hstable : (prefixWord ++ tailWord_3633916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633916).length < 2 ^ (prefixWord ++ tailWord_3633916).sum := by decide
  have hdescent : baseEnd_3633916 < baseStart_3633916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633922 : List Nat := [3, 4, 1, 1, 1, 4, 1, 8]
def baseStart_3633922 : Nat := 118140960795 + 3633922 * 2 ^ 59
def prefixEnd_3633922 : Nat := 4983230072969 + 3 ^ 40 * 3633922 * 2
def baseEnd_3633922 : Nat := 69109209146216166561589

theorem tailTrace_3633922 : CollatzResearch.WordTrace tailWord_3633922 prefixEnd_3633922 69109209146216166561589 := by
  unfold tailWord_3633922
  simp only [CollatzResearch.WordTrace]
  refine ⟨33135005985232173328068005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88360015960619128874848013 33135005985232173328068005)
  ·
    refine ⟨6212813622231032499012751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33135005985232173328068005 6212813622231032499012751)
    ·
      refine ⟨9319220433346548748519127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6212813622231032499012751 9319220433346548748519127)
      ·
        refine ⟨13978830650019823122778691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9319220433346548748519127 13978830650019823122778691)
        ·
          refine ⟨20968245975029734684168037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13978830650019823122778691 20968245975029734684168037)
          ·
            refine ⟨3931546120318075253281507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20968245975029734684168037 3931546120318075253281507)
            ·
              refine ⟨5897319180477112879922261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3931546120318075253281507 5897319180477112879922261)
              ·
                refine ⟨69109209146216166561589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5897319180477112879922261 69109209146216166561589)
                ·
                  rfl

theorem cell23_3633922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 8].length) (baseStart_3633922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633922 prefixEnd_3633922 := by exact prefixLift 3633922
  have htrace : WordTrace (prefixWord ++ tailWord_3633922) baseStart_3633922 baseEnd_3633922 := by
    simpa [prefixWord, tailWord_3633922, baseEnd_3633922] using wordTrace_append hprefix tailTrace_3633922
  have hstable : (prefixWord ++ tailWord_3633922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633922).length < 2 ^ (prefixWord ++ tailWord_3633922).sum := by decide
  have hdescent : baseEnd_3633922 < baseStart_3633922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3633966 : List Nat := [4, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3633966 : Nat := 118140960795 + 3633966 * 2 ^ 59
def prefixEnd_3633966 : Nat := 4983230072969 + 3 ^ 40 * 3633966 * 2
def baseEnd_3633966 : Nat := 1865971240096634325012701

theorem tailTrace_3633966 : CollatzResearch.WordTrace tailWord_3633966 prefixEnd_3633966 1865971240096634325012701 := by
  unfold tailWord_3633966
  simp only [CollatzResearch.WordTrace]
  refine ⟨16567703594096161103359219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88361085835179525884582501 16567703594096161103359219)
  ·
    refine ⟨24851555391144241655038829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16567703594096161103359219 24851555391144241655038829)
    ·
      refine ⟨9319333271679090620639561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24851555391144241655038829 9319333271679090620639561)
      ·
        refine ⟨6989499953759317965479671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9319333271679090620639561 6989499953759317965479671)
        ·
          refine ⟨10484249930638976948219507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6989499953759317965479671 10484249930638976948219507)
          ·
            refine ⟨15726374895958465422329261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10484249930638976948219507 15726374895958465422329261)
            ·
              refine ⟨5897390585984424533373473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15726374895958465422329261 5897390585984424533373473)
              ·
                refine ⟨4423042939488318400030105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5897390585984424533373473 4423042939488318400030105)
                ·
                  refine ⟨3317282204616238800022579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4423042939488318400030105 3317282204616238800022579)
                  ·
                    refine ⟨4975923306924358200033869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3317282204616238800022579 4975923306924358200033869)
                    ·
                      refine ⟨1865971240096634325012701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4975923306924358200033869 1865971240096634325012701)
                      ·
                        rfl

theorem cell23_3633966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3633966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3633966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3633966 prefixEnd_3633966 := by exact prefixLift 3633966
  have htrace : WordTrace (prefixWord ++ tailWord_3633966) baseStart_3633966 baseEnd_3633966 := by
    simpa [prefixWord, tailWord_3633966, baseEnd_3633966] using wordTrace_append hprefix tailTrace_3633966
  have hstable : (prefixWord ++ tailWord_3633966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3633966).length < 2 ^ (prefixWord ++ tailWord_3633966).sum := by decide
  have hdescent : baseEnd_3633966 < baseStart_3633966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3633966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634045 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_3634045 : Nat := 118140960795 + 3634045 * 2 ^ 59
def prefixEnd_3634045 : Nat := 4983230072969 + 3 ^ 40 * 3634045 * 2
def baseEnd_3634045 : Nat := 1866011805068339515924837

theorem tailTrace_3634045 : CollatzResearch.WordTrace tailWord_3634045 prefixEnd_3634045 1866011805068339515924837 := by
  unfold tailWord_3634045
  simp only [CollatzResearch.WordTrace]
  refine ⟨132544510119483085318999589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88363006746322056879333059 132544510119483085318999589)
  ·
    refine ⟨24852095647403078497312423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132544510119483085318999589 24852095647403078497312423)
    ·
      refine ⟨37278143471104617745968635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24852095647403078497312423 37278143471104617745968635)
      ·
        refine ⟨55917215206656926618952953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37278143471104617745968635 55917215206656926618952953)
        ·
          refine ⟨41937911404992694964214715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55917215206656926618952953 41937911404992694964214715)
          ·
            refine ⟨62906867107489042446322073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41937911404992694964214715 62906867107489042446322073)
            ·
              refine ⟨47180150330616781834741555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62906867107489042446322073 47180150330616781834741555)
              ·
                refine ⟨70770225495925172752112333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47180150330616781834741555 70770225495925172752112333)
                ·
                  refine ⟨26538834560971939782042125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70770225495925172752112333 26538834560971939782042125)
                  ·
                    refine ⟨9952062960364477418265797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26538834560971939782042125 9952062960364477418265797)
                    ·
                      refine ⟨1866011805068339515924837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9952062960364477418265797 1866011805068339515924837)
                      ·
                        rfl

theorem cell23_3634045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_3634045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634045 prefixEnd_3634045 := by exact prefixLift 3634045
  have htrace : WordTrace (prefixWord ++ tailWord_3634045) baseStart_3634045 baseEnd_3634045 := by
    simpa [prefixWord, tailWord_3634045, baseEnd_3634045] using wordTrace_append hprefix tailTrace_3634045
  have hstable : (prefixWord ++ tailWord_3634045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634045).length < 2 ^ (prefixWord ++ tailWord_3634045).sum := by decide
  have hdescent : baseEnd_3634045 < baseStart_3634045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634089 : List Nat := [1, 2, 1, 1, 1, 1, 7, 4, 1, 4]
def baseStart_3634089 : Nat := 118140960795 + 3634089 * 2 ^ 59
def prefixEnd_3634089 : Nat := 4983230072969 + 3 ^ 40 * 3634089 * 2
def baseEnd_3634089 : Nat := 622011466072379114591545

theorem tailTrace_3634089 : CollatzResearch.WordTrace tailWord_3634089 prefixEnd_3634089 622011466072379114591545 := by
  unfold tailWord_3634089
  simp only [CollatzResearch.WordTrace]
  refine ⟨132546114931323680833601321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88364076620882453889067547 132546114931323680833601321)
  ·
    refine ⟨99409586198492760625200991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132546114931323680833601321 99409586198492760625200991)
    ·
      refine ⟨149114379297739140937801487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99409586198492760625200991 149114379297739140937801487)
      ·
        refine ⟨223671568946608711406702231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149114379297739140937801487 223671568946608711406702231)
        ·
          refine ⟨335507353419913067110053347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223671568946608711406702231 335507353419913067110053347)
          ·
            refine ⟨503261030129869600665080021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335507353419913067110053347 503261030129869600665080021)
            ·
              refine ⟨11795180393668818765587813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 503261030129869600665080021 11795180393668818765587813)
              ·
                refine ⟨2211596323812903518547715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11795180393668818765587813 2211596323812903518547715)
                ·
                  refine ⟨3317394485719355277821573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211596323812903518547715 3317394485719355277821573)
                  ·
                    refine ⟨622011466072379114591545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3317394485719355277821573 622011466072379114591545)
                    ·
                      rfl

theorem cell23_3634089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 1, 4].length) (baseStart_3634089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634089 prefixEnd_3634089 := by exact prefixLift 3634089
  have htrace : WordTrace (prefixWord ++ tailWord_3634089) baseStart_3634089 baseEnd_3634089 := by
    simpa [prefixWord, tailWord_3634089, baseEnd_3634089] using wordTrace_append hprefix tailTrace_3634089
  have hstable : (prefixWord ++ tailWord_3634089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634089).length < 2 ^ (prefixWord ++ tailWord_3634089).sum := by decide
  have hdescent : baseEnd_3634089 < baseStart_3634089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634116 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3634116 : Nat := 118140960795 + 3634116 * 2 ^ 59
def prefixEnd_3634116 : Nat := 4983230072969 + 3 ^ 40 * 3634116 * 2
def baseEnd_3634116 : Nat := 1866048262194808738137011

theorem tailTrace_3634116 : CollatzResearch.WordTrace tailWord_3634116 prefixEnd_3634116 1866048262194808738137011 := by
  unfold tailWord_3634116
  simp only [CollatzResearch.WordTrace]
  refine ⟨66273549851112932222417101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88364733134817242963222801 66273549851112932222417101)
  ·
    refine ⟨24852581194167349583406413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66273549851112932222417101 24852581194167349583406413)
    ·
      refine ⟨9319717947812756093777405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24852581194167349583406413 9319717947812756093777405)
      ·
        refine ⟨3494894230429783535166527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9319717947812756093777405 3494894230429783535166527)
        ·
          refine ⟨5242341345644675302749791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3494894230429783535166527 5242341345644675302749791)
          ·
            refine ⟨7863512018467012954124687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5242341345644675302749791 7863512018467012954124687)
            ·
              refine ⟨11795268027700519431187031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7863512018467012954124687 11795268027700519431187031)
              ·
                refine ⟨17692902041550779146780547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11795268027700519431187031 17692902041550779146780547)
                ·
                  refine ⟨26539353062326168720170821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17692902041550779146780547 26539353062326168720170821)
                  ·
                    refine ⟨4976128699186156635032029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26539353062326168720170821 4976128699186156635032029)
                    ·
                      refine ⟨1866048262194808738137011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4976128699186156635032029 1866048262194808738137011)
                      ·
                        rfl

theorem cell23_3634116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3634116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634116 prefixEnd_3634116 := by exact prefixLift 3634116
  have htrace : WordTrace (prefixWord ++ tailWord_3634116) baseStart_3634116 baseEnd_3634116 := by
    simpa [prefixWord, tailWord_3634116, baseEnd_3634116] using wordTrace_append hprefix tailTrace_3634116
  have hstable : (prefixWord ++ tailWord_3634116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634116).length < 2 ^ (prefixWord ++ tailWord_3634116).sum := by decide
  have hdescent : baseEnd_3634116 < baseStart_3634116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634152 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3634152 : Nat := 118140960795 + 3634152 * 2 ^ 59
def prefixEnd_3634152 : Nat := 4983230072969 + 3 ^ 40 * 3634152 * 2
def baseEnd_3634152 : Nat := 1866066747498370597286845

theorem tailTrace_3634152 : CollatzResearch.WordTrace tailWord_3634152 prefixEnd_3634152 1866066747498370597286845 := by
  unfold tailWord_3634152
  simp only [CollatzResearch.WordTrace]
  refine ⟨66274206365047721296572355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88365608486730295062096473 66274206365047721296572355)
  ·
    refine ⟨99411309547571581944858533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66274206365047721296572355 99411309547571581944858533)
    ·
      refine ⟨18639620540169671614660975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99411309547571581944858533 18639620540169671614660975)
      ·
        refine ⟨27959430810254507421991463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18639620540169671614660975 27959430810254507421991463)
        ·
          refine ⟨41939146215381761132987195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27959430810254507421991463 41939146215381761132987195)
          ·
            refine ⟨62908719323072641699480793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41939146215381761132987195 62908719323072641699480793)
            ·
              refine ⟨47181539492304481274610595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62908719323072641699480793 47181539492304481274610595)
              ·
                refine ⟨70772309238456721911915893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47181539492304481274610595 70772309238456721911915893)
                ·
                  refine ⟨6634903991105317679242115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70772309238456721911915893 6634903991105317679242115)
                  ·
                    refine ⟨9952355986657976518863173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6634903991105317679242115 9952355986657976518863173)
                    ·
                      refine ⟨1866066747498370597286845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9952355986657976518863173 1866066747498370597286845)
                      ·
                        rfl

theorem cell23_3634152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3634152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634152 prefixEnd_3634152 := by exact prefixLift 3634152
  have htrace : WordTrace (prefixWord ++ tailWord_3634152) baseStart_3634152 baseEnd_3634152 := by
    simpa [prefixWord, tailWord_3634152, baseEnd_3634152] using wordTrace_append hprefix tailTrace_3634152
  have hstable : (prefixWord ++ tailWord_3634152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634152).length < 2 ^ (prefixWord ++ tailWord_3634152).sum := by decide
  have hdescent : baseEnd_3634152 < baseStart_3634152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634166 : List Nat := [5, 1, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_3634166 : Nat := 118140960795 + 3634166 * 2 ^ 59
def prefixEnd_3634166 : Nat := 4983230072969 + 3 ^ 40 * 3634166 * 2
def baseEnd_3634166 : Nat := 622024645409177847503927

theorem tailTrace_3634166 : CollatzResearch.WordTrace tailWord_3634166 prefixEnd_3634166 622024645409177847503927 := by
  unfold tailWord_3634166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8284307709502795186509647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88365948901363148656102901 8284307709502795186509647)
  ·
    refine ⟨12426461564254192779764471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8284307709502795186509647 12426461564254192779764471)
    ·
      refine ⟨18639692346381289169646707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12426461564254192779764471 18639692346381289169646707)
      ·
        refine ⟨27959538519571933754470061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18639692346381289169646707 27959538519571933754470061)
        ·
          refine ⟨10484826944839475157926273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27959538519571933754470061 10484826944839475157926273)
          ·
            refine ⟨7863620208629606368444705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10484826944839475157926273 7863620208629606368444705)
            ·
              refine ⟨5897715156472204776333529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7863620208629606368444705 5897715156472204776333529)
              ·
                refine ⟨4423286367354153582250147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5897715156472204776333529 4423286367354153582250147)
                ·
                  refine ⟨6634929551031230373375221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4423286367354153582250147 6634929551031230373375221)
                  ·
                    refine ⟨622024645409177847503927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6634929551031230373375221 622024645409177847503927)
                    ·
                      rfl

theorem cell23_3634166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_3634166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634166 prefixEnd_3634166 := by exact prefixLift 3634166
  have htrace : WordTrace (prefixWord ++ tailWord_3634166) baseStart_3634166 baseEnd_3634166 := by
    simpa [prefixWord, tailWord_3634166, baseEnd_3634166] using wordTrace_append hprefix tailTrace_3634166
  have hstable : (prefixWord ++ tailWord_3634166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634166).length < 2 ^ (prefixWord ++ tailWord_3634166).sum := by decide
  have hdescent : baseEnd_3634166 < baseStart_3634166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634169 : List Nat := [1, 2, 1, 3, 1, 3, 4, 2, 1, 1, 4]
def baseStart_3634169 : Nat := 118140960795 + 3634169 * 2 ^ 59
def prefixEnd_3634169 : Nat := 4983230072969 + 3 ^ 40 * 3634169 * 2
def baseEnd_3634169 : Nat := 1866075476669497030774267

theorem tailTrace_3634169 : CollatzResearch.WordTrace tailWord_3634169 prefixEnd_3634169 1866075476669497030774267 := by
  unfold tailWord_3634169
  simp only [CollatzResearch.WordTrace]
  refine ⟨132549032771033854496513561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88366021847355902997675707 132549032771033854496513561)
  ·
    refine ⟨99411774578275390872385171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132549032771033854496513561 99411774578275390872385171)
    ·
      refine ⟨149117661867413086308577757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99411774578275390872385171 149117661867413086308577757)
      ·
        refine ⟨55919123200279907365716659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149117661867413086308577757 55919123200279907365716659)
        ·
          refine ⟨83878684800419861048574989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55919123200279907365716659 83878684800419861048574989)
          ·
            refine ⟨31454506800157447893215621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83878684800419861048574989 31454506800157447893215621)
            ·
              refine ⟨5897720025029521479977929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31454506800157447893215621 5897720025029521479977929)
              ·
                refine ⟨4423290018772141109983447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5897720025029521479977929 4423290018772141109983447)
                ·
                  refine ⟨6634935028158211664975171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4423290018772141109983447 6634935028158211664975171)
                  ·
                    refine ⟨9952402542237317497462757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6634935028158211664975171 9952402542237317497462757)
                    ·
                      refine ⟨1866075476669497030774267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9952402542237317497462757 1866075476669497030774267)
                      ·
                        rfl

theorem cell23_3634169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_3634169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634169 prefixEnd_3634169 := by exact prefixLift 3634169
  have htrace : WordTrace (prefixWord ++ tailWord_3634169) baseStart_3634169 baseEnd_3634169 := by
    simpa [prefixWord, tailWord_3634169, baseEnd_3634169] using wordTrace_append hprefix tailTrace_3634169
  have hstable : (prefixWord ++ tailWord_3634169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634169).length < 2 ^ (prefixWord ++ tailWord_3634169).sum := by decide
  have hdescent : baseEnd_3634169 < baseStart_3634169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634252 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 2, 6]
def baseStart_3634252 : Nat := 118140960795 + 3634252 * 2 ^ 59
def prefixEnd_3634252 : Nat := 4983230072969 + 3 ^ 40 * 3634252 * 2
def baseEnd_3634252 : Nat := 622039365187940068678795

theorem tailTrace_3634252 : CollatzResearch.WordTrace tailWord_3634252 prefixEnd_3634252 622039365187940068678795 := by
  unfold tailWord_3634252
  simp only [CollatzResearch.WordTrace]
  refine ⟨66276030014866579835892505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88368040019822106447856673 66276030014866579835892505)
  ·
    refine ⟨49707022511149934876919379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66276030014866579835892505 49707022511149934876919379)
    ·
      refine ⟨74560533766724902315379069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49707022511149934876919379 74560533766724902315379069)
      ·
        refine ⟨27960200162521838368267151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74560533766724902315379069 27960200162521838368267151)
        ·
          refine ⟨41940300243782757552400727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27960200162521838368267151 41940300243782757552400727)
          ·
            refine ⟨62910450365674136328601091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41940300243782757552400727 62910450365674136328601091)
            ·
              refine ⟨94365675548511204492901637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62910450365674136328601091 94365675548511204492901637)
              ·
                refine ⟨17693564165345850842419057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94365675548511204492901637 17693564165345850842419057)
                ·
                  refine ⟨13270173124009388131814293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17693564165345850842419057 13270173124009388131814293)
                  ·
                    refine ⟨622039365187940068678795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13270173124009388131814293 622039365187940068678795)
                    ·
                      rfl

theorem cell23_3634252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_3634252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634252 prefixEnd_3634252 := by exact prefixLift 3634252
  have htrace : WordTrace (prefixWord ++ tailWord_3634252) baseStart_3634252 baseEnd_3634252 := by
    simpa [prefixWord, tailWord_3634252, baseEnd_3634252] using wordTrace_append hprefix tailTrace_3634252
  have hstable : (prefixWord ++ tailWord_3634252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634252).length < 2 ^ (prefixWord ++ tailWord_3634252).sum := by decide
  have hdescent : baseEnd_3634252 < baseStart_3634252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634253 : List Nat := [1, 6, 1, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_3634253 : Nat := 118140960795 + 3634253 * 2 ^ 59
def prefixEnd_3634253 : Nat := 4983230072969 + 3 ^ 40 * 3634253 * 2
def baseEnd_3634253 : Nat := 1866118609044474702123881

theorem tailTrace_3634253 : CollatzResearch.WordTrace tailWord_3634253 prefixEnd_3634253 1866118609044474702123881 := by
  unfold tailWord_3634253
  simp only [CollatzResearch.WordTrace]
  refine ⟨132552096502729536842571413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88368064335153024561714275 132552096502729536842571413)
  ·
    refine ⟨6213379523565447039495535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132552096502729536842571413 6213379523565447039495535)
    ·
      refine ⟨9320069285348170559243303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6213379523565447039495535 9320069285348170559243303)
      ·
        refine ⟨13980103928022255838864955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9320069285348170559243303 13980103928022255838864955)
        ·
          refine ⟨20970155892033383758297433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13980103928022255838864955 20970155892033383758297433)
          ·
            refine ⟨15727616919025037818723075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20970155892033383758297433 15727616919025037818723075)
            ·
              refine ⟨23591425378537556728084613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15727616919025037818723075 23591425378537556728084613)
              ·
                refine ⟨4423392258475791886515865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23591425378537556728084613 4423392258475791886515865)
                ·
                  refine ⟨3317544193856843914886899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4423392258475791886515865 3317544193856843914886899)
                  ·
                    refine ⟨4976316290785265872330349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3317544193856843914886899 4976316290785265872330349)
                    ·
                      refine ⟨1866118609044474702123881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4976316290785265872330349 1866118609044474702123881)
                      ·
                        rfl

theorem cell23_3634253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_3634253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634253 prefixEnd_3634253 := by exact prefixLift 3634253
  have htrace : WordTrace (prefixWord ++ tailWord_3634253) baseStart_3634253 baseEnd_3634253 := by
    simpa [prefixWord, tailWord_3634253, baseEnd_3634253] using wordTrace_append hprefix tailTrace_3634253
  have hstable : (prefixWord ++ tailWord_3634253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634253).length < 2 ^ (prefixWord ++ tailWord_3634253).sum := by decide
  have hdescent : baseEnd_3634253 < baseStart_3634253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634270 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_3634270 : Nat := 118140960795 + 3634270 * 2 ^ 59
def prefixEnd_3634270 : Nat := 4983230072969 + 3 ^ 40 * 3634270 * 2
def baseEnd_3634270 : Nat := 1866127338215601135611303

theorem tailTrace_3634270 : CollatzResearch.WordTrace tailWord_3634270 prefixEnd_3634270 1866127338215601135611303 := by
  unfold tailWord_3634270
  simp only [CollatzResearch.WordTrace]
  refine ⟨16569089567958493593242533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88368477695778632497293509 16569089567958493593242533)
  ·
    refine ⟨3106704293992217548732975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16569089567958493593242533 3106704293992217548732975)
    ·
      refine ⟨4660056440988326323099463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3106704293992217548732975 4660056440988326323099463)
      ·
        refine ⟨6990084661482489484649195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4660056440988326323099463 6990084661482489484649195)
        ·
          refine ⟨10485126992223734226973793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6990084661482489484649195 10485126992223734226973793)
          ·
            refine ⟨7863845244167800670230345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10485126992223734226973793 7863845244167800670230345)
            ·
              refine ⟨5897883933125850502672759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7863845244167800670230345 5897883933125850502672759)
              ·
                refine ⟨8846825899688775754009139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5897883933125850502672759 8846825899688775754009139)
                ·
                  refine ⟨13270238849533163631013709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8846825899688775754009139 13270238849533163631013709)
                  ·
                    refine ⟨4976339568574936361630141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13270238849533163631013709 4976339568574936361630141)
                    ·
                      refine ⟨1866127338215601135611303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4976339568574936361630141 1866127338215601135611303)
                      ·
                        rfl

theorem cell23_3634270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_3634270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634270 prefixEnd_3634270 := by exact prefixLift 3634270
  have htrace : WordTrace (prefixWord ++ tailWord_3634270) baseStart_3634270 baseEnd_3634270 := by
    simpa [prefixWord, tailWord_3634270, baseEnd_3634270] using wordTrace_append hprefix tailTrace_3634270
  have hstable : (prefixWord ++ tailWord_3634270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634270).length < 2 ^ (prefixWord ++ tailWord_3634270).sum := by decide
  have hdescent : baseEnd_3634270 < baseStart_3634270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634276 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 6, 2, 2]
def baseStart_3634276 : Nat := 118140960795 + 3634276 * 2 ^ 59
def prefixEnd_3634276 : Nat := 4983230072969 + 3 ^ 40 * 3634276 * 2
def baseEnd_3634276 : Nat := 1866130419099528112136275

theorem tailTrace_3634276 : CollatzResearch.WordTrace tailWord_3634276 prefixEnd_3634276 1866130419099528112136275 := by
  unfold tailWord_3634276
  simp only [CollatzResearch.WordTrace]
  refine ⟨66276467690823105885329341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88368623587764141180439121 66276467690823105885329341)
  ·
    refine ⟨24853675384058664706998503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66276467690823105885329341 24853675384058664706998503)
    ·
      refine ⟨37280513076087997060497755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24853675384058664706998503 37280513076087997060497755)
      ·
        refine ⟨55920769614131995590746633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37280513076087997060497755 55920769614131995590746633)
        ·
          refine ⟨41940577210598996693059975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55920769614131995590746633 41940577210598996693059975)
          ·
            refine ⟨62910865815898495039589963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41940577210598996693059975 62910865815898495039589963)
            ·
              refine ⟨94366298723847742559384945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62910865815898495039589963 94366298723847742559384945)
              ·
                refine ⟨70774724042885806919538709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94366298723847742559384945 70774724042885806919538709)
                ·
                  refine ⟨3317565189510272199353377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70774724042885806919538709 3317565189510272199353377)
                  ·
                    refine ⟨2488173892132704149515033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3317565189510272199353377 2488173892132704149515033)
                    ·
                      refine ⟨1866130419099528112136275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488173892132704149515033 1866130419099528112136275)
                      ·
                        rfl

theorem cell23_3634276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_3634276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634276 prefixEnd_3634276 := by exact prefixLift 3634276
  have htrace : WordTrace (prefixWord ++ tailWord_3634276) baseStart_3634276 baseEnd_3634276 := by
    simpa [prefixWord, tailWord_3634276, baseEnd_3634276] using wordTrace_append hprefix tailTrace_3634276
  have hstable : (prefixWord ++ tailWord_3634276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634276).length < 2 ^ (prefixWord ++ tailWord_3634276).sum := by decide
  have hdescent : baseEnd_3634276 < baseStart_3634276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634297 : List Nat := [1, 2, 1, 3, 6, 1, 2, 1, 1, 3, 2]
def baseStart_3634297 : Nat := 118140960795 + 3634297 * 2 ^ 59
def prefixEnd_3634297 : Nat := 4983230072969 + 3 ^ 40 * 3634297 * 2
def baseEnd_3634297 : Nat := 1866141202193272529973679

theorem tailTrace_3634297 : CollatzResearch.WordTrace tailWord_3634297 prefixEnd_3634297 1866141202193272529973679 := by
  unfold tailWord_3634297
  simp only [CollatzResearch.WordTrace]
  refine ⟨132553701314570132357173145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88369134209713421571448763 132553701314570132357173145)
  ·
    refine ⟨99415275985927599267879859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132553701314570132357173145 99415275985927599267879859)
    ·
      refine ⟨149122913978891398901819789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99415275985927599267879859 149122913978891398901819789)
      ·
        refine ⟨55921092742084274588182421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149122913978891398901819789 55921092742084274588182421)
        ·
          refine ⟨2621301222285200371321051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55921092742084274588182421 2621301222285200371321051)
          ·
            refine ⟨3931951833427800556981577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2621301222285200371321051 3931951833427800556981577)
            ·
              refine ⟨2948963875070850417736183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3931951833427800556981577 2948963875070850417736183)
              ·
                refine ⟨4423445812606275626604275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948963875070850417736183 4423445812606275626604275)
                ·
                  refine ⟨6635168718909413439906413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4423445812606275626604275 6635168718909413439906413)
                  ·
                    refine ⟨2488188269591030039964905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6635168718909413439906413 2488188269591030039964905)
                    ·
                      refine ⟨1866141202193272529973679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488188269591030039964905 1866141202193272529973679)
                      ·
                        rfl

theorem cell23_3634297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_3634297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634297 prefixEnd_3634297 := by exact prefixLift 3634297
  have htrace : WordTrace (prefixWord ++ tailWord_3634297) baseStart_3634297 baseEnd_3634297 := by
    simpa [prefixWord, tailWord_3634297, baseEnd_3634297] using wordTrace_append hprefix tailTrace_3634297
  have hstable : (prefixWord ++ tailWord_3634297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634297).length < 2 ^ (prefixWord ++ tailWord_3634297).sum := by decide
  have hdescent : baseEnd_3634297 < baseStart_3634297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634319 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 6, 5, 2]
def baseStart_3634319 : Nat := 118140960795 + 3634319 * 2 ^ 59
def prefixEnd_3634319 : Nat := 4983230072969 + 3 ^ 40 * 3634319 * 2
def baseEnd_3634319 : Nat := 1866152498767671443898577

theorem tailTrace_3634319 : CollatzResearch.WordTrace tailWord_3634319 prefixEnd_3634319 1866152498767671443898577 := by
  unfold tailWord_3634319
  simp only [CollatzResearch.WordTrace]
  refine ⟨132554503720490430114474011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88369669146993620076316007 132554503720490430114474011)
  ·
    refine ⟨198831755580735645171711017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132554503720490430114474011 198831755580735645171711017)
    ·
      refine ⟨149123816685551733878783263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198831755580735645171711017 149123816685551733878783263)
      ·
        refine ⟨223685725028327600818174895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149123816685551733878783263 223685725028327600818174895)
        ·
          refine ⟨335528587542491401227262343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223685725028327600818174895 335528587542491401227262343)
          ·
            refine ⟨503292881313737101840893515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335528587542491401227262343 503292881313737101840893515)
            ·
              refine ⟨754939321970605652761340273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503292881313737101840893515 754939321970605652761340273)
              ·
                refine ⟨566204491477954239571005205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754939321970605652761340273 566204491477954239571005205)
                ·
                  refine ⟨26540835538029104979890869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 566204491477954239571005205 26540835538029104979890869)
                  ·
                    refine ⟨2488203331690228591864769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26540835538029104979890869 2488203331690228591864769)
                    ·
                      refine ⟨1866152498767671443898577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488203331690228591864769 1866152498767671443898577)
                      ·
                        rfl

theorem cell23_3634319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 5, 2].length) (baseStart_3634319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634319 prefixEnd_3634319 := by exact prefixLift 3634319
  have htrace : WordTrace (prefixWord ++ tailWord_3634319) baseStart_3634319 baseEnd_3634319 := by
    simpa [prefixWord, tailWord_3634319, baseEnd_3634319] using wordTrace_append hprefix tailTrace_3634319
  have hstable : (prefixWord ++ tailWord_3634319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634319).length < 2 ^ (prefixWord ++ tailWord_3634319).sum := by decide
  have hdescent : baseEnd_3634319 < baseStart_3634319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634346 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3634346 : Nat := 118140960795 + 3634346 * 2 ^ 59
def prefixEnd_3634346 : Nat := 4983230072969 + 3 ^ 40 * 3634346 * 2
def baseEnd_3634346 : Nat := 622055454248447612753651

theorem tailTrace_3634346 : CollatzResearch.WordTrace tailWord_3634346 prefixEnd_3634346 622055454248447612753651 := by
  unfold tailWord_3634346
  simp only [CollatzResearch.WordTrace]
  refine ⟨33138872122848153431426723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88370325660928409150471261 33138872122848153431426723)
  ·
    refine ⟨49708308184272230147140085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33138872122848153431426723 49708308184272230147140085)
    ·
      refine ⟨4660153892275521576294383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49708308184272230147140085 4660153892275521576294383)
      ·
        refine ⟨6990230838413282364441575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4660153892275521576294383 6990230838413282364441575)
        ·
          refine ⟨10485346257619923546662363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6990230838413282364441575 10485346257619923546662363)
          ·
            refine ⟨15728019386429885319993545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10485346257619923546662363 15728019386429885319993545)
            ·
              refine ⟨11796014539822413989995159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15728019386429885319993545 11796014539822413989995159)
              ·
                refine ⟨17694021809733620984992739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11796014539822413989995159 17694021809733620984992739)
                ·
                  refine ⟨26541032714600431477489109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17694021809733620984992739 26541032714600431477489109)
                  ·
                    refine ⟨622055454248447612753651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26541032714600431477489109 622055454248447612753651)
                    ·
                      rfl

theorem cell23_3634346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3634346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634346 prefixEnd_3634346 := by exact prefixLift 3634346
  have htrace : WordTrace (prefixWord ++ tailWord_3634346) baseStart_3634346 baseEnd_3634346 := by
    simpa [prefixWord, tailWord_3634346, baseEnd_3634346] using wordTrace_append hprefix tailTrace_3634346
  have hstable : (prefixWord ++ tailWord_3634346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634346).length < 2 ^ (prefixWord ++ tailWord_3634346).sum := by decide
  have hdescent : baseEnd_3634346 < baseStart_3634346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634366 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_3634366 : Nat := 118140960795 + 3634366 * 2 ^ 59
def prefixEnd_3634366 : Nat := 4983230072969 + 3 ^ 40 * 3634366 * 2
def baseEnd_3634366 : Nat := 1866176632358432760010861

theorem tailTrace_3634366 : CollatzResearch.WordTrace tailWord_3634366 prefixEnd_3634366 1866176632358432760010861 := by
  unfold tailWord_3634366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16569527243915019642679369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88370811967546771427623301 16569527243915019642679369)
  ·
    refine ⟨12427145432936264732009527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16569527243915019642679369 12427145432936264732009527)
    ·
      refine ⟨18640718149404397098014291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12427145432936264732009527 18640718149404397098014291)
      ·
        refine ⟨27961077224106595647021437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18640718149404397098014291 27961077224106595647021437)
        ·
          refine ⟨10485403959039973367633039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27961077224106595647021437 10485403959039973367633039)
          ·
            refine ⟨15728105938559960051449559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10485403959039973367633039 15728105938559960051449559)
            ·
              refine ⟨23592158907839940077174339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15728105938559960051449559 23592158907839940077174339)
              ·
                refine ⟨35388238361759910115761509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23592158907839940077174339 35388238361759910115761509)
                ·
                  refine ⟨6635294692829983146705283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35388238361759910115761509 6635294692829983146705283)
                  ·
                    refine ⟨9952942039244974720057925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6635294692829983146705283 9952942039244974720057925)
                    ·
                      refine ⟨1866176632358432760010861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9952942039244974720057925 1866176632358432760010861)
                      ·
                        rfl

theorem cell23_3634366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_3634366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634366 prefixEnd_3634366 := by exact prefixLift 3634366
  have htrace : WordTrace (prefixWord ++ tailWord_3634366) baseStart_3634366 baseEnd_3634366 := by
    simpa [prefixWord, tailWord_3634366, baseEnd_3634366] using wordTrace_append hprefix tailTrace_3634366
  have hstable : (prefixWord ++ tailWord_3634366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634366).length < 2 ^ (prefixWord ++ tailWord_3634366).sum := by decide
  have hdescent : baseEnd_3634366 < baseStart_3634366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634376 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 3, 4]
def baseStart_3634376 : Nat := 118140960795 + 3634376 * 2 ^ 59
def prefixEnd_3634376 : Nat := 4983230072969 + 3 ^ 40 * 3634376 * 2
def baseEnd_3634376 : Nat := 622060589054992573628605

theorem tailTrace_3634376 : CollatzResearch.WordTrace tailWord_3634376 prefixEnd_3634376 622060589054992573628605 := by
  unfold tailWord_3634376
  simp only [CollatzResearch.WordTrace]
  refine ⟨66278291340641964424649491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88371055120855952566199321 66278291340641964424649491)
  ·
    refine ⟨99417437010962946636974237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66278291340641964424649491 99417437010962946636974237)
    ·
      refine ⟨37281538879111104988865339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99417437010962946636974237 37281538879111104988865339)
      ·
        refine ⟨55922308318666657483298009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37281538879111104988865339 55922308318666657483298009)
        ·
          refine ⟨41941731238999993112473507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55922308318666657483298009 41941731238999993112473507)
          ·
            refine ⟨62912596858499989668710261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41941731238999993112473507 62912596858499989668710261)
            ·
              refine ⟨5898055955484374031441587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62912596858499989668710261 5898055955484374031441587)
              ·
                refine ⟨8847083933226561047162381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898055955484374031441587 8847083933226561047162381)
                ·
                  refine ⟨3317656474959960392685893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8847083933226561047162381 3317656474959960392685893)
                  ·
                    refine ⟨622060589054992573628605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3317656474959960392685893 622060589054992573628605)
                    ·
                      rfl

theorem cell23_3634376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_3634376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634376 prefixEnd_3634376 := by exact prefixLift 3634376
  have htrace : WordTrace (prefixWord ++ tailWord_3634376) baseStart_3634376 baseEnd_3634376 := by
    simpa [prefixWord, tailWord_3634376, baseEnd_3634376] using wordTrace_append hprefix tailTrace_3634376
  have hstable : (prefixWord ++ tailWord_3634376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634376).length < 2 ^ (prefixWord ++ tailWord_3634376).sum := by decide
  have hdescent : baseEnd_3634376 < baseStart_3634376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634386 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3634386 : Nat := 118140960795 + 3634386 * 2 ^ 59
def prefixEnd_3634386 : Nat := 4983230072969 + 3 ^ 40 * 3634386 * 2
def baseEnd_3634386 : Nat := 1866186901971522681760769

theorem tailTrace_3634386 : CollatzResearch.WordTrace tailWord_3634386 prefixEnd_3634386 1866186901971522681760769 := by
  unfold tailWord_3634386
  simp only [CollatzResearch.WordTrace]
  refine ⟨33139236852811925139290753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88371298274165133704775341 33139236852811925139290753)
  ·
    refine ⟨24854427639608943854468065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33139236852811925139290753 24854427639608943854468065)
    ·
      refine ⟨18640820729706707890851049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24854427639608943854468065 18640820729706707890851049)
      ·
        refine ⟨13980615547280030918138287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18640820729706707890851049 13980615547280030918138287)
        ·
          refine ⟨20970923320920046377207431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13980615547280030918138287 20970923320920046377207431)
          ·
            refine ⟨31456384981380069565811147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20970923320920046377207431 31456384981380069565811147)
            ·
              refine ⟨47184577472070104348716721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31456384981380069565811147 47184577472070104348716721)
              ·
                refine ⟨35388433104052578261537541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47184577472070104348716721 35388433104052578261537541)
                ·
                  refine ⟨6635331207009858424038289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35388433104052578261537541 6635331207009858424038289)
                  ·
                    refine ⟨4976498405257393818028717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6635331207009858424038289 4976498405257393818028717)
                    ·
                      refine ⟨1866186901971522681760769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4976498405257393818028717 1866186901971522681760769)
                      ·
                        rfl

theorem cell23_3634386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3634386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634386 prefixEnd_3634386 := by exact prefixLift 3634386
  have htrace : WordTrace (prefixWord ++ tailWord_3634386) baseStart_3634386 baseEnd_3634386 := by
    simpa [prefixWord, tailWord_3634386, baseEnd_3634386] using wordTrace_append hprefix tailTrace_3634386
  have hstable : (prefixWord ++ tailWord_3634386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634386).length < 2 ^ (prefixWord ++ tailWord_3634386).sum := by decide
  have hdescent : baseEnd_3634386 < baseStart_3634386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634399 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 3]
def baseStart_3634399 : Nat := 118140960795 + 3634399 * 2 ^ 59
def prefixEnd_3634399 : Nat := 4983230072969 + 3 ^ 40 * 3634399 * 2
def baseEnd_3634399 : Nat := 1866193577220031130898209

theorem tailTrace_3634399 : CollatzResearch.WordTrace tailWord_3634399 prefixEnd_3634399 1866193577220031130898209 := by
  unfold tailWord_3634399
  simp only [CollatzResearch.WordTrace]
  refine ⟨132557421560200603777386251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88371614373467069184924167 132557421560200603777386251)
  ·
    refine ⟨198836132340300905666079377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132557421560200603777386251 198836132340300905666079377)
    ·
      refine ⟨149127099255225679249559533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198836132340300905666079377 149127099255225679249559533)
      ·
        refine ⟨55922662220709629718584825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149127099255225679249559533 55922662220709629718584825)
        ·
          refine ⟨41941996665532222288938619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55922662220709629718584825 41941996665532222288938619)
          ·
            refine ⟨62912994998298333433407929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41941996665532222288938619 62912994998298333433407929)
            ·
              refine ⟨47184746248723750075055947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62912994998298333433407929 47184746248723750075055947)
              ·
                refine ⟨70777119373085625112583921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47184746248723750075055947 70777119373085625112583921)
                ·
                  refine ⟨53082839529814218834437941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70777119373085625112583921 53082839529814218834437941)
                  ·
                    refine ⟨4976516205920083015728557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53082839529814218834437941 4976516205920083015728557)
                    ·
                      refine ⟨1866193577220031130898209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4976516205920083015728557 1866193577220031130898209)
                      ·
                        rfl

theorem cell23_3634399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_3634399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634399 prefixEnd_3634399 := by exact prefixLift 3634399
  have htrace : WordTrace (prefixWord ++ tailWord_3634399) baseStart_3634399 baseEnd_3634399 := by
    simpa [prefixWord, tailWord_3634399, baseEnd_3634399] using wordTrace_append hprefix tailTrace_3634399
  have hstable : (prefixWord ++ tailWord_3634399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634399).length < 2 ^ (prefixWord ++ tailWord_3634399).sum := by decide
  have hdescent : baseEnd_3634399 < baseStart_3634399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634436 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_3634436 : Nat := 118140960795 + 3634436 * 2 ^ 59
def prefixEnd_3634436 : Nat := 4983230072969 + 3 ^ 40 * 3634436 * 2
def baseEnd_3634436 : Nat := 622070858668082495378513

theorem tailTrace_3634436 : CollatzResearch.WordTrace tailWord_3634436 prefixEnd_3634436 622070858668082495378513 := by
  unfold tailWord_3634436
  simp only [CollatzResearch.WordTrace]
  refine ⟨66279385530533279548241581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88372514040711039397655441 66279385530533279548241581)
  ·
    refine ⟨24854769573949979830590593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66279385530533279548241581 24854769573949979830590593)
    ·
      refine ⟨18641077180462484872942945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24854769573949979830590593 18641077180462484872942945)
      ·
        refine ⟨13980807885346863654707209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18641077180462484872942945 13980807885346863654707209)
        ·
          refine ⟨10485605914010147741030407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13980807885346863654707209 10485605914010147741030407)
          ·
            refine ⟨15728408871015221611545611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10485605914010147741030407 15728408871015221611545611)
            ·
              refine ⟨23592613306522832417318417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15728408871015221611545611 23592613306522832417318417)
              ·
                refine ⟨17694459979892124312988813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23592613306522832417318417 17694459979892124312988813)
                ·
                  refine ⟨6635422492459546617370805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17694459979892124312988813 6635422492459546617370805)
                  ·
                    refine ⟨622070858668082495378513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6635422492459546617370805 622070858668082495378513)
                    ·
                      rfl

theorem cell23_3634436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_3634436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634436 prefixEnd_3634436 := by exact prefixLift 3634436
  have htrace : WordTrace (prefixWord ++ tailWord_3634436) baseStart_3634436 baseEnd_3634436 := by
    simpa [prefixWord, tailWord_3634436, baseEnd_3634436] using wordTrace_append hprefix tailTrace_3634436
  have hstable : (prefixWord ++ tailWord_3634436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634436).length < 2 ^ (prefixWord ++ tailWord_3634436).sum := by decide
  have hdescent : baseEnd_3634436 < baseStart_3634436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634456 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_3634456 : Nat := 118140960795 + 3634456 * 2 ^ 59
def prefixEnd_3634456 : Nat := 4983230072969 + 3 ^ 40 * 3634456 * 2
def baseEnd_3634456 : Nat := 1866222845617337407885447

theorem tailTrace_3634456 : CollatzResearch.WordTrace tailWord_3634456 prefixEnd_3634456 1866222845617337407885447 := by
  unfold tailWord_3634456
  simp only [CollatzResearch.WordTrace]
  refine ⟨66279750260497051256105611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88373000347329401674807481 66279750260497051256105611)
  ·
    refine ⟨99419625390745576884158417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66279750260497051256105611 99419625390745576884158417)
    ·
      refine ⟨74564719043059182663118813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99419625390745576884158417 74564719043059182663118813)
      ·
        refine ⟨27961769641147193498669555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74564719043059182663118813 27961769641147193498669555)
        ·
          refine ⟨41942654461720790248004333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27961769641147193498669555 41942654461720790248004333)
          ·
            refine ⟨15728495423145296343001625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41942654461720790248004333 15728495423145296343001625)
            ·
              refine ⟨11796371567358972257251219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15728495423145296343001625 11796371567358972257251219)
              ·
                refine ⟨17694557351038458385876829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11796371567358972257251219 17694557351038458385876829)
                ·
                  refine ⟨6635459006639421894703811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17694557351038458385876829 6635459006639421894703811)
                  ·
                    refine ⟨9953188509959132842055717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6635459006639421894703811 9953188509959132842055717)
                    ·
                      refine ⟨1866222845617337407885447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9953188509959132842055717 1866222845617337407885447)
                      ·
                        rfl

theorem cell23_3634456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_3634456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634456 prefixEnd_3634456 := by exact prefixLift 3634456
  have htrace : WordTrace (prefixWord ++ tailWord_3634456) baseStart_3634456 baseEnd_3634456 := by
    simpa [prefixWord, tailWord_3634456, baseEnd_3634456] using wordTrace_append hprefix tailTrace_3634456
  have hstable : (prefixWord ++ tailWord_3634456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634456).length < 2 ^ (prefixWord ++ tailWord_3634456).sum := by decide
  have hdescent : baseEnd_3634456 < baseStart_3634456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634483 : List Nat := [1, 1, 1, 2, 5, 2, 3, 2, 2, 4]
def baseStart_3634483 : Nat := 118140960795 + 3634483 * 2 ^ 59
def prefixEnd_3634483 : Nat := 4983230072969 + 3 ^ 40 * 3634483 * 2
def baseEnd_3634483 : Nat := 622078903198336267415941

theorem tailTrace_3634483 : CollatzResearch.WordTrace tailWord_3634483 prefixEnd_3634483 622078903198336267415941 := by
  unfold tailWord_3634483
  simp only [CollatzResearch.WordTrace]
  refine ⟨132560485291896286123444103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88373656861264190748962735 132560485291896286123444103)
  ·
    refine ⟨198840727937844429185166155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132560485291896286123444103 198840727937844429185166155)
    ·
      refine ⟨298261091906766643777749233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198840727937844429185166155 298261091906766643777749233)
      ·
        refine ⟨223695818930074982833311925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298261091906766643777749233 223695818930074982833311925)
        ·
          refine ⟨20971483024694529640622993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223695818930074982833311925 20971483024694529640622993)
          ·
            refine ⟨15728612268520897230467245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20971483024694529640622993 15728612268520897230467245)
            ·
              refine ⟨5898229600695336461425217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15728612268520897230467245 5898229600695336461425217)
              ·
                refine ⟨4423672200521502346068913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5898229600695336461425217 4423672200521502346068913)
                ·
                  refine ⟨3317754150391126759551685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4423672200521502346068913 3317754150391126759551685)
                  ·
                    refine ⟨622078903198336267415941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3317754150391126759551685 622078903198336267415941)
                    ·
                      rfl

theorem cell23_3634483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 4].length) (baseStart_3634483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634483 prefixEnd_3634483 := by exact prefixLift 3634483
  have htrace : WordTrace (prefixWord ++ tailWord_3634483) baseStart_3634483 baseEnd_3634483 := by
    simpa [prefixWord, tailWord_3634483, baseEnd_3634483] using wordTrace_append hprefix tailTrace_3634483
  have hstable : (prefixWord ++ tailWord_3634483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634483).length < 2 ^ (prefixWord ++ tailWord_3634483).sum := by decide
  have hdescent : baseEnd_3634483 < baseStart_3634483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634490 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2]
def baseStart_3634490 : Nat := 118140960795 + 3634490 * 2 ^ 59
def prefixEnd_3634490 : Nat := 4983230072969 + 3 ^ 40 * 3634490 * 2
def baseEnd_3634490 : Nat := 1866240303959590274860291

theorem tailTrace_3634490 : CollatzResearch.WordTrace tailWord_3634490 prefixEnd_3634490 1866240303959590274860291 := by
  unfold tailWord_3634490
  simp only [CollatzResearch.WordTrace]
  refine ⟨33140185150717731579737231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88373827068580617545965949 33140185150717731579737231)
  ·
    refine ⟨49710277726076597369605847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33140185150717731579737231 49710277726076597369605847)
    ·
      refine ⟨74565416589114896054408771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49710277726076597369605847 74565416589114896054408771)
      ·
        refine ⟨111848124883672344081613157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74565416589114896054408771 111848124883672344081613157)
        ·
          refine ⟨20971523415688564515302467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111848124883672344081613157 20971523415688564515302467)
          ·
            refine ⟨31457285123532846772953701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20971523415688564515302467 31457285123532846772953701)
            ·
              refine ⟨5898240960662408769928819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31457285123532846772953701 5898240960662408769928819)
              ·
                refine ⟨8847361440993613154893229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898240960662408769928819 8847361440993613154893229)
                ·
                  refine ⟨3317760540372604933084961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8847361440993613154893229 3317760540372604933084961)
                  ·
                    refine ⟨2488320405279453699813721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3317760540372604933084961 2488320405279453699813721)
                    ·
                      refine ⟨1866240303959590274860291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488320405279453699813721 1866240303959590274860291)
                      ·
                        rfl

theorem cell23_3634490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2].length) (baseStart_3634490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634490 prefixEnd_3634490 := by exact prefixLift 3634490
  have htrace : WordTrace (prefixWord ++ tailWord_3634490) baseStart_3634490 baseEnd_3634490 := by
    simpa [prefixWord, tailWord_3634490, baseEnd_3634490] using wordTrace_append hprefix tailTrace_3634490
  have hstable : (prefixWord ++ tailWord_3634490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634490).length < 2 ^ (prefixWord ++ tailWord_3634490).sum := by decide
  have hdescent : baseEnd_3634490 < baseStart_3634490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634500 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3634500 : Nat := 118140960795 + 3634500 * 2 ^ 59
def prefixEnd_3634500 : Nat := 4983230072969 + 3 ^ 40 * 3634500 * 2
def baseEnd_3634500 : Nat := 622081812922045078578415

theorem tailTrace_3634500 : CollatzResearch.WordTrace tailWord_3634500 prefixEnd_3634500 622081812922045078578415 := by
  unfold tailWord_3634500
  simp only [CollatzResearch.WordTrace]
  refine ⟨66280552666417349013406477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88374070221889798684541969 66280552666417349013406477)
  ·
    refine ⟨24855207249906505880027429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66280552666417349013406477 24855207249906505880027429)
    ·
      refine ⟨4660351359357469852505143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24855207249906505880027429 4660351359357469852505143)
      ·
        refine ⟨6990527039036204778757715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4660351359357469852505143 6990527039036204778757715)
        ·
          refine ⟨10485790558554307168136573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6990527039036204778757715 10485790558554307168136573)
          ·
            refine ⟨3932171459457865188051215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10485790558554307168136573 3932171459457865188051215)
            ·
              refine ⟨5898257189186797782076823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3932171459457865188051215 5898257189186797782076823)
              ·
                refine ⟨8847385783780196673115235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898257189186797782076823 8847385783780196673115235)
                ·
                  refine ⟨13271078675670295009672853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8847385783780196673115235 13271078675670295009672853)
                  ·
                    refine ⟨622081812922045078578415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13271078675670295009672853 622081812922045078578415)
                    ·
                      rfl

theorem cell23_3634500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3634500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634500 prefixEnd_3634500 := by exact prefixLift 3634500
  have htrace : WordTrace (prefixWord ++ tailWord_3634500) baseStart_3634500 baseEnd_3634500 := by
    simpa [prefixWord, tailWord_3634500, baseEnd_3634500] using wordTrace_append hprefix tailTrace_3634500
  have hstable : (prefixWord ++ tailWord_3634500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634500).length < 2 ^ (prefixWord ++ tailWord_3634500).sum := by decide
  have hdescent : baseEnd_3634500 < baseStart_3634500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634503 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_3634503 : Nat := 118140960795 + 3634503 * 2 ^ 59
def prefixEnd_3634503 : Nat := 4983230072969 + 3 ^ 40 * 3634503 * 2
def baseEnd_3634503 : Nat := 1866246979208098723997731

theorem tailTrace_3634503 : CollatzResearch.WordTrace tailWord_3634503 prefixEnd_3634503 1866246979208098723997731 := by
  unfold tailWord_3634503
  simp only [CollatzResearch.WordTrace]
  refine ⟨132561214751823829539172163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88374143167882553026114775 132561214751823829539172163)
  ·
    refine ⟨198841822127735744308758245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132561214751823829539172163 198841822127735744308758245)
    ·
      refine ⟨37282841648950452057892171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198841822127735744308758245 37282841648950452057892171)
      ·
        refine ⟨55924262473425678086838257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37282841648950452057892171 55924262473425678086838257)
        ·
          refine ⟨41943196855069258565128693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55924262473425678086838257 41943196855069258565128693)
          ·
            refine ⟨3932174705162742990480815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41943196855069258565128693 3932174705162742990480815)
            ·
              refine ⟨5898262057744114485721223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3932174705162742990480815 5898262057744114485721223)
              ·
                refine ⟨8847393086616171728581835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898262057744114485721223 8847393086616171728581835)
                ·
                  refine ⟨13271089629924257592872753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8847393086616171728581835 13271089629924257592872753)
                  ·
                    refine ⟨9953317222443193194654565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13271089629924257592872753 9953317222443193194654565)
                    ·
                      refine ⟨1866246979208098723997731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9953317222443193194654565 1866246979208098723997731)
                      ·
                        rfl

theorem cell23_3634503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_3634503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634503 prefixEnd_3634503 := by exact prefixLift 3634503
  have htrace : WordTrace (prefixWord ++ tailWord_3634503) baseStart_3634503 baseEnd_3634503 := by
    simpa [prefixWord, tailWord_3634503, baseEnd_3634503] using wordTrace_append hprefix tailTrace_3634503
  have hstable : (prefixWord ++ tailWord_3634503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634503).length < 2 ^ (prefixWord ++ tailWord_3634503).sum := by decide
  have hdescent : baseEnd_3634503 < baseStart_3634503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634529 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3634529 : Nat := 118140960795 + 3634529 * 2 ^ 59
def prefixEnd_3634529 : Nat := 4983230072969 + 3 ^ 40 * 3634529 * 2
def baseEnd_3634529 : Nat := 1866260329705115622272611

theorem tailTrace_3634529 : CollatzResearch.WordTrace tailWord_3634529 prefixEnd_3634529 1866260329705115622272611 := by
  unfold tailWord_3634529
  simp only [CollatzResearch.WordTrace]
  refine ⟨132562163049729635979618641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88374775366486423986412427 132562163049729635979618641)
  ·
    refine ⟨99421622287297226984713981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132562163049729635979618641 99421622287297226984713981)
    ·
      refine ⟨37283108357736460119267743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99421622287297226984713981 37283108357736460119267743)
      ·
        refine ⟨55924662536604690178901615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37283108357736460119267743 55924662536604690178901615)
        ·
          refine ⟨83886993804907035268352423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55924662536604690178901615 83886993804907035268352423)
          ·
            refine ⟨125830490707360552902528635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83886993804907035268352423 125830490707360552902528635)
            ·
              refine ⟨188745736061040829353792953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125830490707360552902528635 188745736061040829353792953)
              ·
                refine ⟨141559302045780622015344715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188745736061040829353792953 141559302045780622015344715)
                ·
                  refine ⟨212338953068670933023017073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141559302045780622015344715 212338953068670933023017073)
                  ·
                    refine ⟨159254214801503199767262805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212338953068670933023017073 159254214801503199767262805)
                    ·
                      refine ⟨1866260329705115622272611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 159254214801503199767262805 1866260329705115622272611)
                      ·
                        rfl

theorem cell23_3634529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3634529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634529 prefixEnd_3634529 := by exact prefixLift 3634529
  have htrace : WordTrace (prefixWord ++ tailWord_3634529) baseStart_3634529 baseEnd_3634529 := by
    simpa [prefixWord, tailWord_3634529, baseEnd_3634529] using wordTrace_append hprefix tailTrace_3634529
  have hstable : (prefixWord ++ tailWord_3634529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634529).length < 2 ^ (prefixWord ++ tailWord_3634529).sum := by decide
  have hdescent : baseEnd_3634529 < baseStart_3634529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634546 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_3634546 : Nat := 118140960795 + 3634546 * 2 ^ 59
def prefixEnd_3634546 : Nat := 4983230072969 + 3 ^ 40 * 3634546 * 2
def baseEnd_3634546 : Nat := 1866269058876242055760033

theorem tailTrace_3634546 : CollatzResearch.WordTrace tailWord_3634546 prefixEnd_3634546 1866269058876242055760033 := by
  unfold tailWord_3634546
  simp only [CollatzResearch.WordTrace]
  refine ⟨33140695772667011970746873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88375188727112031921991661 33140695772667011970746873)
  ·
    refine ⟨24855521829500258978060155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33140695772667011970746873 24855521829500258978060155)
    ·
      refine ⟨37283282744250388467090233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24855521829500258978060155 37283282744250388467090233)
      ·
        refine ⟨27962462058187791350317675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37283282744250388467090233 27962462058187791350317675)
        ·
          refine ⟨41943693087281687025476513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27962462058187791350317675 41943693087281687025476513)
          ·
            refine ⟨31457769815461265269107385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41943693087281687025476513 31457769815461265269107385)
            ·
              refine ⟨23593327361595948951830539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31457769815461265269107385 23593327361595948951830539)
              ·
                refine ⟨35389991042393923427745809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23593327361595948951830539 35389991042393923427745809)
                ·
                  refine ⟨26542493281795442570809357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35389991042393923427745809 26542493281795442570809357)
                  ·
                    refine ⟨9953434980673290964053509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26542493281795442570809357 9953434980673290964053509)
                    ·
                      refine ⟨1866269058876242055760033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9953434980673290964053509 1866269058876242055760033)
                      ·
                        rfl

theorem cell23_3634546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_3634546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634546 prefixEnd_3634546 := by exact prefixLift 3634546
  have htrace : WordTrace (prefixWord ++ tailWord_3634546) baseStart_3634546 baseEnd_3634546 := by
    simpa [prefixWord, tailWord_3634546, baseEnd_3634546] using wordTrace_append hprefix tailTrace_3634546
  have hstable : (prefixWord ++ tailWord_3634546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634546).length < 2 ^ (prefixWord ++ tailWord_3634546).sum := by decide
  have hdescent : baseEnd_3634546 < baseStart_3634546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634567 : List Nat := [1, 1, 4, 2, 2, 4, 1, 2, 1, 3, 2]
def baseStart_3634567 : Nat := 118140960795 + 3634567 * 2 ^ 59
def prefixEnd_3634567 : Nat := 4983230072969 + 3 ^ 40 * 3634567 * 2
def baseEnd_3634567 : Nat := 1866279841969986473597437

theorem tailTrace_3634567 : CollatzResearch.WordTrace tailWord_3634567 prefixEnd_3634567 1866279841969986473597437 := by
  unfold tailWord_3634567
  simp only [CollatzResearch.WordTrace]
  refine ⟨132563549023591968469501955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88375699349061312313001303 132563549023591968469501955)
  ·
    refine ⟨198845323535387952704252933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132563549023591968469501955 198845323535387952704252933)
    ·
      refine ⟨37283498162885241132047425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198845323535387952704252933 37283498162885241132047425)
      ·
        refine ⟨27962623622163930849035569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37283498162885241132047425 27962623622163930849035569)
        ·
          refine ⟨20971967716622948136776677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27962623622163930849035569 20971967716622948136776677)
          ·
            refine ⟨3932243946866802775645627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20971967716622948136776677 3932243946866802775645627)
            ·
              refine ⟨5898365920300204163468441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3932243946866802775645627 5898365920300204163468441)
              ·
                refine ⟨4423774440225153122601331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5898365920300204163468441 4423774440225153122601331)
                ·
                  refine ⟨6635661660337729683901997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4423774440225153122601331 6635661660337729683901997)
                  ·
                    refine ⟨2488373122626648631463249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6635661660337729683901997 2488373122626648631463249)
                    ·
                      refine ⟨1866279841969986473597437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488373122626648631463249 1866279841969986473597437)
                      ·
                        rfl

theorem cell23_3634567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_3634567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634567 prefixEnd_3634567 := by exact prefixLift 3634567
  have htrace : WordTrace (prefixWord ++ tailWord_3634567) baseStart_3634567 baseEnd_3634567 := by
    simpa [prefixWord, tailWord_3634567, baseEnd_3634567] using wordTrace_append hprefix tailTrace_3634567
  have hstable : (prefixWord ++ tailWord_3634567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634567).length < 2 ^ (prefixWord ++ tailWord_3634567).sum := by decide
  have hdescent : baseEnd_3634567 < baseStart_3634567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634580 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_3634580 : Nat := 118140960795 + 3634580 * 2 ^ 59
def prefixEnd_3634580 : Nat := 4983230072969 + 3 ^ 40 * 3634580 * 2
def baseEnd_3634580 : Nat := 1866286517218494922734877

theorem tailTrace_3634580 : CollatzResearch.WordTrace tailWord_3634580 prefixEnd_3634580 1866286517218494922734877 := by
  unfold tailWord_3634580
  simp only [CollatzResearch.WordTrace]
  refine ⟨66282011586272435844862597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88376015448363247793150129 66282011586272435844862597)
  ·
    refine ⟨12427877172426081720911737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66282011586272435844862597 12427877172426081720911737)
    ·
      refine ⟨9320907879319561290683803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12427877172426081720911737 9320907879319561290683803)
      ·
        refine ⟨13981361818979341936025705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9320907879319561290683803 13981361818979341936025705)
        ·
          refine ⟨10486021364234506452019279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13981361818979341936025705 10486021364234506452019279)
          ·
            refine ⟨15729032046351759678028919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10486021364234506452019279 15729032046351759678028919)
            ·
              refine ⟨23593548069527639517043379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15729032046351759678028919 23593548069527639517043379)
              ·
                refine ⟨35390322104291459275565069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23593548069527639517043379 35390322104291459275565069)
                ·
                  refine ⟨13271370789109297228336901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35390322104291459275565069 13271370789109297228336901)
                  ·
                    refine ⟨2488382022957993230313169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13271370789109297228336901 2488382022957993230313169)
                    ·
                      refine ⟨1866286517218494922734877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488382022957993230313169 1866286517218494922734877)
                      ·
                        rfl

theorem cell23_3634580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_3634580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634580 prefixEnd_3634580 := by exact prefixLift 3634580
  have htrace : WordTrace (prefixWord ++ tailWord_3634580) baseStart_3634580 baseEnd_3634580 := by
    simpa [prefixWord, tailWord_3634580, baseEnd_3634580] using wordTrace_append hprefix tailTrace_3634580
  have hstable : (prefixWord ++ tailWord_3634580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634580).length < 2 ^ (prefixWord ++ tailWord_3634580).sum := by decide
  have hdescent : baseEnd_3634580 < baseStart_3634580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634584 : List Nat := [2, 1, 2, 5, 2, 1, 3, 1, 1, 3, 2]
def baseStart_3634584 : Nat := 118140960795 + 3634584 * 2 ^ 59
def prefixEnd_3634584 : Nat := 4983230072969 + 3 ^ 40 * 3634584 * 2
def baseEnd_3634584 : Nat := 1866288571141112907084859

theorem tailTrace_3634584 : CollatzResearch.WordTrace tailWord_3634584 prefixEnd_3634584 1866288571141112907084859 := by
  unfold tailWord_3634584
  simp only [CollatzResearch.WordTrace]
  refine ⟨66282084532265190186435403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88376112709686920248580537 66282084532265190186435403)
  ·
    refine ⟨99423126798397785279653105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66282084532265190186435403 99423126798397785279653105)
    ·
      refine ⟨74567345098798338959739829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99423126798397785279653105 74567345098798338959739829)
      ·
        refine ⟨6990688603012344277475609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74567345098798338959739829 6990688603012344277475609)
        ·
          refine ⟨5243016452259258208106707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6990688603012344277475609 5243016452259258208106707)
          ·
            refine ⟨7864524678388887312160061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5243016452259258208106707 7864524678388887312160061)
            ·
              refine ⟨2949196754395832742060023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7864524678388887312160061 2949196754395832742060023)
              ·
                refine ⟨4423795131593749113090035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2949196754395832742060023 4423795131593749113090035)
                ·
                  refine ⟨6635692697390623669635053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4423795131593749113090035 6635692697390623669635053)
                  ·
                    refine ⟨2488384761521483876113145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6635692697390623669635053 2488384761521483876113145)
                    ·
                      refine ⟨1866288571141112907084859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488384761521483876113145 1866288571141112907084859)
                      ·
                        rfl

theorem cell23_3634584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_3634584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634584 prefixEnd_3634584 := by exact prefixLift 3634584
  have htrace : WordTrace (prefixWord ++ tailWord_3634584) baseStart_3634584 baseEnd_3634584 := by
    simpa [prefixWord, tailWord_3634584, baseEnd_3634584] using wordTrace_append hprefix tailTrace_3634584
  have hstable : (prefixWord ++ tailWord_3634584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634584).length < 2 ^ (prefixWord ++ tailWord_3634584).sum := by decide
  have hdescent : baseEnd_3634584 < baseStart_3634584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634613 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_3634613 : Nat := 118140960795 + 3634613 * 2 ^ 59
def prefixEnd_3634613 : Nat := 4983230072969 + 3 ^ 40 * 3634613 * 2
def baseEnd_3634613 : Nat := 1866303462080093293622225

theorem tailTrace_3634613 : CollatzResearch.WordTrace tailWord_3634613 prefixEnd_3634613 1866303462080093293622225 := by
  unfold tailWord_3634613
  simp only [CollatzResearch.WordTrace]
  refine ⟨132565226781425318325676493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88376817854283545550450995 132565226781425318325676493)
  ·
    refine ⟨49711960043034494372128685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132565226781425318325676493 49711960043034494372128685)
    ·
      refine ⟨18641985016137935389548257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49711960043034494372128685 18641985016137935389548257)
      ·
        refine ⟨13981488762103451542161193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18641985016137935389548257 13981488762103451542161193)
        ·
          refine ⟨10486116571577588656620895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13981488762103451542161193 10486116571577588656620895)
          ·
            refine ⟨15729174857366382984931343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10486116571577588656620895 15729174857366382984931343)
            ·
              refine ⟨23593762286049574477397015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15729174857366382984931343 23593762286049574477397015)
              ·
                refine ⟨35390643429074361716095523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23593762286049574477397015 35390643429074361716095523)
                ·
                  refine ⟨53085965143611542574143285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35390643429074361716095523 53085965143611542574143285)
                  ·
                    refine ⟨4976809232213582116325933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53085965143611542574143285 4976809232213582116325933)
                    ·
                      refine ⟨1866303462080093293622225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4976809232213582116325933 1866303462080093293622225)
                      ·
                        rfl

theorem cell23_3634613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_3634613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634613 prefixEnd_3634613 := by exact prefixLift 3634613
  have htrace : WordTrace (prefixWord ++ tailWord_3634613) baseStart_3634613 baseEnd_3634613 := by
    simpa [prefixWord, tailWord_3634613, baseEnd_3634613] using wordTrace_append hprefix tailTrace_3634613
  have hstable : (prefixWord ++ tailWord_3634613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634613).length < 2 ^ (prefixWord ++ tailWord_3634613).sum := by decide
  have hdescent : baseEnd_3634613 < baseStart_3634613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634616 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 4, 5]
def baseStart_3634616 : Nat := 118140960795 + 3634616 * 2 ^ 59
def prefixEnd_3634616 : Nat := 4983230072969 + 3 ^ 40 * 3634616 * 2
def baseEnd_3634616 : Nat := 622101667507352260628237

theorem tailTrace_3634616 : CollatzResearch.WordTrace tailWord_3634616 prefixEnd_3634616 622101667507352260628237 := by
  unfold tailWord_3634616
  simp only [CollatzResearch.WordTrace]
  refine ⟨66282668100207224919017851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88376890800276299892023801 66282668100207224919017851)
  ·
    refine ⟨99424002150310837378526777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66282668100207224919017851 99424002150310837378526777)
    ·
      refine ⟨74568001612733128033895083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99424002150310837378526777 74568001612733128033895083)
      ·
        refine ⟨111852002419099692050842625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74568001612733128033895083 111852002419099692050842625)
        ·
          refine ⟨83889001814324769038131969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111852002419099692050842625 83889001814324769038131969)
          ·
            refine ⟨62916751360743576778598977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83889001814324769038131969 62916751360743576778598977)
            ·
              refine ⟨47187563520557682583949233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62916751360743576778598977 47187563520557682583949233)
              ·
                refine ⟨35390672640418261937961925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47187563520557682583949233 35390672640418261937961925)
                ·
                  refine ⟨6635751120078424113367861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35390672640418261937961925 6635751120078424113367861)
                  ·
                    refine ⟨622101667507352260628237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6635751120078424113367861 622101667507352260628237)
                    ·
                      rfl

theorem cell23_3634616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_3634616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634616 prefixEnd_3634616 := by exact prefixLift 3634616
  have htrace : WordTrace (prefixWord ++ tailWord_3634616) baseStart_3634616 baseEnd_3634616 := by
    simpa [prefixWord, tailWord_3634616, baseEnd_3634616] using wordTrace_append hprefix tailTrace_3634616
  have hstable : (prefixWord ++ tailWord_3634616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634616).length < 2 ^ (prefixWord ++ tailWord_3634616).sum := by decide
  have hdescent : baseEnd_3634616 < baseStart_3634616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634670 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_3634670 : Nat := 118140960795 + 3634670 * 2 ^ 59
def prefixEnd_3634670 : Nat := 4983230072969 + 3 ^ 40 * 3634670 * 2
def baseEnd_3634670 : Nat := 1866332730477399570609463

theorem tailTrace_3634670 : CollatzResearch.WordTrace tailWord_3634670 prefixEnd_3634670 1866332730477399570609463 := by
  unfold tailWord_3634670
  simp only [CollatzResearch.WordTrace]
  refine ⟨16570913217777352132562683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88378203828145878040334309 16570913217777352132562683)
  ·
    refine ⟨24856369826666028198844025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16570913217777352132562683 24856369826666028198844025)
    ·
      refine ⟨18642277369999521149133019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24856369826666028198844025 18642277369999521149133019)
      ·
        refine ⟨27963416054999281723699529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18642277369999521149133019 27963416054999281723699529)
        ·
          refine ⟨20972562041249461292774647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27963416054999281723699529 20972562041249461292774647)
          ·
            refine ⟨31458843061874191939161971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20972562041249461292774647 31458843061874191939161971)
            ·
              refine ⟨47188264592811287908742957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31458843061874191939161971 47188264592811287908742957)
              ·
                refine ⟨17695599222304232965778609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47188264592811287908742957 17695599222304232965778609)
                ·
                  refine ⟨13271699416728174724333957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17695599222304232965778609 13271699416728174724333957)
                  ·
                    refine ⟨2488443640636532760812617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13271699416728174724333957 2488443640636532760812617)
                    ·
                      refine ⟨1866332730477399570609463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488443640636532760812617 1866332730477399570609463)
                      ·
                        rfl

theorem cell23_3634670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_3634670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634670 prefixEnd_3634670 := by exact prefixLift 3634670
  have htrace : WordTrace (prefixWord ++ tailWord_3634670) baseStart_3634670 baseEnd_3634670 := by
    simpa [prefixWord, tailWord_3634670, baseEnd_3634670] using wordTrace_append hprefix tailTrace_3634670
  have hstable : (prefixWord ++ tailWord_3634670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634670).length < 2 ^ (prefixWord ++ tailWord_3634670).sum := by decide
  have hdescent : baseEnd_3634670 < baseStart_3634670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634673 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 1, 4, 3]
def baseStart_3634673 : Nat := 118140960795 + 3634673 * 2 ^ 59
def prefixEnd_3634673 : Nat := 4983230072969 + 3 ^ 40 * 3634673 * 2
def baseEnd_3634673 : Nat := 1866334270919363058871949

theorem tailTrace_3634673 : CollatzResearch.WordTrace tailWord_3634673 prefixEnd_3634673 1866334270919363058871949 := by
  unfold tailWord_3634673
  simp only [CollatzResearch.WordTrace]
  refine ⟨132567415161207948572860673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88378276774138632381907115 132567415161207948572860673)
  ·
    refine ⟨99425561370905961429645505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132567415161207948572860673 99425561370905961429645505)
    ·
      refine ⟨74569171028179471072234129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99425561370905961429645505 74569171028179471072234129)
      ·
        refine ⟨55926878271134603304175597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74569171028179471072234129 55926878271134603304175597)
        ·
          refine ⟨20972579351675476239065849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55926878271134603304175597 20972579351675476239065849)
          ·
            refine ⟨15729434513756607179299387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20972579351675476239065849 15729434513756607179299387)
            ·
              refine ⟨23594151770634910768949081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15729434513756607179299387 23594151770634910768949081)
              ·
                refine ⟨17695613827976183076711811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23594151770634910768949081 17695613827976183076711811)
                ·
                  refine ⟨26543420741964274615067717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17695613827976183076711811 26543420741964274615067717)
                  ·
                    refine ⟨4976891389118301490325197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26543420741964274615067717 4976891389118301490325197)
                    ·
                      refine ⟨1866334270919363058871949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4976891389118301490325197 1866334270919363058871949)
                      ·
                        rfl

theorem cell23_3634673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_3634673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634673 prefixEnd_3634673 := by exact prefixLift 3634673
  have htrace : WordTrace (prefixWord ++ tailWord_3634673) baseStart_3634673 baseEnd_3634673 := by
    simpa [prefixWord, tailWord_3634673, baseEnd_3634673] using wordTrace_append hprefix tailTrace_3634673
  have hstable : (prefixWord ++ tailWord_3634673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634673).length < 2 ^ (prefixWord ++ tailWord_3634673).sum := by decide
  have hdescent : baseEnd_3634673 < baseStart_3634673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634773 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_3634773 : Nat := 118140960795 + 3634773 * 2 ^ 59
def prefixEnd_3634773 : Nat := 4983230072969 + 3 ^ 40 * 3634773 * 2
def baseEnd_3634773 : Nat := 1866385618984812667621489

theorem tailTrace_3634773 : CollatzResearch.WordTrace tailWord_3634773 prefixEnd_3634773 1866385618984812667621489 := by
  unfold tailWord_3634773
  simp only [CollatzResearch.WordTrace]
  refine ⟨132571062460845665651500973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88380708307230443767667315 132571062460845665651500973)
  ·
    refine ⟨49714148422817124619312865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132571062460845665651500973 49714148422817124619312865)
    ·
      refine ⟨37285611317112843464484649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49714148422817124619312865 37285611317112843464484649)
      ·
        refine ⟨27964208487834632598363487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37285611317112843464484649 27964208487834632598363487)
        ·
          refine ⟨41946312731751948897545231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27964208487834632598363487 41946312731751948897545231)
          ·
            refine ⟨62919469097627923346317847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41946312731751948897545231 62919469097627923346317847)
            ·
              refine ⟨94379203646441885019476771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62919469097627923346317847 94379203646441885019476771)
              ·
                refine ⟨141568805469662827529215157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94379203646441885019476771 141568805469662827529215157)
                ·
                  refine ⟨13272075512780890080863921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141568805469662827529215157 13272075512780890080863921)
                  ·
                    refine ⟨9954056634585667560647941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13272075512780890080863921 9954056634585667560647941)
                    ·
                      refine ⟨1866385618984812667621489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9954056634585667560647941 1866385618984812667621489)
                      ·
                        rfl

theorem cell23_3634773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_3634773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634773 prefixEnd_3634773 := by exact prefixLift 3634773
  have htrace : WordTrace (prefixWord ++ tailWord_3634773) baseStart_3634773 baseEnd_3634773 := by
    simpa [prefixWord, tailWord_3634773, baseEnd_3634773] using wordTrace_append hprefix tailTrace_3634773
  have hstable : (prefixWord ++ tailWord_3634773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634773).length < 2 ^ (prefixWord ++ tailWord_3634773).sum := by decide
  have hdescent : baseEnd_3634773 < baseStart_3634773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634794 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_3634794 : Nat := 118140960795 + 3634794 * 2 ^ 59
def prefixEnd_3634794 : Nat := 4983230072969 + 3 ^ 40 * 3634794 * 2
def baseEnd_3634794 : Nat := 1866396402078557085458893

theorem tailTrace_3634794 : CollatzResearch.WordTrace tailWord_3634794 prefixEnd_3634794 1866396402078557085458893 := by
  unfold tailWord_3634794
  simp only [CollatzResearch.WordTrace]
  refine ⟨33142957098442396559503859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88381218929179724158676957 33142957098442396559503859)
  ·
    refine ⟨49714435647663594839255789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33142957098442396559503859 49714435647663594839255789)
    ·
      refine ⟨18642913367873848064720921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49714435647663594839255789 18642913367873848064720921)
      ·
        refine ⟨13982185025905386048540691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18642913367873848064720921 13982185025905386048540691)
        ·
          refine ⟨20973277538858079072811037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13982185025905386048540691 20973277538858079072811037)
          ·
            refine ⟨7864979077071779652304139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20973277538858079072811037 7864979077071779652304139)
            ·
              refine ⟨11797468615607669478456209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7864979077071779652304139 11797468615607669478456209)
              ·
                refine ⟨8848101461705752108842157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11797468615607669478456209 8848101461705752108842157)
                ·
                  refine ⟨3318038048139657040815809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8848101461705752108842157 3318038048139657040815809)
                  ·
                    refine ⟨2488528536104742780611857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3318038048139657040815809 2488528536104742780611857)
                    ·
                      refine ⟨1866396402078557085458893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488528536104742780611857 1866396402078557085458893)
                      ·
                        rfl

theorem cell23_3634794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_3634794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634794 prefixEnd_3634794 := by exact prefixLift 3634794
  have htrace : WordTrace (prefixWord ++ tailWord_3634794) baseStart_3634794 baseEnd_3634794 := by
    simpa [prefixWord, tailWord_3634794, baseEnd_3634794] using wordTrace_append hprefix tailTrace_3634794
  have hstable : (prefixWord ++ tailWord_3634794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634794).length < 2 ^ (prefixWord ++ tailWord_3634794).sum := by decide
  have hdescent : baseEnd_3634794 < baseStart_3634794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634800 : List Nat := [2, 1, 1, 1, 6, 2, 3, 7]
def baseStart_3634800 : Nat := 118140960795 + 3634800 * 2 ^ 59
def prefixEnd_3634800 : Nat := 4983230072969 + 3 ^ 40 * 3634800 * 2
def baseEnd_3634800 : Nat := 69125906776388298591995

theorem tailTrace_3634800 : CollatzResearch.WordTrace tailWord_3634800 prefixEnd_3634800 69125906776388298591995 := by
  unfold tailWord_3634800
  simp only [CollatzResearch.WordTrace]
  refine ⟨66286023615873924631366927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88381364821165232841822569 66286023615873924631366927)
  ·
    refine ⟨99429035423810886947050391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66286023615873924631366927 99429035423810886947050391)
    ·
      refine ⟨149143553135716330420575587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99429035423810886947050391 149143553135716330420575587)
      ·
        refine ⟨223715329703574495630863381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149143553135716330420575587 223715329703574495630863381)
        ·
          refine ⟨10486656079855054482696721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 223715329703574495630863381 10486656079855054482696721)
          ·
            refine ⟨7864992059891290862022541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10486656079855054482696721 7864992059891290862022541)
            ·
              refine ⟨2949372022459234073258453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7864992059891290862022541 2949372022459234073258453)
              ·
                refine ⟨69125906776388298591995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2949372022459234073258453 69125906776388298591995)
                ·
                  rfl

theorem cell23_3634800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 7].length) (baseStart_3634800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634800 prefixEnd_3634800 := by exact prefixLift 3634800
  have htrace : WordTrace (prefixWord ++ tailWord_3634800) baseStart_3634800 baseEnd_3634800 := by
    simpa [prefixWord, tailWord_3634800, baseEnd_3634800] using wordTrace_append hprefix tailTrace_3634800
  have hstable : (prefixWord ++ tailWord_3634800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634800).length < 2 ^ (prefixWord ++ tailWord_3634800).sum := by decide
  have hdescent : baseEnd_3634800 < baseStart_3634800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634833 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_3634833 : Nat := 118140960795 + 3634833 * 2 ^ 59
def prefixEnd_3634833 : Nat := 4983230072969 + 3 ^ 40 * 3634833 * 2
def baseEnd_3634833 : Nat := 1866416427824082432871213

theorem tailTrace_3634833 : CollatzResearch.WordTrace tailWord_3634833 prefixEnd_3634833 1866416427824082432871213 := by
  unfold tailWord_3634833
  simp only [CollatzResearch.WordTrace]
  refine ⟨132573250840628295898685153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88382167227085530599123435 132573250840628295898685153)
  ·
    refine ⟨99429938130471221924013865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132573250840628295898685153 99429938130471221924013865)
    ·
      refine ⟨74572453597853416443010399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99429938130471221924013865 74572453597853416443010399)
      ·
        refine ⟨111858680396780124664515599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74572453597853416443010399 111858680396780124664515599)
        ·
          refine ⟨167788020595170186996773399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111858680396780124664515599 167788020595170186996773399)
          ·
            refine ⟨251682030892755280495160099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167788020595170186996773399 251682030892755280495160099)
            ·
              refine ⟨377523046339132920742740149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251682030892755280495160099 377523046339132920742740149)
              ·
                refine ⟨35392785594293711319631889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 377523046339132920742740149 35392785594293711319631889)
                ·
                  refine ⟨26544589195720283489723917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35392785594293711319631889 26544589195720283489723917)
                  ·
                    refine ⟨9954220948395106308646469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26544589195720283489723917 9954220948395106308646469)
                    ·
                      refine ⟨1866416427824082432871213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9954220948395106308646469 1866416427824082432871213)
                      ·
                        rfl

theorem cell23_3634833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_3634833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634833 prefixEnd_3634833 := by exact prefixLift 3634833
  have htrace : WordTrace (prefixWord ++ tailWord_3634833) baseStart_3634833 baseEnd_3634833 := by
    simpa [prefixWord, tailWord_3634833, baseEnd_3634833] using wordTrace_append hprefix tailTrace_3634833
  have hstable : (prefixWord ++ tailWord_3634833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634833).length < 2 ^ (prefixWord ++ tailWord_3634833).sum := by decide
  have hdescent : baseEnd_3634833 < baseStart_3634833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634844 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_3634844 : Nat := 118140960795 + 3634844 * 2 ^ 59
def prefixEnd_3634844 : Nat := 4983230072969 + 3 ^ 40 * 3634844 * 2
def baseEnd_3634844 : Nat := 1866422076111281889833663

theorem tailTrace_3634844 : CollatzResearch.WordTrace tailWord_3634844 prefixEnd_3634844 1866422076111281889833663 := by
  unfold tailWord_3634844
  simp only [CollatzResearch.WordTrace]
  refine ⟨66286826021794222388667793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88382434695725629851557057 66286826021794222388667793)
  ·
    refine ⟨49715119516345666791500845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66286826021794222388667793 49715119516345666791500845)
    ·
      refine ⟨18643169818629625046812817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49715119516345666791500845 18643169818629625046812817)
      ·
        refine ⟨13982377363972218785109613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18643169818629625046812817 13982377363972218785109613)
        ·
          refine ⟨5243391511489582044416105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13982377363972218785109613 5243391511489582044416105)
          ·
            refine ⟨3932543633617186533312079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5243391511489582044416105 3932543633617186533312079)
            ·
              refine ⟨5898815450425779799968119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3932543633617186533312079 5898815450425779799968119)
              ·
                refine ⟨8848223175638669699952179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5898815450425779799968119 8848223175638669699952179)
                ·
                  refine ⟨13272334763458004549928269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8848223175638669699952179 13272334763458004549928269)
                  ·
                    refine ⟨4977125536296751706223101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13272334763458004549928269 4977125536296751706223101)
                    ·
                      refine ⟨1866422076111281889833663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4977125536296751706223101 1866422076111281889833663)
                      ·
                        rfl

theorem cell23_3634844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_3634844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634844 prefixEnd_3634844 := by exact prefixLift 3634844
  have htrace : WordTrace (prefixWord ++ tailWord_3634844) baseStart_3634844 baseEnd_3634844 := by
    simpa [prefixWord, tailWord_3634844, baseEnd_3634844] using wordTrace_append hprefix tailTrace_3634844
  have hstable : (prefixWord ++ tailWord_3634844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634844).length < 2 ^ (prefixWord ++ tailWord_3634844).sum := by decide
  have hdescent : baseEnd_3634844 < baseStart_3634844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634862 : List Nat := [4, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_3634862 : Nat := 118140960795 + 3634862 * 2 ^ 59
def prefixEnd_3634862 : Nat := 4983230072969 + 3 ^ 40 * 3634862 * 2
def baseEnd_3634862 : Nat := 1866431318763062819408581

theorem tailTrace_3634862 : CollatzResearch.WordTrace tailWord_3634862 prefixEnd_3634862 1866431318763062819408581 := by
  unfold tailWord_3634862
  simp only [CollatzResearch.WordTrace]
  refine ⟨16571788569690404231436355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88382872371682155900993893 16571788569690404231436355)
  ·
    refine ⟨24857682854535606347154533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16571788569690404231436355 24857682854535606347154533)
    ·
      refine ⟨4660815535225426190091475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24857682854535606347154533 4660815535225426190091475)
      ·
        refine ⟨6991223302838139285137213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4660815535225426190091475 6991223302838139285137213)
        ·
          refine ⟨2621708738564302231926455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6991223302838139285137213 2621708738564302231926455)
          ·
            refine ⟨3932563107846453347889683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2621708738564302231926455 3932563107846453347889683)
            ·
              refine ⟨5898844661769680021834525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3932563107846453347889683 5898844661769680021834525)
              ·
                refine ⟨2212066748163630008187947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5898844661769680021834525 2212066748163630008187947)
                ·
                  refine ⟨3318100122245445012281921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212066748163630008187947 3318100122245445012281921)
                  ·
                    refine ⟨2488575091684083759211441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3318100122245445012281921 2488575091684083759211441)
                    ·
                      refine ⟨1866431318763062819408581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488575091684083759211441 1866431318763062819408581)
                      ·
                        rfl

theorem cell23_3634862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_3634862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634862 prefixEnd_3634862 := by exact prefixLift 3634862
  have htrace : WordTrace (prefixWord ++ tailWord_3634862) baseStart_3634862 baseEnd_3634862 := by
    simpa [prefixWord, tailWord_3634862, baseEnd_3634862] using wordTrace_append hprefix tailTrace_3634862
  have hstable : (prefixWord ++ tailWord_3634862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634862).length < 2 ^ (prefixWord ++ tailWord_3634862).sum := by decide
  have hdescent : baseEnd_3634862 < baseStart_3634862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634867 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 6, 2, 2]
def baseStart_3634867 : Nat := 118140960795 + 3634867 * 2 ^ 59
def prefixEnd_3634867 : Nat := 4983230072969 + 3 ^ 40 * 3634867 * 2
def baseEnd_3634867 : Nat := 1866433886166335299846057

theorem tailTrace_3634867 : CollatzResearch.WordTrace tailWord_3634867 prefixEnd_3634867 1866433886166335299846057 := by
  unfold tailWord_3634867
  simp only [CollatzResearch.WordTrace]
  refine ⟨132574490922505119705422855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88382993948336746470281903 132574490922505119705422855)
  ·
    refine ⟨198861736383757679558134283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132574490922505119705422855 198861736383757679558134283)
    ·
      refine ⟨298292604575636519337201425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198861736383757679558134283 298292604575636519337201425)
      ·
        refine ⟨223719453431727389502901069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298292604575636519337201425 223719453431727389502901069)
        ·
          refine ⟨83894795036897771063587901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223719453431727389502901069 83894795036897771063587901)
          ·
            refine ⟨31460548138836664148845463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83894795036897771063587901 31460548138836664148845463)
            ·
              refine ⟨47190822208254996223268195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31460548138836664148845463 47190822208254996223268195)
              ·
                refine ⟨70786233312382494334902293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47190822208254996223268195 70786233312382494334902293)
                ·
                  refine ⟨3318104686517929421948545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70786233312382494334902293 3318104686517929421948545)
                  ·
                    refine ⟨2488578514888447066461409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3318104686517929421948545 2488578514888447066461409)
                    ·
                      refine ⟨1866433886166335299846057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488578514888447066461409 1866433886166335299846057)
                      ·
                        rfl

theorem cell23_3634867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 2, 2].length) (baseStart_3634867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634867 prefixEnd_3634867 := by exact prefixLift 3634867
  have htrace : WordTrace (prefixWord ++ tailWord_3634867) baseStart_3634867 baseEnd_3634867 := by
    simpa [prefixWord, tailWord_3634867, baseEnd_3634867] using wordTrace_append hprefix tailTrace_3634867
  have hstable : (prefixWord ++ tailWord_3634867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634867).length < 2 ^ (prefixWord ++ tailWord_3634867).sum := by decide
  have hdescent : baseEnd_3634867 < baseStart_3634867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634873 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 9]
def baseStart_3634873 : Nat := 118140960795 + 3634873 * 2 ^ 59
def prefixEnd_3634873 : Nat := 4983230072969 + 3 ^ 40 * 3634873 * 2
def baseEnd_3634873 : Nat := 207381885227806919596781

theorem tailTrace_3634873 : CollatzResearch.WordTrace tailWord_3634873 prefixEnd_3634873 207381885227806919596781 := by
  unfold tailWord_3634873
  simp only [CollatzResearch.WordTrace]
  refine ⟨132574709760483382730141273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88383139840322255153427515 132574709760483382730141273)
  ·
    refine ⟨99431032320362537047605955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132574709760483382730141273 99431032320362537047605955)
    ·
      refine ⟨149146548480543805571408933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99431032320362537047605955 149146548480543805571408933)
      ·
        refine ⟨27964977840101963544639175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149146548480543805571408933 27964977840101963544639175)
        ·
          refine ⟨41947466760152945316958763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27964977840101963544639175 41947466760152945316958763)
          ·
            refine ⟨62921200140229417975438145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41947466760152945316958763 62921200140229417975438145)
            ·
              refine ⟨47190900105172063481578609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62921200140229417975438145 47190900105172063481578609)
              ·
                refine ⟨35393175078879047611183957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47190900105172063481578609 35393175078879047611183957)
                ·
                  refine ⟨207381885227806919596781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35393175078879047611183957 207381885227806919596781)
                  ·
                    rfl

theorem cell23_3634873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 9].length) (baseStart_3634873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634873 prefixEnd_3634873 := by exact prefixLift 3634873
  have htrace : WordTrace (prefixWord ++ tailWord_3634873) baseStart_3634873 baseEnd_3634873 := by
    simpa [prefixWord, tailWord_3634873, baseEnd_3634873] using wordTrace_append hprefix tailTrace_3634873
  have hstable : (prefixWord ++ tailWord_3634873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634873).length < 2 ^ (prefixWord ++ tailWord_3634873).sum := by decide
  have hdescent : baseEnd_3634873 < baseStart_3634873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634884 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_3634884 : Nat := 118140960795 + 3634884 * 2 ^ 59
def prefixEnd_3634884 : Nat := 4983230072969 + 3 ^ 40 * 3634884 * 2
def baseEnd_3634884 : Nat := 1866442615337461733333479

theorem tailTrace_3634884 : CollatzResearch.WordTrace tailWord_3634884 prefixEnd_3634884 1866442615337461733333479 := by
  unfold tailWord_3634884
  simp only [CollatzResearch.WordTrace]
  refine ⟨66287555481721765804395853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88383407308962354405861137 66287555481721765804395853)
  ·
    refine ⟨24857833305645662176648445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66287555481721765804395853 24857833305645662176648445)
    ·
      refine ⟨9321687489617123316243167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24857833305645662176648445 9321687489617123316243167)
      ·
        refine ⟨13982531234425684974364751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9321687489617123316243167 13982531234425684974364751)
        ·
          refine ⟨20973796851638527461547127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13982531234425684974364751 20973796851638527461547127)
          ·
            refine ⟨31460695277457791192320691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20973796851638527461547127 31460695277457791192320691)
            ·
              refine ⟨47191042916186686788481037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31460695277457791192320691 47191042916186686788481037)
              ·
                refine ⟨17696641093570007545680389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47191042916186686788481037 17696641093570007545680389)
                ·
                  refine ⟨3318120205044376414815073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17696641093570007545680389 3318120205044376414815073)
                  ·
                    refine ⟨2488590153783282311111305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3318120205044376414815073 2488590153783282311111305)
                    ·
                      refine ⟨1866442615337461733333479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488590153783282311111305 1866442615337461733333479)
                      ·
                        rfl

theorem cell23_3634884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_3634884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634884 prefixEnd_3634884 := by exact prefixLift 3634884
  have htrace : WordTrace (prefixWord ++ tailWord_3634884) baseStart_3634884 baseEnd_3634884 := by
    simpa [prefixWord, tailWord_3634884, baseEnd_3634884] using wordTrace_append hprefix tailTrace_3634884
  have hstable : (prefixWord ++ tailWord_3634884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634884).length < 2 ^ (prefixWord ++ tailWord_3634884).sum := by decide
  have hdescent : baseEnd_3634884 < baseStart_3634884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634930 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3634930 : Nat := 118140960795 + 3634930 * 2 ^ 59
def prefixEnd_3634930 : Nat := 4983230072969 + 3 ^ 40 * 3634930 * 2
def baseEnd_3634930 : Nat := 1866466235447568553358267

theorem tailTrace_3634930 : CollatzResearch.WordTrace tailWord_3634930 prefixEnd_3634930 1866466235447568553358267 := by
  unfold tailWord_3634930
  simp only [CollatzResearch.WordTrace]
  refine ⟨33144197180319220366241561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88384525814184587643310829 33144197180319220366241561)
  ·
    refine ⟨24858147885239415274681171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33144197180319220366241561 24858147885239415274681171)
    ·
      refine ⟨37287221827859122912021757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24858147885239415274681171 37287221827859122912021757)
      ·
        refine ⟨13982708185447171092008159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37287221827859122912021757 13982708185447171092008159)
        ·
          refine ⟨20974062278170756638012239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13982708185447171092008159 20974062278170756638012239)
          ·
            refine ⟨31461093417256134957018359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20974062278170756638012239 31461093417256134957018359)
            ·
              refine ⟨47191640125884202435527539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31461093417256134957018359 47191640125884202435527539)
              ·
                refine ⟨70787460188826303653291309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47191640125884202435527539 70787460188826303653291309)
                ·
                  refine ⟨26545297570809863869984241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70787460188826303653291309 26545297570809863869984241)
                  ·
                    refine ⟨19908973178107397902488181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26545297570809863869984241 19908973178107397902488181)
                    ·
                      refine ⟨1866466235447568553358267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19908973178107397902488181 1866466235447568553358267)
                      ·
                        rfl

theorem cell23_3634930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3634930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634930 prefixEnd_3634930 := by exact prefixLift 3634930
  have htrace : WordTrace (prefixWord ++ tailWord_3634930) baseStart_3634930 baseEnd_3634930 := by
    simpa [prefixWord, tailWord_3634930, baseEnd_3634930] using wordTrace_append hprefix tailTrace_3634930
  have hstable : (prefixWord ++ tailWord_3634930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634930).length < 2 ^ (prefixWord ++ tailWord_3634930).sum := by decide
  have hdescent : baseEnd_3634930 < baseStart_3634930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634967 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 5, 4]
def baseStart_3634967 : Nat := 118140960795 + 3634967 * 2 ^ 59
def prefixEnd_3634967 : Nat := 4983230072969 + 3 ^ 40 * 3634967 * 2
def baseEnd_3634967 : Nat := 622161744743928302865199

theorem tailTrace_3634967 : CollatzResearch.WordTrace tailWord_3634967 prefixEnd_3634967 622161744743928302865199 := by
  unfold tailWord_3634967
  simp only [CollatzResearch.WordTrace]
  refine ⟨132578138222142836784063155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88385425481428557856042103 132578138222142836784063155)
  ·
    refine ⟨198867207333214255176094733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132578138222142836784063155 198867207333214255176094733)
    ·
      refine ⟨74575202749955345691035525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198867207333214255176094733 74575202749955345691035525)
      ·
        refine ⟨13982850515616627317069161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74575202749955345691035525 13982850515616627317069161)
        ·
          refine ⟨10487137886712470487801871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13982850515616627317069161 10487137886712470487801871)
          ·
            refine ⟨15730706830068705731702807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10487137886712470487801871 15730706830068705731702807)
            ·
              refine ⟨23596060245103058597554211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15730706830068705731702807 23596060245103058597554211)
              ·
                refine ⟨35394090367654587896331317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23596060245103058597554211 35394090367654587896331317)
                ·
                  refine ⟨3318195971967617615281061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35394090367654587896331317 3318195971967617615281061)
                  ·
                    refine ⟨622161744743928302865199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3318195971967617615281061 622161744743928302865199)
                    ·
                      rfl

theorem cell23_3634967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_3634967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634967 prefixEnd_3634967 := by exact prefixLift 3634967
  have htrace : WordTrace (prefixWord ++ tailWord_3634967) baseStart_3634967 baseEnd_3634967 := by
    simpa [prefixWord, tailWord_3634967, baseEnd_3634967] using wordTrace_append hprefix tailTrace_3634967
  have hstable : (prefixWord ++ tailWord_3634967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634967).length < 2 ^ (prefixWord ++ tailWord_3634967).sum := by decide
  have hdescent : baseEnd_3634967 < baseStart_3634967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634977 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_3634977 : Nat := 118140960795 + 3634977 * 2 ^ 59
def prefixEnd_3634977 : Nat := 4983230072969 + 3 ^ 40 * 3634977 * 2
def baseEnd_3634977 : Nat := 1866490369038329869470551

theorem tailTrace_3634977 : CollatzResearch.WordTrace tailWord_3634977 prefixEnd_3634977 1866490369038329869470551 := by
  unfold tailWord_3634977
  simp only [CollatzResearch.WordTrace]
  refine ⟨132578502952106608491927185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88385668634737738994618123 132578502952106608491927185)
  ·
    refine ⟨99433877214079956368945389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132578502952106608491927185 99433877214079956368945389)
    ·
      refine ⟨37287703955279983638354521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99433877214079956368945389 37287703955279983638354521)
      ·
        refine ⟨27965777966459987728765891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37287703955279983638354521 27965777966459987728765891)
        ·
          refine ⟨41948666949689981593148837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27965777966459987728765891 41948666949689981593148837)
          ·
            refine ⟨7865375053066871548715407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41948666949689981593148837 7865375053066871548715407)
            ·
              refine ⟨11798062579600307323073111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7865375053066871548715407 11798062579600307323073111)
              ·
                refine ⟨17697093869400460984609667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11798062579600307323073111 17697093869400460984609667)
                ·
                  refine ⟨26545640804100691476914501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17697093869400460984609667 26545640804100691476914501)
                  ·
                    refine ⟨4977307650768879651921469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26545640804100691476914501 4977307650768879651921469)
                    ·
                      refine ⟨1866490369038329869470551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4977307650768879651921469 1866490369038329869470551)
                      ·
                        rfl

theorem cell23_3634977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_3634977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634977 prefixEnd_3634977 := by exact prefixLift 3634977
  have htrace : WordTrace (prefixWord ++ tailWord_3634977) baseStart_3634977 baseEnd_3634977 := by
    simpa [prefixWord, tailWord_3634977, baseEnd_3634977] using wordTrace_append hprefix tailTrace_3634977
  have hstable : (prefixWord ++ tailWord_3634977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634977).length < 2 ^ (prefixWord ++ tailWord_3634977).sum := by decide
  have hdescent : baseEnd_3634977 < baseStart_3634977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3634997 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 8]
def baseStart_3634997 : Nat := 118140960795 + 3634997 * 2 ^ 59
def prefixEnd_3634997 : Nat := 4983230072969 + 3 ^ 40 * 3634997 * 2
def baseEnd_3634997 : Nat := 207388959850157754580051

theorem tailTrace_3634997 : CollatzResearch.WordTrace tailWord_3634997 prefixEnd_3634997 207388959850157754580051 := by
  unfold tailWord_3634997
  simp only [CollatzResearch.WordTrace]
  refine ⟨132579232412034151907655245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88386154941356101271770163 132579232412034151907655245)
  ·
    refine ⟨49717212154512806965370717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132579232412034151907655245 49717212154512806965370717)
    ·
      refine ⟨18643954557942302612014019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49717212154512806965370717 18643954557942302612014019)
      ·
        refine ⟨27965931836913453918021029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18643954557942302612014019 27965931836913453918021029)
        ·
          refine ⟨5243612219421272609628943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27965931836913453918021029 5243612219421272609628943)
          ·
            refine ⟨7865418329131908914443415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5243612219421272609628943 7865418329131908914443415)
            ·
              refine ⟨11798127493697863371665123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7865418329131908914443415 11798127493697863371665123)
              ·
                refine ⟨17697191240546795057497685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11798127493697863371665123 17697191240546795057497685)
                ·
                  refine ⟨207388959850157754580051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17697191240546795057497685 207388959850157754580051)
                  ·
                    rfl

theorem cell23_3634997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_3634997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3634997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3634997 prefixEnd_3634997 := by exact prefixLift 3634997
  have htrace : WordTrace (prefixWord ++ tailWord_3634997) baseStart_3634997 baseEnd_3634997 := by
    simpa [prefixWord, tailWord_3634997, baseEnd_3634997] using wordTrace_append hprefix tailTrace_3634997
  have hstable : (prefixWord ++ tailWord_3634997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3634997).length < 2 ^ (prefixWord ++ tailWord_3634997).sum := by decide
  have hdescent : baseEnd_3634997 < baseStart_3634997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3634997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635000 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_3635000 : Nat := 118140960795 + 3635000 * 2 ^ 59
def prefixEnd_3635000 : Nat := 4983230072969 + 3 ^ 40 * 3635000 * 2
def baseEnd_3635000 : Nat := 1866502179093383279482945

theorem tailTrace_3635000 : CollatzResearch.WordTrace tailWord_3635000 prefixEnd_3635000 1866502179093383279482945 := by
  unfold tailWord_3635000
  simp only [CollatzResearch.WordTrace]
  refine ⟨66289670915511641710007227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88386227887348855613342969 66289670915511641710007227)
  ·
    refine ⟨99434506373267462565010841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66289670915511641710007227 99434506373267462565010841)
    ·
      refine ⟨74575879779950596923758131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99434506373267462565010841 74575879779950596923758131)
      ·
        refine ⟨111863819669925895385637197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74575879779950596923758131 111863819669925895385637197)
        ·
          refine ⟨41948932376222210769613949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111863819669925895385637197 41948932376222210769613949)
          ·
            refine ⟨15730849641083329038605231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41948932376222210769613949 15730849641083329038605231)
            ·
              refine ⟨23596274461624993557907847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15730849641083329038605231 23596274461624993557907847)
              ·
                refine ⟨35394411692437490336861771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23596274461624993557907847 35394411692437490336861771)
                ·
                  refine ⟨53091617538656235505292657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35394411692437490336861771 53091617538656235505292657)
                  ·
                    refine ⟨39818713153992176628969493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53091617538656235505292657 39818713153992176628969493)
                    ·
                      refine ⟨1866502179093383279482945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39818713153992176628969493 1866502179093383279482945)
                      ·
                        rfl

theorem cell23_3635000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_3635000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635000 prefixEnd_3635000 := by exact prefixLift 3635000
  have htrace : WordTrace (prefixWord ++ tailWord_3635000) baseStart_3635000 baseEnd_3635000 := by
    simpa [prefixWord, tailWord_3635000, baseEnd_3635000] using wordTrace_append hprefix tailTrace_3635000
  have hstable : (prefixWord ++ tailWord_3635000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635000).length < 2 ^ (prefixWord ++ tailWord_3635000).sum := by decide
  have hdescent : baseEnd_3635000 < baseStart_3635000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635001 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 3, 4]
def baseStart_3635001 : Nat := 118140960795 + 3635001 * 2 ^ 59
def prefixEnd_3635001 : Nat := 4983230072969 + 3 ^ 40 * 3635001 * 2
def baseEnd_3635001 : Nat := 622167564191345925190147

theorem tailTrace_3635001 : CollatzResearch.WordTrace tailWord_3635001 prefixEnd_3635001 622167564191345925190147 := by
  unfold tailWord_3635001
  simp only [CollatzResearch.WordTrace]
  refine ⟨132579378304019660590800857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88386252202679773727200571 132579378304019660590800857)
  ·
    refine ⟨99434533728014745443100643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132579378304019660590800857 99434533728014745443100643)
    ·
      refine ⟨149151800592022118164650965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99434533728014745443100643 149151800592022118164650965)
      ·
        refine ⟨3495745326375518394484007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 149151800592022118164650965 3495745326375518394484007)
        ·
          refine ⟨5243617989563277591726011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3495745326375518394484007 5243617989563277591726011)
          ·
            refine ⟨7865426984344916387589017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5243617989563277591726011 7865426984344916387589017)
            ·
              refine ⟨5899070238258687290691763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7865426984344916387589017 5899070238258687290691763)
              ·
                refine ⟨8848605357388030936037645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5899070238258687290691763 8848605357388030936037645)
                ·
                  refine ⟨3318227009020511601014117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8848605357388030936037645 3318227009020511601014117)
                  ·
                    refine ⟨622167564191345925190147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3318227009020511601014117 622167564191345925190147)
                    ·
                      rfl

theorem cell23_3635001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 4].length) (baseStart_3635001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635001 prefixEnd_3635001 := by exact prefixLift 3635001
  have htrace : WordTrace (prefixWord ++ tailWord_3635001) baseStart_3635001 baseEnd_3635001 := by
    simpa [prefixWord, tailWord_3635001, baseEnd_3635001] using wordTrace_append hprefix tailTrace_3635001
  have hstable : (prefixWord ++ tailWord_3635001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635001).length < 2 ^ (prefixWord ++ tailWord_3635001).sum := by decide
  have hdescent : baseEnd_3635001 < baseStart_3635001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635017 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 3, 5, 2]
def baseStart_3635017 : Nat := 118140960795 + 3635017 * 2 ^ 59
def prefixEnd_3635017 : Nat := 4983230072969 + 3 ^ 40 * 3635017 * 2
def baseEnd_3635017 : Nat := 1866510908264509712970367

theorem tailTrace_3635017 : CollatzResearch.WordTrace tailWord_3635017 prefixEnd_3635017 1866510908264509712970367 := by
  unfold tailWord_3635017
  simp only [CollatzResearch.WordTrace]
  refine ⟨132579961871961695323383305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88386641247974463548922203 132579961871961695323383305)
  ·
    refine ⟨99434971403971271492537479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132579961871961695323383305 99434971403971271492537479)
    ·
      refine ⟨149152457105956907238806219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99434971403971271492537479 149152457105956907238806219)
      ·
        refine ⟨223728685658935360858209329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149152457105956907238806219 223728685658935360858209329)
        ·
          refine ⟨167796514244201520643656997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223728685658935360858209329 167796514244201520643656997)
          ·
            refine ⟨31461846420787785120685687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167796514244201520643656997 31461846420787785120685687)
            ·
              refine ⟨47192769631181677681028531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31461846420787785120685687 47192769631181677681028531)
              ·
                refine ⟨70789154446772516521542797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47192769631181677681028531 70789154446772516521542797)
                ·
                  refine ⟨26545932917539693695578549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70789154446772516521542797 26545932917539693695578549)
                  ·
                    refine ⟨2488681211019346283960489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26545932917539693695578549 2488681211019346283960489)
                    ·
                      refine ⟨1866510908264509712970367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488681211019346283960489 1866510908264509712970367)
                      ·
                        rfl

theorem cell23_3635017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 5, 2].length) (baseStart_3635017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635017 prefixEnd_3635017 := by exact prefixLift 3635017
  have htrace : WordTrace (prefixWord ++ tailWord_3635017) baseStart_3635017 baseEnd_3635017 := by
    simpa [prefixWord, tailWord_3635017, baseEnd_3635017] using wordTrace_append hprefix tailTrace_3635017
  have hstable : (prefixWord ++ tailWord_3635017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635017).length < 2 ^ (prefixWord ++ tailWord_3635017).sum := by decide
  have hdescent : baseEnd_3635017 < baseStart_3635017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635034 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2]
def baseStart_3635034 : Nat := 118140960795 + 3635034 * 2 ^ 59
def prefixEnd_3635034 : Nat := 4983230072969 + 3 ^ 40 * 3635034 * 2
def baseEnd_3635034 : Nat := 1866519637435636146457789

theorem tailTrace_3635034 : CollatzResearch.WordTrace tailWord_3635034 prefixEnd_3635034 1866519637435636146457789 := by
  unfold tailWord_3635034
  simp only [CollatzResearch.WordTrace]
  refine ⟨33145145478225026806688039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88387054608600071484501437 33145145478225026806688039)
  ·
    refine ⟨49717718217337540210032059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33145145478225026806688039 49717718217337540210032059)
    ·
      refine ⟨74576577326006310315048089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49717718217337540210032059 74576577326006310315048089)
      ·
        refine ⟨55932432994504732736286067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74576577326006310315048089 55932432994504732736286067)
        ·
          refine ⟨83898649491757099104429101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55932432994504732736286067 83898649491757099104429101)
          ·
            refine ⟨31461993559408912164160913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83898649491757099104429101 31461993559408912164160913)
            ·
              refine ⟨23596495169556684123120685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31461993559408912164160913 23596495169556684123120685)
              ·
                refine ⟨8848685688583756546170257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23596495169556684123120685 8848685688583756546170257)
                ·
                  refine ⟨6636514266437817409627693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8848685688583756546170257 6636514266437817409627693)
                  ·
                    refine ⟨2488692849914181528610385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6636514266437817409627693 2488692849914181528610385)
                    ·
                      refine ⟨1866519637435636146457789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488692849914181528610385 1866519637435636146457789)
                      ·
                        rfl

theorem cell23_3635034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_3635034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635034 prefixEnd_3635034 := by exact prefixLift 3635034
  have htrace : WordTrace (prefixWord ++ tailWord_3635034) baseStart_3635034 baseEnd_3635034 := by
    simpa [prefixWord, tailWord_3635034, baseEnd_3635034] using wordTrace_append hprefix tailTrace_3635034
  have hstable : (prefixWord ++ tailWord_3635034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635034).length < 2 ^ (prefixWord ++ tailWord_3635034).sum := by decide
  have hdescent : baseEnd_3635034 < baseStart_3635034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635057 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 4, 4]
def baseStart_3635057 : Nat := 118140960795 + 3635057 * 2 ^ 59
def prefixEnd_3635057 : Nat := 4983230072969 + 3 ^ 40 * 3635057 * 2
def baseEnd_3635057 : Nat := 622177149163563185490061

theorem tailTrace_3635057 : CollatzResearch.WordTrace tailWord_3635057 prefixEnd_3635057 622177149163563185490061 := by
  unfold tailWord_3635057
  simp only [CollatzResearch.WordTrace]
  refine ⟨132581420791816782154839425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88387613861211188103226283 132581420791816782154839425)
  ·
    refine ⟨99436065593862586616129569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132581420791816782154839425 99436065593862586616129569)
    ·
      refine ⟨74577049195396939962097177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99436065593862586616129569 74577049195396939962097177)
      ·
        refine ⟨55932786896547704971572883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74577049195396939962097177 55932786896547704971572883)
        ·
          refine ⟨83899180344821557457359325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55932786896547704971572883 83899180344821557457359325)
          ·
            refine ⟨31462192629308084046509747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83899180344821557457359325 31462192629308084046509747)
            ·
              refine ⟨47193288943962126069764621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31462192629308084046509747 47193288943962126069764621)
              ·
                refine ⟨17697483353985797276161733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47193288943962126069764621 17697483353985797276161733)
                ·
                  refine ⟨3318278128872336989280325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17697483353985797276161733 3318278128872336989280325)
                  ·
                    refine ⟨622177149163563185490061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3318278128872336989280325 622177149163563185490061)
                    ·
                      rfl

theorem cell23_3635057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_3635057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635057 prefixEnd_3635057 := by exact prefixLift 3635057
  have htrace : WordTrace (prefixWord ++ tailWord_3635057) baseStart_3635057 baseEnd_3635057 := by
    simpa [prefixWord, tailWord_3635057, baseEnd_3635057] using wordTrace_append hprefix tailTrace_3635057
  have hstable : (prefixWord ++ tailWord_3635057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635057).length < 2 ^ (prefixWord ++ tailWord_3635057).sum := by decide
  have hdescent : baseEnd_3635057 < baseStart_3635057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635067 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 3]
def baseStart_3635067 : Nat := 118140960795 + 3635067 * 2 ^ 59
def prefixEnd_3635067 : Nat := 4983230072969 + 3 ^ 40 * 3635067 * 2
def baseEnd_3635067 : Nat := 1866536582297234517345137

theorem tailTrace_3635067 : CollatzResearch.WordTrace tailWord_3635067 prefixEnd_3635067 1866536582297234517345137 := by
  unfold tailWord_3635067
  simp only [CollatzResearch.WordTrace]
  refine ⟨132581785521780553862703455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88387857014520369241802303 132581785521780553862703455)
  ·
    refine ⟨198872678282670830794055183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132581785521780553862703455 198872678282670830794055183)
    ·
      refine ⟨298309017424006246191082775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198872678282670830794055183 298309017424006246191082775)
      ·
        refine ⟨447463526136009369286624163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298309017424006246191082775 447463526136009369286624163)
        ·
          refine ⟨671195289204014053929936245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447463526136009369286624163 671195289204014053929936245)
          ·
            refine ⟨62924558362876317555931523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 671195289204014053929936245 62924558362876317555931523)
            ·
              refine ⟨94386837544314476333897285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62924558362876317555931523 94386837544314476333897285)
              ·
                refine ⟨17697532039558964312605741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94386837544314476333897285 17697532039558964312605741)
                ·
                  refine ⟨6636574514834611617227153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17697532039558964312605741 6636574514834611617227153)
                  ·
                    refine ⟨4977430886125958712920365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6636574514834611617227153 4977430886125958712920365)
                    ·
                      refine ⟨1866536582297234517345137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4977430886125958712920365 1866536582297234517345137)
                      ·
                        rfl

theorem cell23_3635067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 3].length) (baseStart_3635067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635067 prefixEnd_3635067 := by exact prefixLift 3635067
  have htrace : WordTrace (prefixWord ++ tailWord_3635067) baseStart_3635067 baseEnd_3635067 := by
    simpa [prefixWord, tailWord_3635067, baseEnd_3635067] using wordTrace_append hprefix tailTrace_3635067
  have hstable : (prefixWord ++ tailWord_3635067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635067).length < 2 ^ (prefixWord ++ tailWord_3635067).sum := by decide
  have hdescent : baseEnd_3635067 < baseStart_3635067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635077 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_3635077 : Nat := 118140960795 + 3635077 * 2 ^ 59
def prefixEnd_3635077 : Nat := 4983230072969 + 3 ^ 40 * 3635077 * 2
def baseEnd_3635077 : Nat := 1866541717103779478220091

theorem tailTrace_3635077 : CollatzResearch.WordTrace tailWord_3635077 prefixEnd_3635077 1866541717103779478220091 := by
  unfold tailWord_3635077
  simp only [CollatzResearch.WordTrace]
  refine ⟨132582150251744325570567485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88388100167829550380378323 132582150251744325570567485)
  ·
    refine ⟨49718306344404122088962807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132582150251744325570567485 49718306344404122088962807)
    ·
      refine ⟨74577459516606183133444211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49718306344404122088962807 74577459516606183133444211)
      ·
        refine ⟨111866189274909274700166317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74577459516606183133444211 111866189274909274700166317)
        ·
          refine ⟨41949820978090978012562369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111866189274909274700166317 41949820978090978012562369)
          ·
            refine ⟨31462365733568233509421777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41949820978090978012562369 31462365733568233509421777)
            ·
              refine ⟨23596774300176175132066333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31462365733568233509421777 23596774300176175132066333)
              ·
                refine ⟨8848790362566065674524875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23596774300176175132066333 8848790362566065674524875)
                ·
                  refine ⟨13273185543849098511787313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8848790362566065674524875 13273185543849098511787313)
                  ·
                    refine ⟨9954889157886823883840485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13273185543849098511787313 9954889157886823883840485)
                    ·
                      refine ⟨1866541717103779478220091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9954889157886823883840485 1866541717103779478220091)
                      ·
                        rfl

theorem cell23_3635077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_3635077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635077 prefixEnd_3635077 := by exact prefixLift 3635077
  have htrace : WordTrace (prefixWord ++ tailWord_3635077) baseStart_3635077 baseEnd_3635077 := by
    simpa [prefixWord, tailWord_3635077, baseEnd_3635077] using wordTrace_append hprefix tailTrace_3635077
  have hstable : (prefixWord ++ tailWord_3635077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635077).length < 2 ^ (prefixWord ++ tailWord_3635077).sum := by decide
  have hdescent : baseEnd_3635077 < baseStart_3635077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635097 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 3, 3, 3]
def baseStart_3635097 : Nat := 118140960795 + 3635097 * 2 ^ 59
def prefixEnd_3635097 : Nat := 4983230072969 + 3 ^ 40 * 3635097 * 2
def baseEnd_3635097 : Nat := 1866551986716869399969999

theorem tailTrace_3635097 : CollatzResearch.WordTrace tailWord_3635097 prefixEnd_3635097 1866551986716869399969999 := by
  unfold tailWord_3635097
  simp only [CollatzResearch.WordTrace]
  refine ⟨132582879711671868986295545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88388586474447912657530363 132582879711671868986295545)
  ·
    refine ⟨99437159783753901739721659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132582879711671868986295545 99437159783753901739721659)
    ·
      refine ⟨149155739675630852609582489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99437159783753901739721659 149155739675630852609582489)
      ·
        refine ⟨111866804756723139457186867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149155739675630852609582489 111866804756723139457186867)
        ·
          refine ⟨167800207135084709185780301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111866804756723139457186867 167800207135084709185780301)
          ·
            refine ⟨62925077675656765944667613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167800207135084709185780301 62925077675656765944667613)
            ·
              refine ⟨23596904128371287229250355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62925077675656765944667613 23596904128371287229250355)
              ·
                refine ⟨35395356192556930843875533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23596904128371287229250355 35395356192556930843875533)
                ·
                  refine ⟨13273258572208849066453325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35395356192556930843875533 13273258572208849066453325)
                  ·
                    refine ⟨4977471964578318399919997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13273258572208849066453325 4977471964578318399919997)
                    ·
                      refine ⟨1866551986716869399969999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4977471964578318399919997 1866551986716869399969999)
                      ·
                        rfl

theorem cell23_3635097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_3635097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635097 prefixEnd_3635097 := by exact prefixLift 3635097
  have htrace : WordTrace (prefixWord ++ tailWord_3635097) baseStart_3635097 baseEnd_3635097 := by
    simpa [prefixWord, tailWord_3635097, baseEnd_3635097] using wordTrace_append hprefix tailTrace_3635097
  have hstable : (prefixWord ++ tailWord_3635097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635097).length < 2 ^ (prefixWord ++ tailWord_3635097).sum := by decide
  have hdescent : baseEnd_3635097 < baseStart_3635097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635165 : List Nat := [1, 4, 3, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_3635165 : Nat := 118140960795 + 3635165 * 2 ^ 59
def prefixEnd_3635165 : Nat := 4983230072969 + 3 ^ 40 * 3635165 * 2
def baseEnd_3635165 : Nat := 1866586903401375133919687

theorem tailTrace_3635165 : CollatzResearch.WordTrace tailWord_3635165 prefixEnd_3635165 1866586903401375133919687 := by
  unfold tailWord_3635165
  simp only [CollatzResearch.WordTrace]
  refine ⟨132585359875425516599770949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88390239916950344399847299 132585359875425516599770949)
  ·
    refine ⟨24859754976642284362457053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132585359875425516599770949 24859754976642284362457053)
    ·
      refine ⟨9322408116240856635921395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24859754976642284362457053 9322408116240856635921395)
      ·
        refine ⟨13983612174361284953882093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9322408116240856635921395 13983612174361284953882093)
        ·
          refine ⟨5243854565385481857705785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13983612174361284953882093 5243854565385481857705785)
          ·
            refine ⟨3932890924039111393279339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5243854565385481857705785 3932890924039111393279339)
            ·
              refine ⟨5899336386058667089919009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3932890924039111393279339 5899336386058667089919009)
              ·
                refine ⟨4424502289544000317439257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5899336386058667089919009 4424502289544000317439257)
                ·
                  refine ⟨3318376717158000238079443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4424502289544000317439257 3318376717158000238079443)
                  ·
                    refine ⟨4977565075737000357119165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3318376717158000238079443 4977565075737000357119165)
                    ·
                      refine ⟨1866586903401375133919687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4977565075737000357119165 1866586903401375133919687)
                      ·
                        rfl

theorem cell23_3635165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_3635165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635165 prefixEnd_3635165 := by exact prefixLift 3635165
  have htrace : WordTrace (prefixWord ++ tailWord_3635165) baseStart_3635165 baseEnd_3635165 := by
    simpa [prefixWord, tailWord_3635165, baseEnd_3635165] using wordTrace_append hprefix tailTrace_3635165
  have hstable : (prefixWord ++ tailWord_3635165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635165).length < 2 ^ (prefixWord ++ tailWord_3635165).sum := by decide
  have hdescent : baseEnd_3635165 < baseStart_3635165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635224 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 2, 5]
def baseStart_3635224 : Nat := 118140960795 + 3635224 * 2 ^ 59
def prefixEnd_3635224 : Nat := 4983230072969 + 3 ^ 40 * 3635224 * 2
def baseEnd_3635224 : Nat := 622205732919996801027305

theorem tailTrace_3635224 : CollatzResearch.WordTrace tailWord_3635224 prefixEnd_3635224 622205732919996801027305 := by
  unfold tailWord_3635224
  simp only [CollatzResearch.WordTrace]
  refine ⟨66293755891105884838084363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88391674521474513117445817 66293755891105884838084363)
  ·
    refine ⟨99440633836658827257126545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66293755891105884838084363 99440633836658827257126545)
    ·
      refine ⟨74580475377494120442844909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99440633836658827257126545 74580475377494120442844909)
      ·
        refine ⟨27967678266560295166066841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74580475377494120442844909 27967678266560295166066841)
        ·
          refine ⟨20975758699920221374550131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27967678266560295166066841 20975758699920221374550131)
          ·
            refine ⟨31463638049880332061825197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20975758699920221374550131 31463638049880332061825197)
            ·
              refine ⟨11798864268705124523184449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31463638049880332061825197 11798864268705124523184449)
              ·
                refine ⟨8849148201528843392388337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11798864268705124523184449 8849148201528843392388337)
                ·
                  refine ⟨6636861151146632544291253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8849148201528843392388337 6636861151146632544291253)
                  ·
                    refine ⟨622205732919996801027305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6636861151146632544291253 622205732919996801027305)
                    ·
                      rfl

theorem cell23_3635224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_3635224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635224 prefixEnd_3635224 := by exact prefixLift 3635224
  have htrace : WordTrace (prefixWord ++ tailWord_3635224) baseStart_3635224 baseEnd_3635224 := by
    simpa [prefixWord, tailWord_3635224, baseEnd_3635224] using wordTrace_append hprefix tailTrace_3635224
  have hstable : (prefixWord ++ tailWord_3635224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635224).length < 2 ^ (prefixWord ++ tailWord_3635224).sum := by decide
  have hdescent : baseEnd_3635224 < baseStart_3635224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635227 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 4]
def baseStart_3635227 : Nat := 118140960795 + 3635227 * 2 ^ 59
def prefixEnd_3635227 : Nat := 4983230072969 + 3 ^ 40 * 3635227 * 2
def baseEnd_3635227 : Nat := 1866618739201953891344401

theorem tailTrace_3635227 : CollatzResearch.WordTrace tailWord_3635227 prefixEnd_3635227 1866618739201953891344401 := by
  unfold tailWord_3635227
  simp only [CollatzResearch.WordTrace]
  refine ⟨132587621201200901188527935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88391747467467267459018623 132587621201200901188527935)
  ·
    refine ⟨198881431801801351782791903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132587621201200901188527935 198881431801801351782791903)
    ·
      refine ⟨298322147702702027674187855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198881431801801351782791903 298322147702702027674187855)
      ·
        refine ⟨447483221554053041511281783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298322147702702027674187855 447483221554053041511281783)
        ·
          refine ⟨671224832331079562266922675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447483221554053041511281783 671224832331079562266922675)
          ·
            refine ⟨1006837248496619343400384013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671224832331079562266922675 1006837248496619343400384013)
            ·
              refine ⟨377563968186232253775144005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1006837248496619343400384013 377563968186232253775144005)
              ·
                refine ⟨70793244034918547582839501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377563968186232253775144005 70793244034918547582839501)
                ·
                  refine ⟨26547466513094455343564813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70793244034918547582839501 26547466513094455343564813)
                  ·
                    refine ⟨9955299942410420753836805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26547466513094455343564813 9955299942410420753836805)
                    ·
                      refine ⟨1866618739201953891344401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9955299942410420753836805 1866618739201953891344401)
                      ·
                        rfl

theorem cell23_3635227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 4].length) (baseStart_3635227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635227 prefixEnd_3635227 := by exact prefixLift 3635227
  have htrace : WordTrace (prefixWord ++ tailWord_3635227) baseStart_3635227 baseEnd_3635227 := by
    simpa [prefixWord, tailWord_3635227, baseEnd_3635227] using wordTrace_append hprefix tailTrace_3635227
  have hstable : (prefixWord ++ tailWord_3635227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635227).length < 2 ^ (prefixWord ++ tailWord_3635227).sum := by decide
  have hdescent : baseEnd_3635227 < baseStart_3635227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635228 : List Nat := [2, 2, 3, 1, 3, 2, 3, 2, 5]
def baseStart_3635228 : Nat := 118140960795 + 3635228 * 2 ^ 59
def prefixEnd_3635228 : Nat := 4983230072969 + 3 ^ 40 * 3635228 * 2
def baseEnd_3635228 : Nat := 207402139186956487492433

theorem tailTrace_3635228 : CollatzResearch.WordTrace tailWord_3635228 prefixEnd_3635228 207402139186956487492433 := by
  unfold tailWord_3635228
  simp only [CollatzResearch.WordTrace]
  refine ⟨66293828837098639179657169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88391771782798185572876225 66293828837098639179657169)
  ·
    refine ⟨49720371627823979384742877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66293828837098639179657169 49720371627823979384742877)
    ·
      refine ⟨18645139360433992269278579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49720371627823979384742877 18645139360433992269278579)
      ·
        refine ⟨27967709040650988403917869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18645139360433992269278579 27967709040650988403917869)
        ·
          refine ⟨10487890890244120651469201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27967709040650988403917869 10487890890244120651469201)
          ·
            refine ⟨7865918167683090488601901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10487890890244120651469201 7865918167683090488601901)
            ·
              refine ⟨2949719312881158933225713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7865918167683090488601901 2949719312881158933225713)
              ·
                refine ⟨2212289484660869199919285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2949719312881158933225713 2212289484660869199919285)
                ·
                  refine ⟨207402139186956487492433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2212289484660869199919285 207402139186956487492433)
                  ·
                    rfl

theorem cell23_3635228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 5].length) (baseStart_3635228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635228 prefixEnd_3635228 := by exact prefixLift 3635228
  have htrace : WordTrace (prefixWord ++ tailWord_3635228) baseStart_3635228 baseEnd_3635228 := by
    simpa [prefixWord, tailWord_3635228, baseEnd_3635228] using wordTrace_append hprefix tailTrace_3635228
  have hstable : (prefixWord ++ tailWord_3635228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635228).length < 2 ^ (prefixWord ++ tailWord_3635228).sum := by decide
  have hdescent : baseEnd_3635228 < baseStart_3635228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635234 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_3635234 : Nat := 118140960795 + 3635234 * 2 ^ 59
def prefixEnd_3635234 : Nat := 4983230072969 + 3 ^ 40 * 3635234 * 2
def baseEnd_3635234 : Nat := 1866622333566535363956869

theorem tailTrace_3635234 : CollatzResearch.WordTrace tailWord_3635234 prefixEnd_3635234 1866622333566535363956869 := by
  unfold tailWord_3635234
  simp only [CollatzResearch.WordTrace]
  refine ⟨33146969128043885346008189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88391917674783694256021837 33146969128043885346008189)
  ·
    refine ⟨12430113423016457004753071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33146969128043885346008189 12430113423016457004753071)
    ·
      refine ⟨18645170134524685507129607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12430113423016457004753071 18645170134524685507129607)
      ·
        refine ⟨27967755201787028260694411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18645170134524685507129607 27967755201787028260694411)
        ·
          refine ⟨41951632802680542391041617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27967755201787028260694411 41951632802680542391041617)
          ·
            refine ⟨31463724602010406793281213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41951632802680542391041617 31463724602010406793281213)
            ·
              refine ⟨11798896725753902547480455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31463724602010406793281213 11798896725753902547480455)
              ·
                refine ⟨17698345088630853821220683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11798896725753902547480455 17698345088630853821220683)
                ·
                  refine ⟨26547517632946280731831025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17698345088630853821220683 26547517632946280731831025)
                  ·
                    refine ⟨19910638224709710548873269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26547517632946280731831025 19910638224709710548873269)
                    ·
                      refine ⟨1866622333566535363956869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19910638224709710548873269 1866622333566535363956869)
                      ·
                        rfl

theorem cell23_3635234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_3635234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635234 prefixEnd_3635234 := by exact prefixLift 3635234
  have htrace : WordTrace (prefixWord ++ tailWord_3635234) baseStart_3635234 baseEnd_3635234 := by
    simpa [prefixWord, tailWord_3635234, baseEnd_3635234] using wordTrace_append hprefix tailTrace_3635234
  have hstable : (prefixWord ++ tailWord_3635234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635234).length < 2 ^ (prefixWord ++ tailWord_3635234).sum := by decide
  have hdescent : baseEnd_3635234 < baseStart_3635234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635239 : List Nat := [1, 1, 7, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_3635239 : Nat := 118140960795 + 3635239 * 2 ^ 59
def prefixEnd_3635239 : Nat := 4983230072969 + 3 ^ 40 * 3635239 * 2
def baseEnd_3635239 : Nat := 1866624900969807844394347

theorem tailTrace_3635239 : CollatzResearch.WordTrace tailWord_3635239 prefixEnd_3635239 1866624900969807844394347 := by
  unfold tailWord_3635239
  simp only [CollatzResearch.WordTrace]
  refine ⟨132588058877157427237964771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88392039251438284825309847 132588058877157427237964771)
  ·
    refine ⟨198882088315736140856947157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132588058877157427237964771 198882088315736140856947157)
    ·
      refine ⟨4661298944900065801334699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 198882088315736140856947157 4661298944900065801334699)
      ·
        refine ⟨6991948417350098702002049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661298944900065801334699 6991948417350098702002049)
        ·
          refine ⟨5243961313012574026501537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6991948417350098702002049 5243961313012574026501537)
          ·
            refine ⟨3932970984759430519876153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5243961313012574026501537 3932970984759430519876153)
            ·
              refine ⟨2949728238569572889907115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3932970984759430519876153 2949728238569572889907115)
              ·
                refine ⟨4424592357854359334860673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2949728238569572889907115 4424592357854359334860673)
                ·
                  refine ⟨3318444268390769501145505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4424592357854359334860673 3318444268390769501145505)
                  ·
                    refine ⟨2488833201293077125859129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3318444268390769501145505 2488833201293077125859129)
                    ·
                      refine ⟨1866624900969807844394347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2488833201293077125859129 1866624900969807844394347)
                      ·
                        rfl

theorem cell23_3635239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_3635239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635239 prefixEnd_3635239 := by exact prefixLift 3635239
  have htrace : WordTrace (prefixWord ++ tailWord_3635239) baseStart_3635239 baseEnd_3635239 := by
    simpa [prefixWord, tailWord_3635239, baseEnd_3635239] using wordTrace_append hprefix tailTrace_3635239
  have hstable : (prefixWord ++ tailWord_3635239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635239).length < 2 ^ (prefixWord ++ tailWord_3635239).sum := by decide
  have hdescent : baseEnd_3635239 < baseStart_3635239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635261 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_3635261 : Nat := 118140960795 + 3635261 * 2 ^ 59
def prefixEnd_3635261 : Nat := 4983230072969 + 3 ^ 40 * 3635261 * 2
def baseEnd_3635261 : Nat := 1866636197544206758319245

theorem tailTrace_3635261 : CollatzResearch.WordTrace tailWord_3635261 prefixEnd_3635261 1866636197544206758319245 := by
  unfold tailWord_3635261
  simp only [CollatzResearch.WordTrace]
  refine ⟨132588861283077724995265637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88392574188718483330177091 132588861283077724995265637)
  ·
    refine ⟨24860411490577073436612307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132588861283077724995265637 24860411490577073436612307)
    ·
      refine ⟨37290617235865610154918461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24860411490577073436612307 37290617235865610154918461)
      ·
        refine ⟨13983981463449603808094423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37290617235865610154918461 13983981463449603808094423)
        ·
          refine ⟨20975972195174405712141635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13983981463449603808094423 20975972195174405712141635)
          ·
            refine ⟨31463958292761608568212453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20975972195174405712141635 31463958292761608568212453)
            ·
              refine ⟨5899492179892801606539835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31463958292761608568212453 5899492179892801606539835)
              ·
                refine ⟨8849238269839202409809753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5899492179892801606539835 8849238269839202409809753)
                ·
                  refine ⟨6636928702379401807357315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8849238269839202409809753 6636928702379401807357315)
                  ·
                    refine ⟨9955393053569102711035973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6636928702379401807357315 9955393053569102711035973)
                    ·
                      refine ⟨1866636197544206758319245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9955393053569102711035973 1866636197544206758319245)
                      ·
                        rfl

theorem cell23_3635261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_3635261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635261 prefixEnd_3635261 := by exact prefixLift 3635261
  have htrace : WordTrace (prefixWord ++ tailWord_3635261) baseStart_3635261 baseEnd_3635261 := by
    simpa [prefixWord, tailWord_3635261, baseEnd_3635261] using wordTrace_append hprefix tailTrace_3635261
  have hstable : (prefixWord ++ tailWord_3635261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635261).length < 2 ^ (prefixWord ++ tailWord_3635261).sum := by decide
  have hdescent : baseEnd_3635261 < baseStart_3635261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635267 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 8]
def baseStart_3635267 : Nat := 118140960795 + 3635267 * 2 ^ 59
def prefixEnd_3635267 : Nat := 4983230072969 + 3 ^ 40 * 3635267 * 2
def baseEnd_3635267 : Nat := 207404364269792637204913

theorem tailTrace_3635267 : CollatzResearch.WordTrace tailWord_3635267 prefixEnd_3635267 207404364269792637204913 := by
  unfold tailWord_3635267
  simp only [CollatzResearch.WordTrace]
  refine ⟨132589080121055988019984055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88392720080703992013322703 132589080121055988019984055)
  ·
    refine ⟨198883620181583982029976083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132589080121055988019984055 198883620181583982029976083)
    ·
      refine ⟨298325430272375973044964125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198883620181583982029976083 298325430272375973044964125)
      ·
        refine ⟨111872036352140989891861547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298325430272375973044964125 111872036352140989891861547)
        ·
          refine ⟨167808054528211484837792321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111872036352140989891861547 167808054528211484837792321)
          ·
            refine ⟨125856040896158613628344241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167808054528211484837792321 125856040896158613628344241)
            ·
              refine ⟨94392030672118960221258181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125856040896158613628344241 94392030672118960221258181)
              ·
                refine ⟨17698505751022305041485909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94392030672118960221258181 17698505751022305041485909)
                ·
                  refine ⟨207404364269792637204913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17698505751022305041485909 207404364269792637204913)
                  ·
                    rfl

theorem cell23_3635267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 8].length) (baseStart_3635267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635267 prefixEnd_3635267 := by exact prefixLift 3635267
  have htrace : WordTrace (prefixWord ++ tailWord_3635267) baseStart_3635267 baseEnd_3635267 := by
    simpa [prefixWord, tailWord_3635267, baseEnd_3635267] using wordTrace_append hprefix tailTrace_3635267
  have hstable : (prefixWord ++ tailWord_3635267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635267).length < 2 ^ (prefixWord ++ tailWord_3635267).sum := by decide
  have hdescent : baseEnd_3635267 < baseStart_3635267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635288 : List Nat := [2, 1, 2, 2, 1, 5, 1, 4, 1, 4]
def baseStart_3635288 : Nat := 118140960795 + 3635288 * 2 ^ 59
def prefixEnd_3635288 : Nat := 4983230072969 + 3 ^ 40 * 3635288 * 2
def baseEnd_3635288 : Nat := 622216687173959384227207

theorem tailTrace_3635288 : CollatzResearch.WordTrace tailWord_3635288 prefixEnd_3635288 622216687173959384227207 := by
  unfold tailWord_3635288
  simp only [CollatzResearch.WordTrace]
  refine ⟨66294923026989954303249259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88393230702653272404332345 66294923026989954303249259)
  ·
    refine ⟨99442384540484931454873889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66294923026989954303249259 99442384540484931454873889)
    ·
      refine ⟨74581788405363698591155417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99442384540484931454873889 74581788405363698591155417)
      ·
        refine ⟨55936341304022773943366563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74581788405363698591155417 55936341304022773943366563)
        ·
          refine ⟨83904511956034160915049845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55936341304022773943366563 83904511956034160915049845)
          ·
            refine ⟨7866047995878202585785923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83904511956034160915049845 7866047995878202585785923)
            ·
              refine ⟨11799071993817303878678885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7866047995878202585785923 11799071993817303878678885)
              ·
                refine ⟨2212325998840744477252291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11799071993817303878678885 2212325998840744477252291)
                ·
                  refine ⟨3318488998261116715878437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212325998840744477252291 3318488998261116715878437)
                  ·
                    refine ⟨622216687173959384227207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3318488998261116715878437 622216687173959384227207)
                    ·
                      rfl

theorem cell23_3635288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_3635288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635288 prefixEnd_3635288 := by exact prefixLift 3635288
  have htrace : WordTrace (prefixWord ++ tailWord_3635288) baseStart_3635288 baseEnd_3635288 := by
    simpa [prefixWord, tailWord_3635288, baseEnd_3635288] using wordTrace_append hprefix tailTrace_3635288
  have hstable : (prefixWord ++ tailWord_3635288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635288).length < 2 ^ (prefixWord ++ tailWord_3635288).sum := by decide
  have hdescent : baseEnd_3635288 < baseStart_3635288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635311 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 5, 1, 3]
def baseStart_3635311 : Nat := 118140960795 + 3635311 * 2 ^ 59
def prefixEnd_3635311 : Nat := 4983230072969 + 3 ^ 40 * 3635311 * 2
def baseEnd_3635311 : Nat := 1866661871576931562694015

theorem tailTrace_3635311 : CollatzResearch.WordTrace tailWord_3635311 prefixEnd_3635311 1866661871576931562694015 := by
  unfold tailWord_3635311
  simp only [CollatzResearch.WordTrace]
  refine ⟨132590684932896583534585787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88393789955264389023057191 132590684932896583534585787)
  ·
    refine ⟨198886027399344875301878681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132590684932896583534585787 198886027399344875301878681)
    ·
      refine ⟨149164520549508656476409011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198886027399344875301878681 149164520549508656476409011)
      ·
        refine ⟨223746780824262984714613517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149164520549508656476409011 223746780824262984714613517)
        ·
          refine ⟨83905042809098619267980069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223746780824262984714613517 83905042809098619267980069)
          ·
            refine ⟨15732195526705991112746263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83905042809098619267980069 15732195526705991112746263)
            ·
              refine ⟨23598293290058986669119395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15732195526705991112746263 23598293290058986669119395)
              ·
                refine ⟨35397439935088480003679093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23598293290058986669119395 35397439935088480003679093)
                ·
                  refine ⟨3318509993914545000344915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35397439935088480003679093 3318509993914545000344915)
                  ·
                    refine ⟨4977764990871817500517373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3318509993914545000344915 4977764990871817500517373)
                    ·
                      refine ⟨1866661871576931562694015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4977764990871817500517373 1866661871576931562694015)
                      ·
                        rfl

theorem cell23_3635311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 1, 3].length) (baseStart_3635311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635311 prefixEnd_3635311 := by exact prefixLift 3635311
  have htrace : WordTrace (prefixWord ++ tailWord_3635311) baseStart_3635311 baseEnd_3635311 := by
    simpa [prefixWord, tailWord_3635311, baseEnd_3635311] using wordTrace_append hprefix tailTrace_3635311
  have hstable : (prefixWord ++ tailWord_3635311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635311).length < 2 ^ (prefixWord ++ tailWord_3635311).sum := by decide
  have hdescent : baseEnd_3635311 < baseStart_3635311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635331 : List Nat := [1, 1, 1, 3, 3, 4, 1, 3, 1, 5]
def baseStart_3635331 : Nat := 118140960795 + 3635331 * 2 ^ 59
def prefixEnd_3635331 : Nat := 4983230072969 + 3 ^ 40 * 3635331 * 2
def baseEnd_3635331 : Nat := 622224047063340494814641

theorem tailTrace_3635331 : CollatzResearch.WordTrace tailWord_3635331 prefixEnd_3635331 622224047063340494814641 := by
  unfold tailWord_3635331
  simp only [CollatzResearch.WordTrace]
  refine ⟨132591414392824126950313847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88394276261882751300209231 132591414392824126950313847)
  ·
    refine ⟨198887121589236190425470771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132591414392824126950313847 198887121589236190425470771)
    ·
      refine ⟨298330682383854285638206157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198887121589236190425470771 298330682383854285638206157)
      ·
        refine ⟨111874005893945357114327309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298330682383854285638206157 111874005893945357114327309)
        ·
          refine ⟨41952752210229508917872741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111874005893945357114327309 41952752210229508917872741)
          ·
            refine ⟨7866141039418032922101139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41952752210229508917872741 7866141039418032922101139)
            ·
              refine ⟨11799211559127049383151709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7866141039418032922101139 11799211559127049383151709)
              ·
                refine ⟨4424704334672643518681891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11799211559127049383151709 4424704334672643518681891)
                ·
                  refine ⟨6637056502008965278022837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424704334672643518681891 6637056502008965278022837)
                  ·
                    refine ⟨622224047063340494814641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6637056502008965278022837 622224047063340494814641)
                    ·
                      rfl

theorem cell23_3635331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 5].length) (baseStart_3635331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635331 prefixEnd_3635331 := by exact prefixLift 3635331
  have htrace : WordTrace (prefixWord ++ tailWord_3635331) baseStart_3635331 baseEnd_3635331 := by
    simpa [prefixWord, tailWord_3635331, baseEnd_3635331] using wordTrace_append hprefix tailTrace_3635331
  have hstable : (prefixWord ++ tailWord_3635331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635331).length < 2 ^ (prefixWord ++ tailWord_3635331).sum := by decide
  have hdescent : baseEnd_3635331 < baseStart_3635331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635361 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 1, 6]
def baseStart_3635361 : Nat := 118140960795 + 3635361 * 2 ^ 59
def prefixEnd_3635361 : Nat := 4983230072969 + 3 ^ 40 * 3635361 * 2
def baseEnd_3635361 : Nat := 622229181869885455689595

theorem tailTrace_3635361 : CollatzResearch.WordTrace tailWord_3635361 prefixEnd_3635361 622229181869885455689595 := by
  unfold tailWord_3635361
  simp only [CollatzResearch.WordTrace]
  refine ⟨132592508582715442073905937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88395005721810294715937291 132592508582715442073905937)
  ·
    refine ⟨99444381437036581555429453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132592508582715442073905937 99444381437036581555429453)
    ·
      refine ⟨37291643038888718083286045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99444381437036581555429453 37291643038888718083286045)
      ·
        refine ⟨13984366139583269281232267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37291643038888718083286045 13984366139583269281232267)
        ·
          refine ⟨20976549209374903921848401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13984366139583269281232267 20976549209374903921848401)
          ·
            refine ⟨15732411907031177941386301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20976549209374903921848401 15732411907031177941386301)
            ·
              refine ⟨5899654465136691728019863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15732411907031177941386301 5899654465136691728019863)
              ·
                refine ⟨8849481697705037592029795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5899654465136691728019863 8849481697705037592029795)
                ·
                  refine ⟨13274222546557556388044693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8849481697705037592029795 13274222546557556388044693)
                  ·
                    refine ⟨622229181869885455689595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13274222546557556388044693 622229181869885455689595)
                    ·
                      rfl

theorem cell23_3635361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_3635361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635361 prefixEnd_3635361 := by exact prefixLift 3635361
  have htrace : WordTrace (prefixWord ++ tailWord_3635361) baseStart_3635361 baseEnd_3635361 := by
    simpa [prefixWord, tailWord_3635361, baseEnd_3635361] using wordTrace_append hprefix tailTrace_3635361
  have hstable : (prefixWord ++ tailWord_3635361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635361).length < 2 ^ (prefixWord ++ tailWord_3635361).sum := by decide
  have hdescent : baseEnd_3635361 < baseStart_3635361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635388 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_3635388 : Nat := 118140960795 + 3635388 * 2 ^ 59
def prefixEnd_3635388 : Nat := 4983230072969 + 3 ^ 40 * 3635388 * 2
def baseEnd_3635388 : Nat := 1866701409587327761431161

theorem tailTrace_3635388 : CollatzResearch.WordTrace tailWord_3635388 prefixEnd_3635388 1866701409587327761431161 := by
  unfold tailWord_3635388
  simp only [CollatzResearch.WordTrace]
  refine ⟨66296746676808812842569409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88395662235745083790092545 66296746676808812842569409)
  ·
    refine ⟨49722560007606609631927057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66296746676808812842569409 49722560007606609631927057)
    ·
      refine ⟨37291920005704957223945293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49722560007606609631927057 37291920005704957223945293)
      ·
        refine ⟨13984470002139358958979485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37291920005704957223945293 13984470002139358958979485)
        ·
          refine ⟨5244176250802259609617307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13984470002139358958979485 5244176250802259609617307)
          ·
            refine ⟨7866264376203389414425961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5244176250802259609617307 7866264376203389414425961)
            ·
              refine ⟨5899698282152542060819471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7866264376203389414425961 5899698282152542060819471)
              ·
                refine ⟨8849547423228813091229207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5899698282152542060819471 8849547423228813091229207)
                ·
                  refine ⟨13274321134843219636843811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8849547423228813091229207 13274321134843219636843811)
                  ·
                    refine ⟨19911481702264829455265717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13274321134843219636843811 19911481702264829455265717)
                    ·
                      refine ⟨1866701409587327761431161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19911481702264829455265717 1866701409587327761431161)
                      ·
                        rfl

theorem cell23_3635388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_3635388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635388 prefixEnd_3635388 := by exact prefixLift 3635388
  have htrace : WordTrace (prefixWord ++ tailWord_3635388) baseStart_3635388 baseEnd_3635388 := by
    simpa [prefixWord, tailWord_3635388, baseEnd_3635388] using wordTrace_append hprefix tailTrace_3635388
  have hstable : (prefixWord ++ tailWord_3635388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635388).length < 2 ^ (prefixWord ++ tailWord_3635388).sum := by decide
  have hdescent : baseEnd_3635388 < baseStart_3635388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635458 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3635458 : Nat := 118140960795 + 3635458 * 2 ^ 59
def prefixEnd_3635458 : Nat := 4983230072969 + 3 ^ 40 * 3635458 * 2
def baseEnd_3635458 : Nat := 1866737353233142487555839

theorem tailTrace_3635458 : CollatzResearch.WordTrace tailWord_3635458 prefixEnd_3635458 1866737353233142487555839 := by
  unfold tailWord_3635458
  simp only [CollatzResearch.WordTrace]
  refine ⟨33149011615841006910046757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88397364308909351760124685 33149011615841006910046757)
  ·
    refine ⟨6215439677970188795633767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33149011615841006910046757 6215439677970188795633767)
    ·
      refine ⟨9323159516955283193450651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6215439677970188795633767 9323159516955283193450651)
      ·
        refine ⟨13984739275432924790175977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9323159516955283193450651 13984739275432924790175977)
        ·
          refine ⟨10488554456574693592631983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13984739275432924790175977 10488554456574693592631983)
          ·
            refine ⟨15732831684862040388947975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10488554456574693592631983 15732831684862040388947975)
            ·
              refine ⟨23599247527293060583421963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15732831684862040388947975 23599247527293060583421963)
              ·
                refine ⟨35398871290939590875132945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23599247527293060583421963 35398871290939590875132945)
                ·
                  refine ⟨26549153468204693156349709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35398871290939590875132945 26549153468204693156349709)
                  ·
                    refine ⟨9955932550576759933631141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26549153468204693156349709 9955932550576759933631141)
                    ·
                      refine ⟨1866737353233142487555839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9955932550576759933631141 1866737353233142487555839)
                      ·
                        rfl

theorem cell23_3635458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3635458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635458 prefixEnd_3635458 := by exact prefixLift 3635458
  have htrace : WordTrace (prefixWord ++ tailWord_3635458) baseStart_3635458 baseEnd_3635458 := by
    simpa [prefixWord, tailWord_3635458, baseEnd_3635458] using wordTrace_append hprefix tailTrace_3635458
  have hstable : (prefixWord ++ tailWord_3635458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635458).length < 2 ^ (prefixWord ++ tailWord_3635458).sum := by decide
  have hdescent : baseEnd_3635458 < baseStart_3635458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635491 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 3]
def baseStart_3635491 : Nat := 118140960795 + 3635491 * 2 ^ 59
def prefixEnd_3635491 : Nat := 4983230072969 + 3 ^ 40 * 3635491 * 2
def baseEnd_3635491 : Nat := 1866754298094740858443187

theorem tailTrace_3635491 : CollatzResearch.WordTrace tailWord_3635491 prefixEnd_3635491 1866754298094740858443187 := by
  unfold tailWord_3635491
  simp only [CollatzResearch.WordTrace]
  refine ⟨132597250072244474276138327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88398166714829649517425551 132597250072244474276138327)
  ·
    refine ⟨198895875108366711414207491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132597250072244474276138327 198895875108366711414207491)
    ·
      refine ⟨298343812662550067121311237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198895875108366711414207491 298343812662550067121311237)
      ·
        refine ⟨55939464874228137585245857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298343812662550067121311237 55939464874228137585245857)
        ·
          refine ⟨41954598655671103188934393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55939464874228137585245857 41954598655671103188934393)
          ·
            refine ⟨31465948991753327391700795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41954598655671103188934393 31465948991753327391700795)
            ·
              refine ⟨47198923487629991087551193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31465948991753327391700795 47198923487629991087551193)
              ·
                refine ⟨35399192615722493315663395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47198923487629991087551193 35399192615722493315663395)
                ·
                  refine ⟨53098788923583739973495093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35399192615722493315663395 53098788923583739973495093)
                  ·
                    refine ⟨4978011461585975622515165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53098788923583739973495093 4978011461585975622515165)
                    ·
                      refine ⟨1866754298094740858443187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4978011461585975622515165 1866754298094740858443187)
                      ·
                        rfl

theorem cell23_3635491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_3635491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635491 prefixEnd_3635491 := by exact prefixLift 3635491
  have htrace : WordTrace (prefixWord ++ tailWord_3635491) baseStart_3635491 baseEnd_3635491 := by
    simpa [prefixWord, tailWord_3635491, baseEnd_3635491] using wordTrace_append hprefix tailTrace_3635491
  have hstable : (prefixWord ++ tailWord_3635491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635491).length < 2 ^ (prefixWord ++ tailWord_3635491).sum := by decide
  have hdescent : baseEnd_3635491 < baseStart_3635491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635496 : List Nat := [2, 1, 5, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_3635496 : Nat := 118140960795 + 3635496 * 2 ^ 59
def prefixEnd_3635496 : Nat := 4983230072969 + 3 ^ 40 * 3635496 * 2
def baseEnd_3635496 : Nat := 1866756865498013338880665

theorem tailTrace_3635496 : CollatzResearch.WordTrace tailWord_3635496 prefixEnd_3635496 1866756865498013338880665 := by
  unfold tailWord_3635496
  simp only [CollatzResearch.WordTrace]
  refine ⟨66298716218613180065035171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88398288291484240086713561 66298716218613180065035171)
  ·
    refine ⟨99448074327919770097552757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66298716218613180065035171 99448074327919770097552757)
    ·
      refine ⟨9323256968242478446645571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99448074327919770097552757 9323256968242478446645571)
      ·
        refine ⟨13984885452363717669968357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9323256968242478446645571 13984885452363717669968357)
        ·
          refine ⟨2622166022318197063119067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13984885452363717669968357 2622166022318197063119067)
          ·
            refine ⟨3933249033477295594678601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622166022318197063119067 3933249033477295594678601)
            ·
              refine ⟨2949936775107971696008951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3933249033477295594678601 2949936775107971696008951)
              ·
                refine ⟨4424905162661957544013427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2949936775107971696008951 4424905162661957544013427)
                ·
                  refine ⟨6637357743992936316020141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424905162661957544013427 6637357743992936316020141)
                  ·
                    refine ⟨2489009153997351118507553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6637357743992936316020141 2489009153997351118507553)
                    ·
                      refine ⟨1866756865498013338880665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2489009153997351118507553 1866756865498013338880665)
                      ·
                        rfl

theorem cell23_3635496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_3635496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635496 prefixEnd_3635496 := by exact prefixLift 3635496
  have htrace : WordTrace (prefixWord ++ tailWord_3635496) baseStart_3635496 baseEnd_3635496 := by
    simpa [prefixWord, tailWord_3635496, baseEnd_3635496] using wordTrace_append hprefix tailTrace_3635496
  have hstable : (prefixWord ++ tailWord_3635496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635496).length < 2 ^ (prefixWord ++ tailWord_3635496).sum := by decide
  have hdescent : baseEnd_3635496 < baseStart_3635496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635511 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 2, 5]
def baseStart_3635511 : Nat := 118140960795 + 3635511 * 2 ^ 59
def prefixEnd_3635511 : Nat := 4983230072969 + 3 ^ 40 * 3635511 * 2
def baseEnd_3635511 : Nat := 622254855902610260064365

theorem tailTrace_3635511 : CollatzResearch.WordTrace tailWord_3635511 prefixEnd_3635511 622254855902610260064365 := by
  unfold tailWord_3635511
  simp only [CollatzResearch.WordTrace]
  refine ⟨132597979532172017691866387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88398653021448011794577591 132597979532172017691866387)
  ·
    refine ⟨198896969298258026537799581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132597979532172017691866387 198896969298258026537799581)
    ·
      refine ⟨74586363486846759951674843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198896969298258026537799581 74586363486846759951674843)
      ·
        refine ⟨111879545230270139927512265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74586363486846759951674843 111879545230270139927512265)
        ·
          refine ⟨83909658922702604945634199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111879545230270139927512265 83909658922702604945634199)
          ·
            refine ⟨125864488384053907418451299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83909658922702604945634199 125864488384053907418451299)
            ·
              refine ⟨188796732576080861127676949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125864488384053907418451299 188796732576080861127676949)
              ·
                refine ⟨8849846839503790365359857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188796732576080861127676949 8849846839503790365359857)
                ·
                  refine ⟨6637385129627842774019893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8849846839503790365359857 6637385129627842774019893)
                  ·
                    refine ⟨622254855902610260064365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6637385129627842774019893 622254855902610260064365)
                    ·
                      rfl

theorem cell23_3635511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_3635511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635511 prefixEnd_3635511 := by exact prefixLift 3635511
  have htrace : WordTrace (prefixWord ++ tailWord_3635511) baseStart_3635511 baseEnd_3635511 := by
    simpa [prefixWord, tailWord_3635511, baseEnd_3635511] using wordTrace_append hprefix tailTrace_3635511
  have hstable : (prefixWord ++ tailWord_3635511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635511).length < 2 ^ (prefixWord ++ tailWord_3635511).sum := by decide
  have hdescent : baseEnd_3635511 < baseStart_3635511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635531 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 4]
def baseStart_3635531 : Nat := 118140960795 + 3635531 * 2 ^ 59
def prefixEnd_3635531 : Nat := 4983230072969 + 3 ^ 40 * 3635531 * 2
def baseEnd_3635531 : Nat := 1866774837320920701943003

theorem tailTrace_3635531 : CollatzResearch.WordTrace tailWord_3635531 prefixEnd_3635531 1866774837320920701943003 := by
  unfold tailWord_3635531
  simp only [CollatzResearch.WordTrace]
  refine ⟨132598708992099561107594447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88399139328066374071729631 132598708992099561107594447)
  ·
    refine ⟨198898063488149341661391671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132598708992099561107594447 198898063488149341661391671)
    ·
      refine ⟨298347095232224012492087507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198898063488149341661391671 298347095232224012492087507)
      ·
        refine ⟨447520642848336018738131261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298347095232224012492087507 447520642848336018738131261)
        ·
          refine ⟨167820241068126007026799223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447520642848336018738131261 167820241068126007026799223)
          ·
            refine ⟨251730361602189010540198835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167820241068126007026799223 251730361602189010540198835)
            ·
              refine ⟨377595542403283515810298253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251730361602189010540198835 377595542403283515810298253)
              ·
                refine ⟨141598328401231318428861845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377595542403283515810298253 141598328401231318428861845)
                ·
                  refine ⟨6637421643807718051352899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141598328401231318428861845 6637421643807718051352899)
                  ·
                    refine ⟨9956132465711577077029349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6637421643807718051352899 9956132465711577077029349)
                    ·
                      refine ⟨1866774837320920701943003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9956132465711577077029349 1866774837320920701943003)
                      ·
                        rfl

theorem cell23_3635531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 4].length) (baseStart_3635531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635531 prefixEnd_3635531 := by exact prefixLift 3635531
  have htrace : WordTrace (prefixWord ++ tailWord_3635531) baseStart_3635531 baseEnd_3635531 := by
    simpa [prefixWord, tailWord_3635531, baseEnd_3635531] using wordTrace_append hprefix tailTrace_3635531
  have hstable : (prefixWord ++ tailWord_3635531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635531).length < 2 ^ (prefixWord ++ tailWord_3635531).sum := by decide
  have hdescent : baseEnd_3635531 < baseStart_3635531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635568 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 3]
def baseStart_3635568 : Nat := 118140960795 + 3635568 * 2 ^ 59
def prefixEnd_3635568 : Nat := 4983230072969 + 3 ^ 40 * 3635568 * 2
def baseEnd_3635568 : Nat := 1866793836105137057180333

theorem tailTrace_3635568 : CollatzResearch.WordTrace tailWord_3635568 prefixEnd_3635568 1866793836105137057180333 := by
  unfold tailWord_3635568
  simp only [CollatzResearch.WordTrace]
  refine ⟨66300029246482758213345679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88400038995310344284460905 66300029246482758213345679)
  ·
    refine ⟨99450043869724137320018519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66300029246482758213345679 99450043869724137320018519)
    ·
      refine ⟨149175065804586205980027779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99450043869724137320018519 149175065804586205980027779)
      ·
        refine ⟨223762598706879308970041669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149175065804586205980027779 223762598706879308970041669)
        ·
          refine ⟨41955487257539870431882813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223762598706879308970041669 41955487257539870431882813)
          ·
            refine ⟨15733307721577451411956055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41955487257539870431882813 15733307721577451411956055)
            ·
              refine ⟨23599961582366177117934083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15733307721577451411956055 23599961582366177117934083)
              ·
                refine ⟨35399942373549265676901125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23599961582366177117934083 35399942373549265676901125)
                ·
                  refine ⟨6637489195040487314418961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35399942373549265676901125 6637489195040487314418961)
                  ·
                    refine ⟨4978116896280365485814221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6637489195040487314418961 4978116896280365485814221)
                    ·
                      refine ⟨1866793836105137057180333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4978116896280365485814221 1866793836105137057180333)
                      ·
                        rfl

theorem cell23_3635568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 3].length) (baseStart_3635568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635568 prefixEnd_3635568 := by exact prefixLift 3635568
  have htrace : WordTrace (prefixWord ++ tailWord_3635568) baseStart_3635568 baseEnd_3635568 := by
    simpa [prefixWord, tailWord_3635568, baseEnd_3635568] using wordTrace_append hprefix tailTrace_3635568
  have hstable : (prefixWord ++ tailWord_3635568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635568).length < 2 ^ (prefixWord ++ tailWord_3635568).sum := by decide
  have hdescent : baseEnd_3635568 < baseStart_3635568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635588 : List Nat := [2, 3, 2, 1, 1, 2, 3, 3, 6]
def baseStart_3635588 : Nat := 118140960795 + 3635588 * 2 ^ 59
def prefixEnd_3635588 : Nat := 4983230072969 + 3 ^ 40 * 3635588 * 2
def baseEnd_3635588 : Nat := 207422678413136330992249

theorem tailTrace_3635588 : CollatzResearch.WordTrace tailWord_3635588 prefixEnd_3635588 207422678413136330992249 := by
  unfold tailWord_3635588
  simp only [CollatzResearch.WordTrace]
  refine ⟨66300393976446529921209709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88400525301928706561612945 66300393976446529921209709)
  ·
    refine ⟨24862647741167448720453641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66300393976446529921209709 24862647741167448720453641)
    ·
      refine ⟨18646985805875586540340231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24862647741167448720453641 18646985805875586540340231)
      ·
        refine ⟨27970478708813379810510347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18646985805875586540340231 27970478708813379810510347)
        ·
          refine ⟨41955718063220069715765521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27970478708813379810510347 41955718063220069715765521)
          ·
            refine ⟨31466788547415052286824141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41955718063220069715765521 31466788547415052286824141)
            ·
              refine ⟨11800045705280644607559053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31466788547415052286824141 11800045705280644607559053)
              ·
                refine ⟨4425017139480241727834645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11800045705280644607559053 4425017139480241727834645)
                ·
                  refine ⟨207422678413136330992249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4425017139480241727834645 207422678413136330992249)
                  ·
                    rfl

theorem cell23_3635588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_3635588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635588 prefixEnd_3635588 := by exact prefixLift 3635588
  have htrace : WordTrace (prefixWord ++ tailWord_3635588) baseStart_3635588 baseEnd_3635588 := by
    simpa [prefixWord, tailWord_3635588, baseEnd_3635588] using wordTrace_append hprefix tailTrace_3635588
  have hstable : (prefixWord ++ tailWord_3635588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635588).length < 2 ^ (prefixWord ++ tailWord_3635588).sum := by decide
  have hdescent : baseEnd_3635588 < baseStart_3635588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635648 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 6, 4]
def baseStart_3635648 : Nat := 118140960795 + 3635648 * 2 ^ 59
def prefixEnd_3635648 : Nat := 4983230072969 + 3 ^ 40 * 3635648 * 2
def baseEnd_3635648 : Nat := 622278304852498914726655

theorem tailTrace_3635648 : CollatzResearch.WordTrace tailWord_3635648 prefixEnd_3635648 622278304852498914726655 := by
  unfold tailWord_3635648
  simp only [CollatzResearch.WordTrace]
  refine ⟨66301488166337845044801799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88401984221783793393069065 66301488166337845044801799)
  ·
    refine ⟨99452232249506767567202699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66301488166337845044801799 99452232249506767567202699)
    ·
      refine ⟨149178348374260151350804049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99452232249506767567202699 149178348374260151350804049)
      ·
        refine ⟨111883761280695113513103037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149178348374260151350804049 111883761280695113513103037)
        ·
          refine ⟨41956410480260667567413639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111883761280695113513103037 41956410480260667567413639)
          ·
            refine ⟨62934615720391001351120459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41956410480260667567413639 62934615720391001351120459)
            ·
              refine ⟨94401923580586502026680689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62934615720391001351120459 94401923580586502026680689)
              ·
                refine ⟨70801442685439876520010517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94401923580586502026680689 70801442685439876520010517)
                ·
                  refine ⟨3318817625879994211875493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70801442685439876520010517 3318817625879994211875493)
                  ·
                    refine ⟨622278304852498914726655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3318817625879994211875493 622278304852498914726655)
                    ·
                      rfl

theorem cell23_3635648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 6, 4].length) (baseStart_3635648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635648 prefixEnd_3635648 := by exact prefixLift 3635648
  have htrace : WordTrace (prefixWord ++ tailWord_3635648) baseStart_3635648 baseEnd_3635648 := by
    simpa [prefixWord, tailWord_3635648, baseEnd_3635648] using wordTrace_append hprefix tailTrace_3635648
  have hstable : (prefixWord ++ tailWord_3635648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635648).length < 2 ^ (prefixWord ++ tailWord_3635648).sum := by decide
  have hdescent : baseEnd_3635648 < baseStart_3635648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635705 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 1, 3, 3]
def baseStart_3635705 : Nat := 118140960795 + 3635705 * 2 ^ 59
def prefixEnd_3635705 : Nat := 4983230072969 + 3 ^ 40 * 3635705 * 2
def baseEnd_3635705 : Nat := 1866864182954803021167203

theorem tailTrace_3635705 : CollatzResearch.WordTrace tailWord_3635705 prefixEnd_3635705 1866864182954803021167203 := by
  unfold tailWord_3635705
  simp only [CollatzResearch.WordTrace]
  refine ⟨132605055293469188824428569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88403370195646125882952379 132605055293469188824428569)
  ·
    refine ⟨99453791470101891618321427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132605055293469188824428569 99453791470101891618321427)
    ·
      refine ⟨149180687205152837427482141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99453791470101891618321427 149180687205152837427482141)
      ·
        refine ⟨55942757701932314035305803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149180687205152837427482141 55942757701932314035305803)
        ·
          refine ⟨83914136552898471052958705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55942757701932314035305803 83914136552898471052958705)
          ·
            refine ⟨62935602414673853289719029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83914136552898471052958705 62935602414673853289719029)
            ·
              refine ⟨5900212726375673745911159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62935602414673853289719029 5900212726375673745911159)
              ·
                refine ⟨8850319089563510618866739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5900212726375673745911159 8850319089563510618866739)
                ·
                  refine ⟨13275478634345265928300109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8850319089563510618866739 13275478634345265928300109)
                  ·
                    refine ⟨4978304487879474723112541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13275478634345265928300109 4978304487879474723112541)
                    ·
                      refine ⟨1866864182954803021167203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4978304487879474723112541 1866864182954803021167203)
                      ·
                        rfl

theorem cell23_3635705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_3635705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635705 prefixEnd_3635705 := by exact prefixLift 3635705
  have htrace : WordTrace (prefixWord ++ tailWord_3635705) baseStart_3635705 baseEnd_3635705 := by
    simpa [prefixWord, tailWord_3635705, baseEnd_3635705] using wordTrace_append hprefix tailTrace_3635705
  have hstable : (prefixWord ++ tailWord_3635705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635705).length < 2 ^ (prefixWord ++ tailWord_3635705).sum := by decide
  have hdescent : baseEnd_3635705 < baseStart_3635705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635738 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 4, 6]
def baseStart_3635738 : Nat := 118140960795 + 3635738 * 2 ^ 59
def prefixEnd_3635738 : Nat := 4983230072969 + 3 ^ 40 * 3635738 * 2
def baseEnd_3635738 : Nat := 622293709272133797351517

theorem tailTrace_3635738 : CollatzResearch.WordTrace tailWord_3635738 prefixEnd_3635738 622293709272133797351517 := by
  unfold tailWord_3635738
  simp only [CollatzResearch.WordTrace]
  refine ⟨33151564725587408865094967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88404172601566423640253245 33151564725587408865094967)
  ·
    refine ⟨49727347088381113297642451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33151564725587408865094967 49727347088381113297642451)
    ·
      refine ⟨74591020632571669946463677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49727347088381113297642451 74591020632571669946463677)
      ·
        refine ⟨27971632737214376229923879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74591020632571669946463677 27971632737214376229923879)
        ·
          refine ⟨41957449105821564344885819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27971632737214376229923879 41957449105821564344885819)
          ·
            refine ⟨62936173658732346517328729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41957449105821564344885819 62936173658732346517328729)
            ·
              refine ⟨47202130244049259887996547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62936173658732346517328729 47202130244049259887996547)
              ·
                refine ⟨70803195366073889831994821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47202130244049259887996547 70803195366073889831994821)
                ·
                  refine ⟨13275599131138854343499029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70803195366073889831994821 13275599131138854343499029)
                  ·
                    refine ⟨622293709272133797351517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13275599131138854343499029 622293709272133797351517)
                    ·
                      rfl

theorem cell23_3635738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_3635738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635738 prefixEnd_3635738 := by exact prefixLift 3635738
  have htrace : WordTrace (prefixWord ++ tailWord_3635738) baseStart_3635738 baseEnd_3635738 := by
    simpa [prefixWord, tailWord_3635738, baseEnd_3635738] using wordTrace_append hprefix tailTrace_3635738
  have hstable : (prefixWord ++ tailWord_3635738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635738).length < 2 ^ (prefixWord ++ tailWord_3635738).sum := by decide
  have hdescent : baseEnd_3635738 < baseStart_3635738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635766 : List Nat := [5, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_3635766 : Nat := 118140960795 + 3635766 * 2 ^ 59
def prefixEnd_3635766 : Nat := 4983230072969 + 3 ^ 40 * 3635766 * 2
def baseEnd_3635766 : Nat := 1866895505274727282504423

theorem tailTrace_3635766 : CollatzResearch.WordTrace tailWord_3635766 prefixEnd_3635766 1866895505274727282504423 := by
  unfold tailWord_3635766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8287955009140512265149947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88404853430832130828266101 8287955009140512265149947)
  ·
    refine ⟨12431932513710768397724921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8287955009140512265149947 12431932513710768397724921)
    ·
      refine ⟨9323949385283076298293691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12431932513710768397724921 9323949385283076298293691)
      ·
        refine ⟨13985924077924614447440537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9323949385283076298293691 13985924077924614447440537)
        ·
          refine ⟨10489443058443460835580403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13985924077924614447440537 10489443058443460835580403)
          ·
            refine ⟨15734164587665191253370605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10489443058443460835580403 15734164587665191253370605)
            ·
              refine ⟨5900311720374446720013977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15734164587665191253370605 5900311720374446720013977)
              ·
                refine ⟨4425233790280835040010483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5900311720374446720013977 4425233790280835040010483)
                ·
                  refine ⟨6637850685421252560015725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4425233790280835040010483 6637850685421252560015725)
                  ·
                    refine ⟨2489194007032969710005897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6637850685421252560015725 2489194007032969710005897)
                    ·
                      refine ⟨1866895505274727282504423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2489194007032969710005897 1866895505274727282504423)
                      ·
                        rfl

theorem cell23_3635766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_3635766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635766 prefixEnd_3635766 := by exact prefixLift 3635766
  have htrace : WordTrace (prefixWord ++ tailWord_3635766) baseStart_3635766 baseEnd_3635766 := by
    simpa [prefixWord, tailWord_3635766, baseEnd_3635766] using wordTrace_append hprefix tailTrace_3635766
  have hstable : (prefixWord ++ tailWord_3635766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635766).length < 2 ^ (prefixWord ++ tailWord_3635766).sum := by decide
  have hdescent : baseEnd_3635766 < baseStart_3635766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635768 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 9]
def baseStart_3635768 : Nat := 118140960795 + 3635768 * 2 ^ 59
def prefixEnd_3635768 : Nat := 4983230072969 + 3 ^ 40 * 3635768 * 2
def baseEnd_3635768 : Nat := 207432948026226252742157

theorem tailTrace_3635768 : CollatzResearch.WordTrace tailWord_3635768 prefixEnd_3635768 207432948026226252742157 := by
  unfold tailWord_3635768
  simp only [CollatzResearch.WordTrace]
  refine ⟨66303676546120475291985979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88404902061493967055981305 66303676546120475291985979)
  ·
    refine ⟨99455514819180712937978969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66303676546120475291985979 99455514819180712937978969)
    ·
      refine ⟨74591636114385534703484227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99455514819180712937978969 74591636114385534703484227)
      ·
        refine ⟨111887454171578302055226341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74591636114385534703484227 111887454171578302055226341)
        ·
          refine ⟨20978897657170931635354939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111887454171578302055226341 20978897657170931635354939)
          ·
            refine ⟨31468346485756397453032409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20978897657170931635354939 31468346485756397453032409)
            ·
              refine ⟨23601259864317298089774307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31468346485756397453032409 23601259864317298089774307)
              ·
                refine ⟨35401889796475947134661461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23601259864317298089774307 35401889796475947134661461)
                ·
                  refine ⟨207432948026226252742157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35401889796475947134661461 207432948026226252742157)
                  ·
                    rfl

theorem cell23_3635768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 9].length) (baseStart_3635768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635768 prefixEnd_3635768 := by exact prefixLift 3635768
  have htrace : WordTrace (prefixWord ++ tailWord_3635768) baseStart_3635768 baseEnd_3635768 := by
    simpa [prefixWord, tailWord_3635768, baseEnd_3635768] using wordTrace_append hprefix tailTrace_3635768
  have hstable : (prefixWord ++ tailWord_3635768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635768).length < 2 ^ (prefixWord ++ tailWord_3635768).sum := by decide
  have hdescent : baseEnd_3635768 < baseStart_3635768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635796 : List Nat := [2, 4, 1, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_3635796 : Nat := 118140960795 + 3635796 * 2 ^ 59
def prefixEnd_3635796 : Nat := 4983230072969 + 3 ^ 40 * 3635796 * 2
def baseEnd_3635796 : Nat := 1866910909694362165129285

theorem tailTrace_3635796 : CollatzResearch.WordTrace tailWord_3635796 prefixEnd_3635796 1866910909694362165129285 := by
  unfold tailWord_3635796
  simp only [CollatzResearch.WordTrace]
  refine ⟨66304187168069755682995621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88405582890759674243994161 66304187168069755682995621)
  ·
    refine ⟨12432035094013079190561679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66304187168069755682995621 12432035094013079190561679)
    ·
      refine ⟨18648052641019618785842519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12432035094013079190561679 18648052641019618785842519)
      ·
        refine ⟨27972078961529428178763779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18648052641019618785842519 27972078961529428178763779)
        ·
          refine ⟨41958118442294142268145669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27972078961529428178763779 41958118442294142268145669)
          ·
            refine ⟨7867147207930151675277313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41958118442294142268145669 7867147207930151675277313)
            ·
              refine ⟨5900360405947613756457985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7867147207930151675277313 5900360405947613756457985)
              ·
                refine ⟨4425270304460710317343489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5900360405947613756457985 4425270304460710317343489)
                ·
                  refine ⟨3318952728345532738007617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4425270304460710317343489 3318952728345532738007617)
                  ·
                    refine ⟨2489214546259149553505713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3318952728345532738007617 2489214546259149553505713)
                    ·
                      refine ⟨1866910909694362165129285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2489214546259149553505713 1866910909694362165129285)
                      ·
                        rfl

theorem cell23_3635796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_3635796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635796 prefixEnd_3635796 := by exact prefixLift 3635796
  have htrace : WordTrace (prefixWord ++ tailWord_3635796) baseStart_3635796 baseEnd_3635796 := by
    simpa [prefixWord, tailWord_3635796, baseEnd_3635796] using wordTrace_append hprefix tailTrace_3635796
  have hstable : (prefixWord ++ tailWord_3635796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635796).length < 2 ^ (prefixWord ++ tailWord_3635796).sum := by decide
  have hdescent : baseEnd_3635796 < baseStart_3635796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635806 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3635806 : Nat := 118140960795 + 3635806 * 2 ^ 59
def prefixEnd_3635806 : Nat := 4983230072969 + 3 ^ 40 * 3635806 * 2
def baseEnd_3635806 : Nat := 622305348166969042001413

theorem tailTrace_3635806 : CollatzResearch.WordTrace tailWord_3635806 prefixEnd_3635806 622305348166969042001413 := by
  unfold tailWord_3635806
  simp only [CollatzResearch.WordTrace]
  refine ⟨16576092383262910384231909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88405826044068855382570181 16576092383262910384231909)
  ·
    refine ⟨3108017321861795697043483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16576092383262910384231909 3108017321861795697043483)
    ·
      refine ⟨4662025982792693545565225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3108017321861795697043483 4662025982792693545565225)
      ·
        refine ⟨3496519487094520159173919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4662025982792693545565225 3496519487094520159173919)
        ·
          refine ⟨5244779230641780238760879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3496519487094520159173919 5244779230641780238760879)
          ·
            refine ⟨7867168845962670358141319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5244779230641780238760879 7867168845962670358141319)
            ·
              refine ⟨11800753268944005537211979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7867168845962670358141319 11800753268944005537211979)
              ·
                refine ⟨17701129903416008305817969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11800753268944005537211979 17701129903416008305817969)
                ·
                  refine ⟨13275847427562006229363477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17701129903416008305817969 13275847427562006229363477)
                  ·
                    refine ⟨622305348166969042001413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13275847427562006229363477 622305348166969042001413)
                    ·
                      rfl

theorem cell23_3635806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3635806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635806 prefixEnd_3635806 := by exact prefixLift 3635806
  have htrace : WordTrace (prefixWord ++ tailWord_3635806) baseStart_3635806 baseEnd_3635806 := by
    simpa [prefixWord, tailWord_3635806, baseEnd_3635806] using wordTrace_append hprefix tailTrace_3635806
  have hstable : (prefixWord ++ tailWord_3635806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635806).length < 2 ^ (prefixWord ++ tailWord_3635806).sum := by decide
  have hdescent : baseEnd_3635806 < baseStart_3635806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635835 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 4]
def baseStart_3635835 : Nat := 118140960795 + 3635835 * 2 ^ 59
def prefixEnd_3635835 : Nat := 4983230072969 + 3 ^ 40 * 3635835 * 2
def baseEnd_3635835 : Nat := 1866930935439887512541605

theorem tailTrace_3635835 : CollatzResearch.WordTrace tailWord_3635835 prefixEnd_3635835 1866930935439887512541605 := by
  unfold tailWord_3635835
  simp only [CollatzResearch.WordTrace]
  refine ⟨132609796782998221026660959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88406531188665480684440639 132609796782998221026660959)
  ·
    refine ⟨198914695174497331539991439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132609796782998221026660959 198914695174497331539991439)
    ·
      refine ⟨298372042761745997309987159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198914695174497331539991439 298372042761745997309987159)
      ·
        refine ⟨447558064142618995964980739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298372042761745997309987159 447558064142618995964980739)
        ·
          refine ⟨671337096213928493947471109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447558064142618995964980739 671337096213928493947471109)
          ·
            refine ⟨125875705540111592615150833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 671337096213928493947471109 125875705540111592615150833)
            ·
              refine ⟨94406779155083694461363125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125875705540111592615150833 94406779155083694461363125)
              ·
                refine ⟨8850635545789096355752793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94406779155083694461363125 8850635545789096355752793)
                ·
                  refine ⟨6637976659341822266814595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8850635545789096355752793 6637976659341822266814595)
                  ·
                    refine ⟨9956964989012733400221893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6637976659341822266814595 9956964989012733400221893)
                    ·
                      refine ⟨1866930935439887512541605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9956964989012733400221893 1866930935439887512541605)
                      ·
                        rfl

theorem cell23_3635835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 4].length) (baseStart_3635835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635835 prefixEnd_3635835 := by exact prefixLift 3635835
  have htrace : WordTrace (prefixWord ++ tailWord_3635835) baseStart_3635835 baseEnd_3635835 := by
    simpa [prefixWord, tailWord_3635835, baseEnd_3635835] using wordTrace_append hprefix tailTrace_3635835
  have hstable : (prefixWord ++ tailWord_3635835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635835).length < 2 ^ (prefixWord ++ tailWord_3635835).sum := by decide
  have hdescent : baseEnd_3635835 < baseStart_3635835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635939 : List Nat := [1, 1, 1, 7, 1, 1, 3, 2, 1, 5]
def baseStart_3635939 : Nat := 118140960795 + 3635939 * 2 ^ 59
def prefixEnd_3635939 : Nat := 4983230072969 + 3 ^ 40 * 3635939 * 2
def baseEnd_3635939 : Nat := 622328112475985035213709

theorem tailTrace_3635939 : CollatzResearch.WordTrace tailWord_3635939 prefixEnd_3635939 622328112475985035213709 := by
  unfold tailWord_3635939
  simp only [CollatzResearch.WordTrace]
  refine ⟨132613589974621446788446871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88409059983080964525631247 132613589974621446788446871)
  ·
    refine ⟨198920384961932170182670307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132613589974621446788446871 198920384961932170182670307)
    ·
      refine ⟨298380577442898255274005461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198920384961932170182670307 298380577442898255274005461)
      ·
        refine ⟨6993294783817927857984503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 298380577442898255274005461 6993294783817927857984503)
        ·
          refine ⟨10489942175726891786976755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6993294783817927857984503 10489942175726891786976755)
          ·
            refine ⟨15734913263590337680465133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10489942175726891786976755 15734913263590337680465133)
            ·
              refine ⟨5900592473846376630174425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15734913263590337680465133 5900592473846376630174425)
              ·
                refine ⟨4425444355384782472630819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5900592473846376630174425 4425444355384782472630819)
                ·
                  refine ⟨6638166533077173708946229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4425444355384782472630819 6638166533077173708946229)
                  ·
                    refine ⟨622328112475985035213709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6638166533077173708946229 622328112475985035213709)
                    ·
                      rfl

theorem cell23_3635939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 5].length) (baseStart_3635939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635939 prefixEnd_3635939 := by exact prefixLift 3635939
  have htrace : WordTrace (prefixWord ++ tailWord_3635939) baseStart_3635939 baseEnd_3635939 := by
    simpa [prefixWord, tailWord_3635939, baseEnd_3635939] using wordTrace_append hprefix tailTrace_3635939
  have hstable : (prefixWord ++ tailWord_3635939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635939).length < 2 ^ (prefixWord ++ tailWord_3635939).sum := by decide
  have hdescent : baseEnd_3635939 < baseStart_3635939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635945 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 5]
def baseStart_3635945 : Nat := 118140960795 + 3635945 * 2 ^ 59
def prefixEnd_3635945 : Nat := 4983230072969 + 3 ^ 40 * 3635945 * 2
def baseEnd_3635945 : Nat := 1866987418311882082166099

theorem tailTrace_3635945 : CollatzResearch.WordTrace tailWord_3635945 prefixEnd_3635945 1866987418311882082166099 := by
  unfold tailWord_3635945
  simp only [CollatzResearch.WordTrace]
  refine ⟨132613808812599709813165289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88409205875066473208776859 132613808812599709813165289)
  ·
    refine ⟨99460356609449782359873967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132613808812599709813165289 99460356609449782359873967)
    ·
      refine ⟨149190534914174673539810951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99460356609449782359873967 149190534914174673539810951)
      ·
        refine ⟨223785802371262010309716427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149190534914174673539810951 223785802371262010309716427)
        ·
          refine ⟨335678703556893015464574641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223785802371262010309716427 335678703556893015464574641)
          ·
            refine ⟨251759027667669761598430981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335678703556893015464574641 251759027667669761598430981)
            ·
              refine ⟨47204817687688080299705809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251759027667669761598430981 47204817687688080299705809)
              ·
                refine ⟨35403613265766060224779357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47204817687688080299705809 35403613265766060224779357)
                ·
                  refine ⟨13276354974662272584292259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35403613265766060224779357 13276354974662272584292259)
                  ·
                    refine ⟨19914532461993408876438389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13276354974662272584292259 19914532461993408876438389)
                    ·
                      refine ⟨1866987418311882082166099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19914532461993408876438389 1866987418311882082166099)
                      ·
                        rfl

theorem cell23_3635945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_3635945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635945 prefixEnd_3635945 := by exact prefixLift 3635945
  have htrace : WordTrace (prefixWord ++ tailWord_3635945) baseStart_3635945 baseEnd_3635945 := by
    simpa [prefixWord, tailWord_3635945, baseEnd_3635945] using wordTrace_append hprefix tailTrace_3635945
  have hstable : (prefixWord ++ tailWord_3635945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635945).length < 2 ^ (prefixWord ++ tailWord_3635945).sum := by decide
  have hdescent : baseEnd_3635945 < baseStart_3635945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635962 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5]
def baseStart_3635962 : Nat := 118140960795 + 3635962 * 2 ^ 59
def prefixEnd_3635962 : Nat := 4983230072969 + 3 ^ 40 * 3635962 * 2
def baseEnd_3635962 : Nat := 1866996147483008515653521

theorem tailTrace_3635962 : CollatzResearch.WordTrace tailWord_3635962 prefixEnd_3635962 1866996147483008515653521 := by
  unfold tailWord_3635962
  simp only [CollatzResearch.WordTrace]
  refine ⟨33153607213384530429133535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88409619235692081144356093 33153607213384530429133535)
  ·
    refine ⟨49730410820076795643700303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33153607213384530429133535 49730410820076795643700303)
    ·
      refine ⟨74595616230115193465550455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49730410820076795643700303 74595616230115193465550455)
      ·
        refine ⟨111893424345172790198325683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74595616230115193465550455 111893424345172790198325683)
        ·
          refine ⟨167840136517759185297488525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111893424345172790198325683 167840136517759185297488525)
          ·
            refine ⟨62940051194159694486558197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167840136517759185297488525 62940051194159694486558197)
            ·
              refine ⟨5900629799452471358114831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62940051194159694486558197 5900629799452471358114831)
              ·
                refine ⟨8850944699178707037172247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5900629799452471358114831 8850944699178707037172247)
                ·
                  refine ⟨13276417048768060555758371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8850944699178707037172247 13276417048768060555758371)
                  ·
                    refine ⟨19914625573152090833637557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13276417048768060555758371 19914625573152090833637557)
                    ·
                      refine ⟨1866996147483008515653521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19914625573152090833637557 1866996147483008515653521)
                      ·
                        rfl

theorem cell23_3635962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_3635962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635962 prefixEnd_3635962 := by exact prefixLift 3635962
  have htrace : WordTrace (prefixWord ++ tailWord_3635962) baseStart_3635962 baseEnd_3635962 := by
    simpa [prefixWord, tailWord_3635962, baseEnd_3635962] using wordTrace_append hprefix tailTrace_3635962
  have hstable : (prefixWord ++ tailWord_3635962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635962).length < 2 ^ (prefixWord ++ tailWord_3635962).sum := by decide
  have hdescent : baseEnd_3635962 < baseStart_3635962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635970 : List Nat := [3, 4, 1, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_3635970 : Nat := 118140960795 + 3635970 * 2 ^ 59
def prefixEnd_3635970 : Nat := 4983230072969 + 3 ^ 40 * 3635970 * 2
def baseEnd_3635970 : Nat := 1867000255328244484353485

theorem tailTrace_3635970 : CollatzResearch.WordTrace tailWord_3635970 prefixEnd_3635970 1867000255328244484353485 := by
  unfold tailWord_3635970
  simp only [CollatzResearch.WordTrace]
  refine ⟨33153680159377284770706341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88409813758339426055216909 33153680159377284770706341)
  ·
    refine ⟨6216315029883240894507439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33153680159377284770706341 6216315029883240894507439)
    ·
      refine ⟨9324472544824861341761159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6216315029883240894507439 9324472544824861341761159)
      ·
        refine ⟨13986708817237292012641739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9324472544824861341761159 13986708817237292012641739)
        ·
          refine ⟨20980063225855938018962609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13986708817237292012641739 20980063225855938018962609)
          ·
            refine ⟨15735047419391953514221957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20980063225855938018962609 15735047419391953514221957)
            ·
              refine ⟨2950321391135991283916617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15735047419391953514221957 2950321391135991283916617)
              ·
                refine ⟨2212741043351993462937463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2950321391135991283916617 2212741043351993462937463)
                ·
                  refine ⟨3319111565027990194406195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212741043351993462937463 3319111565027990194406195)
                  ·
                    refine ⟨4978667347541985291609293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3319111565027990194406195 4978667347541985291609293)
                    ·
                      refine ⟨1867000255328244484353485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4978667347541985291609293 1867000255328244484353485)
                      ·
                        rfl

theorem cell23_3635970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_3635970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635970 prefixEnd_3635970 := by exact prefixLift 3635970
  have htrace : WordTrace (prefixWord ++ tailWord_3635970) baseStart_3635970 baseEnd_3635970 := by
    simpa [prefixWord, tailWord_3635970, baseEnd_3635970] using wordTrace_append hprefix tailTrace_3635970
  have hstable : (prefixWord ++ tailWord_3635970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635970).length < 2 ^ (prefixWord ++ tailWord_3635970).sum := by decide
  have hdescent : baseEnd_3635970 < baseStart_3635970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635972 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3635972 : Nat := 118140960795 + 3635972 * 2 ^ 59
def prefixEnd_3635972 : Nat := 4983230072969 + 3 ^ 40 * 3635972 * 2
def baseEnd_3635972 : Nat := 1867001282289553476528475

theorem tailTrace_3635972 : CollatzResearch.WordTrace tailWord_3635972 prefixEnd_3635972 1867001282289553476528475 := by
  unfold tailWord_3635972
  simp only [CollatzResearch.WordTrace]
  refine ⟨66307396791750946712199085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88409862389001262282932113 66307396791750946712199085)
  ·
    refine ⟨24865273796906605017074657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66307396791750946712199085 24865273796906605017074657)
    ·
      refine ⟨18648955347679953762805993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24865273796906605017074657 18648955347679953762805993)
      ·
        refine ⟨13986716510759965322104495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18648955347679953762805993 13986716510759965322104495)
        ·
          refine ⟨20980074766139947983156743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13986716510759965322104495 20980074766139947983156743)
          ·
            refine ⟨31470112149209921974735115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20980074766139947983156743 31470112149209921974735115)
            ·
              refine ⟨47205168223814882962102673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31470112149209921974735115 47205168223814882962102673)
              ·
                refine ⟨35403876167861162221577005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47205168223814882962102673 35403876167861162221577005)
                ·
                  refine ⟨13276453562947935833091377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35403876167861162221577005 13276453562947935833091377)
                  ·
                    refine ⟨9957340172210951874818533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13276453562947935833091377 9957340172210951874818533)
                    ·
                      refine ⟨1867001282289553476528475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9957340172210951874818533 1867001282289553476528475)
                      ·
                        rfl

theorem cell23_3635972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3635972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635972 prefixEnd_3635972 := by exact prefixLift 3635972
  have htrace : WordTrace (prefixWord ++ tailWord_3635972) baseStart_3635972 baseEnd_3635972 := by
    simpa [prefixWord, tailWord_3635972, baseEnd_3635972] using wordTrace_append hprefix tailTrace_3635972
  have hstable : (prefixWord ++ tailWord_3635972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635972).length < 2 ^ (prefixWord ++ tailWord_3635972).sum := by decide
  have hdescent : baseEnd_3635972 < baseStart_3635972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635985 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_3635985 : Nat := 118140960795 + 3635985 * 2 ^ 59
def prefixEnd_3635985 : Nat := 4983230072969 + 3 ^ 40 * 3635985 * 2
def baseEnd_3635985 : Nat := 1867007957538061925665915

theorem tailTrace_3635985 : CollatzResearch.WordTrace tailWord_3635985 prefixEnd_3635985 1867007957538061925665915 := by
  unfold tailWord_3635985
  simp only [CollatzResearch.WordTrace]
  refine ⟨132615267732454796644621409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88410178488303197763080939 132615267732454796644621409)
  ·
    refine ⟨99461450799341097483466057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132615267732454796644621409 99461450799341097483466057)
    ·
      refine ⟨74596088099505823112599543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99461450799341097483466057 74596088099505823112599543)
      ·
        refine ⟨111894132149258734668899315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74596088099505823112599543 111894132149258734668899315)
        ·
          refine ⟨167841198223888102003348973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111894132149258734668899315 167841198223888102003348973)
          ·
            refine ⟨62940449333958038251255865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167841198223888102003348973 62940449333958038251255865)
            ·
              refine ⟨47205337000468528688441899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62940449333958038251255865 47205337000468528688441899)
              ·
                refine ⟨70808005500702793032662849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47205337000468528688441899 70808005500702793032662849)
                ·
                  refine ⟨53106004125527094774497137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70808005500702793032662849 53106004125527094774497137)
                  ·
                    refine ⟨39829503094145321080872853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53106004125527094774497137 39829503094145321080872853)
                    ·
                      refine ⟨1867007957538061925665915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39829503094145321080872853 1867007957538061925665915)
                      ·
                        rfl

theorem cell23_3635985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_3635985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635985 prefixEnd_3635985 := by exact prefixLift 3635985
  have htrace : WordTrace (prefixWord ++ tailWord_3635985) baseStart_3635985 baseEnd_3635985 := by
    simpa [prefixWord, tailWord_3635985, baseEnd_3635985] using wordTrace_append hprefix tailTrace_3635985
  have hstable : (prefixWord ++ tailWord_3635985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635985).length < 2 ^ (prefixWord ++ tailWord_3635985).sum := by decide
  have hdescent : baseEnd_3635985 < baseStart_3635985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3635986 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3635986 : Nat := 118140960795 + 3635986 * 2 ^ 59
def prefixEnd_3635986 : Nat := 4983230072969 + 3 ^ 40 * 3635986 * 2
def baseEnd_3635986 : Nat := 622336157006238807251137

theorem tailTrace_3635986 : CollatzResearch.WordTrace tailWord_3635986 prefixEnd_3635986 622336157006238807251137 := by
  unfold tailWord_3635986
  simp only [CollatzResearch.WordTrace]
  refine ⟨33153826051362793453851953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88410202803634115876938541 33153826051362793453851953)
  ·
    refine ⟨24865369538522095090388965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33153826051362793453851953 24865369538522095090388965)
    ·
      refine ⟨4662256788472892829447931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24865369538522095090388965 4662256788472892829447931)
      ·
        refine ⟨6993385182709339244171897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4662256788472892829447931 6993385182709339244171897)
        ·
          refine ⟨5245038887032004433128923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6993385182709339244171897 5245038887032004433128923)
          ·
            refine ⟨7867558330548006649693385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245038887032004433128923 7867558330548006649693385)
            ·
              refine ⟨5900668747911004987270039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7867558330548006649693385 5900668747911004987270039)
              ·
                refine ⟨8851003121866507480905059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5900668747911004987270039 8851003121866507480905059)
                ·
                  refine ⟨13276504682799761221357589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8851003121866507480905059 13276504682799761221357589)
                  ·
                    refine ⟨622336157006238807251137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13276504682799761221357589 622336157006238807251137)
                    ·
                      rfl

theorem cell23_3635986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3635986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3635986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3635986 prefixEnd_3635986 := by exact prefixLift 3635986
  have htrace : WordTrace (prefixWord ++ tailWord_3635986) baseStart_3635986 baseEnd_3635986 := by
    simpa [prefixWord, tailWord_3635986, baseEnd_3635986] using wordTrace_append hprefix tailTrace_3635986
  have hstable : (prefixWord ++ tailWord_3635986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3635986).length < 2 ^ (prefixWord ++ tailWord_3635986).sum := by decide
  have hdescent : baseEnd_3635986 < baseStart_3635986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3635986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636010 : List Nat := [3, 1, 4, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_3636010 : Nat := 118140960795 + 3636010 * 2 ^ 59
def prefixEnd_3636010 : Nat := 4983230072969 + 3 ^ 40 * 3636010 * 2
def baseEnd_3636010 : Nat := 1867020794554424327853301

theorem tailTrace_3636010 : CollatzResearch.WordTrace tailWord_3636010 prefixEnd_3636010 1867020794554424327853301 := by
  unfold tailWord_3636010
  simp only [CollatzResearch.WordTrace]
  refine ⟨33154044889341056478570371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88410786371576150609520989 33154044889341056478570371)
  ·
    refine ⟨49731067334011584717855557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33154044889341056478570371 49731067334011584717855557)
    ·
      refine ⟨9324575125127172134597917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49731067334011584717855557 9324575125127172134597917)
      ·
        refine ⟨3496715671922689550474219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9324575125127172134597917 3496715671922689550474219)
        ·
          refine ⟨5245073507884034325711329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3496715671922689550474219 5245073507884034325711329)
          ·
            refine ⟨3933805130913025744283497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5245073507884034325711329 3933805130913025744283497)
            ·
              refine ⟨2950353848184769308212623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3933805130913025744283497 2950353848184769308212623)
              ·
                refine ⟨4425530772277153962318935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950353848184769308212623 4425530772277153962318935)
                ·
                  refine ⟨6638296158415730943478403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4425530772277153962318935 6638296158415730943478403)
                  ·
                    refine ⟨9957444237623596415217605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6638296158415730943478403 9957444237623596415217605)
                    ·
                      refine ⟨1867020794554424327853301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9957444237623596415217605 1867020794554424327853301)
                      ·
                        rfl

theorem cell23_3636010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_3636010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636010 prefixEnd_3636010 := by exact prefixLift 3636010
  have htrace : WordTrace (prefixWord ++ tailWord_3636010) baseStart_3636010 baseEnd_3636010 := by
    simpa [prefixWord, tailWord_3636010, baseEnd_3636010] using wordTrace_append hprefix tailTrace_3636010
  have hstable : (prefixWord ++ tailWord_3636010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636010).length < 2 ^ (prefixWord ++ tailWord_3636010).sum := by decide
  have hdescent : baseEnd_3636010 < baseStart_3636010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636020 : List Nat := [2, 5, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_3636020 : Nat := 118140960795 + 3636020 * 2 ^ 59
def prefixEnd_3636020 : Nat := 4983230072969 + 3 ^ 40 * 3636020 * 2
def baseEnd_3636020 : Nat := 622341976453656429576085

theorem tailTrace_3636020 : CollatzResearch.WordTrace tailWord_3636020 prefixEnd_3636020 622341976453656429576085 := by
  unfold tailWord_3636020
  simp only [CollatzResearch.WordTrace]
  refine ⟨66308272143663998811072757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88411029524885331748097009 66308272143663998811072757)
  ·
    refine ⟨6216400513468499888538071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66308272143663998811072757 6216400513468499888538071)
    ·
      refine ⟨9324600770202749832807107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6216400513468499888538071 9324600770202749832807107)
      ·
        refine ⟨13986901155304124749210661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9324600770202749832807107 13986901155304124749210661)
        ·
          refine ⟨2622543966619523390476999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13986901155304124749210661 2622543966619523390476999)
          ·
            refine ⟨3933815949929285085715499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622543966619523390476999 3933815949929285085715499)
            ·
              refine ⟨5900723924893927628573249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3933815949929285085715499 5900723924893927628573249)
              ·
                refine ⟨4425542943670445721429937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5900723924893927628573249 4425542943670445721429937)
                ·
                  refine ⟨3319157207752834291072453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4425542943670445721429937 3319157207752834291072453)
                  ·
                    refine ⟨622341976453656429576085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3319157207752834291072453 622341976453656429576085)
                    ·
                      rfl

theorem cell23_3636020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_3636020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636020 prefixEnd_3636020 := by exact prefixLift 3636020
  have htrace : WordTrace (prefixWord ++ tailWord_3636020) baseStart_3636020 baseEnd_3636020 := by
    simpa [prefixWord, tailWord_3636020, baseEnd_3636020] using wordTrace_append hprefix tailTrace_3636020
  have hstable : (prefixWord ++ tailWord_3636020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636020).length < 2 ^ (prefixWord ++ tailWord_3636020).sum := by decide
  have hdescent : baseEnd_3636020 < baseStart_3636020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636026 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3]
def baseStart_3636026 : Nat := 118140960795 + 3636026 * 2 ^ 59
def prefixEnd_3636026 : Nat := 4983230072969 + 3 ^ 40 * 3636026 * 2
def baseEnd_3636026 : Nat := 1867029010244896265253227

theorem tailTrace_3636026 : CollatzResearch.WordTrace tailWord_3636026 prefixEnd_3636026 1867029010244896265253227 := by
  unfold tailWord_3636026
  simp only [CollatzResearch.WordTrace]
  refine ⟨33154190781326565161715983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88411175416870840431242621 33154190781326565161715983)
  ·
    refine ⟨49731286171989847742573975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33154190781326565161715983 49731286171989847742573975)
    ·
      refine ⟨74596929257984771613860963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49731286171989847742573975 74596929257984771613860963)
      ·
        refine ⟨111895393886977157420791445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74596929257984771613860963 111895393886977157420791445)
        ·
          refine ⟨5245096588452054254099599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111895393886977157420791445 5245096588452054254099599)
          ·
            refine ⟨7867644882678081381149399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245096588452054254099599 7867644882678081381149399)
            ·
              refine ⟨11801467324017122071724099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7867644882678081381149399 11801467324017122071724099)
              ·
                refine ⟨17702200986025683107586149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11801467324017122071724099 17702200986025683107586149)
                ·
                  refine ⟨3319162684879815582672403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17702200986025683107586149 3319162684879815582672403)
                  ·
                    refine ⟨4978744027319723374008605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3319162684879815582672403 4978744027319723374008605)
                    ·
                      refine ⟨1867029010244896265253227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4978744027319723374008605 1867029010244896265253227)
                      ·
                        rfl

theorem cell23_3636026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_3636026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636026 prefixEnd_3636026 := by exact prefixLift 3636026
  have htrace : WordTrace (prefixWord ++ tailWord_3636026) baseStart_3636026 baseEnd_3636026 := by
    simpa [prefixWord, tailWord_3636026, baseEnd_3636026] using wordTrace_append hprefix tailTrace_3636026
  have hstable : (prefixWord ++ tailWord_3636026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636026).length < 2 ^ (prefixWord ++ tailWord_3636026).sum := by decide
  have hdescent : baseEnd_3636026 < baseStart_3636026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636089 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 7]
def baseStart_3636089 : Nat := 118140960795 + 3636089 * 2 ^ 59
def prefixEnd_3636089 : Nat := 4983230072969 + 3 ^ 40 * 3636089 * 2
def baseEnd_3636089 : Nat := 207451262169569946529493

theorem tailTrace_3636089 : CollatzResearch.WordTrace tailWord_3636089 prefixEnd_3636089 207451262169569946529493 := by
  unfold tailWord_3636089
  simp only [CollatzResearch.WordTrace]
  refine ⟨132619060924078022406407321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88412707282718681604271547 132619060924078022406407321)
  ·
    refine ⟨99464295693058516804805491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132619060924078022406407321 99464295693058516804805491)
    ·
      refine ⟨149196443539587775207208237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99464295693058516804805491 149196443539587775207208237)
      ·
        refine ⟨55948666327345415702703089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149196443539587775207208237 55948666327345415702703089)
        ·
          refine ⟨41961499745509061777027317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55948666327345415702703089 41961499745509061777027317)
          ·
            refine ⟨3933890601141474541596311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41961499745509061777027317 3933890601141474541596311)
            ·
              refine ⟨5900835901712211812394467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3933890601141474541596311 5900835901712211812394467)
              ·
                refine ⟨8851253852568317718591701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5900835901712211812394467 8851253852568317718591701)
                ·
                  refine ⟨207451262169569946529493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8851253852568317718591701 207451262169569946529493)
                  ·
                    rfl

theorem cell23_3636089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 7].length) (baseStart_3636089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636089 prefixEnd_3636089 := by exact prefixLift 3636089
  have htrace : WordTrace (prefixWord ++ tailWord_3636089) baseStart_3636089 baseEnd_3636089 := by
    simpa [prefixWord, tailWord_3636089, baseEnd_3636089] using wordTrace_append hprefix tailTrace_3636089
  have hstable : (prefixWord ++ tailWord_3636089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636089).length < 2 ^ (prefixWord ++ tailWord_3636089).sum := by decide
  have hdescent : baseEnd_3636089 < baseStart_3636089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636094 : List Nat := [4, 2, 3, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_3636094 : Nat := 118140960795 + 3636094 * 2 ^ 59
def prefixEnd_3636094 : Nat := 4983230072969 + 3 ^ 40 * 3636094 * 2
def baseEnd_3636094 : Nat := 1867063926929401999202915

theorem tailTrace_3636094 : CollatzResearch.WordTrace tailWord_3636094 prefixEnd_3636094 1867063926929401999202915 := by
  unfold tailWord_3636094
  simp only [CollatzResearch.WordTrace]
  refine ⟨16577405411132488532542417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88412828859373272173559557 16577405411132488532542417)
  ·
    refine ⟨12433054058349366399406813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16577405411132488532542417 12433054058349366399406813)
    ·
      refine ⟨4662395271881012399777555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12433054058349366399406813 4662395271881012399777555)
      ·
        refine ⟨6993592907821518599666333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4662395271881012399777555 6993592907821518599666333)
        ·
          refine ⟨2622597340433069474874875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6993592907821518599666333 2622597340433069474874875)
          ·
            refine ⟨3933896010649604212312313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622597340433069474874875 3933896010649604212312313)
            ·
              refine ⟨2950422007987203159234235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3933896010649604212312313 2950422007987203159234235)
              ·
                refine ⟨4425633011980804738851353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950422007987203159234235 4425633011980804738851353)
                ·
                  refine ⟨3319224758985603554138515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4425633011980804738851353 3319224758985603554138515)
                  ·
                    refine ⟨4978837138478405331207773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3319224758985603554138515 4978837138478405331207773)
                    ·
                      refine ⟨1867063926929401999202915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4978837138478405331207773 1867063926929401999202915)
                      ·
                        rfl

theorem cell23_3636094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_3636094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636094 prefixEnd_3636094 := by exact prefixLift 3636094
  have htrace : WordTrace (prefixWord ++ tailWord_3636094) baseStart_3636094 baseEnd_3636094 := by
    simpa [prefixWord, tailWord_3636094, baseEnd_3636094] using wordTrace_append hprefix tailTrace_3636094
  have hstable : (prefixWord ++ tailWord_3636094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636094).length < 2 ^ (prefixWord ++ tailWord_3636094).sum := by decide
  have hdescent : baseEnd_3636094 < baseStart_3636094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636119 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 2, 5]
def baseStart_3636119 : Nat := 118140960795 + 3636119 * 2 ^ 59
def prefixEnd_3636119 : Nat := 4983230072969 + 3 ^ 40 * 3636119 * 2
def baseEnd_3636119 : Nat := 622358921315254800463433

theorem tailTrace_3636119 : CollatzResearch.WordTrace tailWord_3636119 prefixEnd_3636119 622358921315254800463433 := by
  unfold tailWord_3636119
  simp only [CollatzResearch.WordTrace]
  refine ⟨132620155113969337529999411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88413436742646225019999607 132620155113969337529999411)
  ·
    refine ⟨198930232670954006294999117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132620155113969337529999411 198930232670954006294999117)
    ·
      refine ⟨74598837251607752360624669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198930232670954006294999117 74598837251607752360624669)
      ·
        refine ⟨27974563969352907135234251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74598837251607752360624669 27974563969352907135234251)
        ·
          refine ⟨41961845954029360702851377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27974563969352907135234251 41961845954029360702851377)
          ·
            refine ⟨31471384465522020527138533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41961845954029360702851377 31471384465522020527138533)
            ·
              refine ⟨5900884587285378848838475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31471384465522020527138533 5900884587285378848838475)
              ·
                refine ⟨8851326880928068273257713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5900884587285378848838475 8851326880928068273257713)
                ·
                  refine ⟨6638495160696051204943285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8851326880928068273257713 6638495160696051204943285)
                  ·
                    refine ⟨622358921315254800463433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6638495160696051204943285 622358921315254800463433)
                    ·
                      rfl

theorem cell23_3636119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_3636119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636119 prefixEnd_3636119 := by exact prefixLift 3636119
  have htrace : WordTrace (prefixWord ++ tailWord_3636119) baseStart_3636119 baseEnd_3636119 := by
    simpa [prefixWord, tailWord_3636119, baseEnd_3636119] using wordTrace_append hprefix tailTrace_3636119
  have hstable : (prefixWord ++ tailWord_3636119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636119).length < 2 ^ (prefixWord ++ tailWord_3636119).sum := by decide
  have hdescent : baseEnd_3636119 < baseStart_3636119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636129 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3636129 : Nat := 118140960795 + 3636129 * 2 ^ 59
def prefixEnd_3636129 : Nat := 4983230072969 + 3 ^ 40 * 3636129 * 2
def baseEnd_3636129 : Nat := 1867081898752309362265253

theorem tailTrace_3636129 : CollatzResearch.WordTrace tailWord_3636129 prefixEnd_3636129 1867081898752309362265253 := by
  unfold tailWord_3636129
  simp only [CollatzResearch.WordTrace]
  refine ⟨132620519843933109237863441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88413679895955406158575627 132620519843933109237863441)
  ·
    refine ⟨99465389882949831928397581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132620519843933109237863441 99465389882949831928397581)
    ·
      refine ⟨37299521206106186973149093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99465389882949831928397581 37299521206106186973149093)
      ·
        refine ⟨6993660226144910057465455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37299521206106186973149093 6993660226144910057465455)
        ·
          refine ⟨10490490339217365086198183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6993660226144910057465455 10490490339217365086198183)
          ·
            refine ⟨15735735508826047629297275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10490490339217365086198183 15735735508826047629297275)
            ·
              refine ⟨23603603263239071443945913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15735735508826047629297275 23603603263239071443945913)
              ·
                refine ⟨17702702447429303582959435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23603603263239071443945913 17702702447429303582959435)
                ·
                  refine ⟨26554053671143955374439153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17702702447429303582959435 26554053671143955374439153)
                  ·
                    refine ⟨19915540253357966530829365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26554053671143955374439153 19915540253357966530829365)
                    ·
                      refine ⟨1867081898752309362265253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19915540253357966530829365 1867081898752309362265253)
                      ·
                        rfl

theorem cell23_3636129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3636129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636129 prefixEnd_3636129 := by exact prefixLift 3636129
  have htrace : WordTrace (prefixWord ++ tailWord_3636129) baseStart_3636129 baseEnd_3636129 := by
    simpa [prefixWord, tailWord_3636129, baseEnd_3636129] using wordTrace_append hprefix tailTrace_3636129
  have hstable : (prefixWord ++ tailWord_3636129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636129).length < 2 ^ (prefixWord ++ tailWord_3636129).sum := by decide
  have hdescent : baseEnd_3636129 < baseStart_3636129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636139 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 4, 4, 2]
def baseStart_3636139 : Nat := 118140960795 + 3636139 * 2 ^ 59
def prefixEnd_3636139 : Nat := 4983230072969 + 3 ^ 40 * 3636139 * 2
def baseEnd_3636139 : Nat := 1867087033558854323140207

theorem tailTrace_3636139 : CollatzResearch.WordTrace tailWord_3636139 prefixEnd_3636139 1867087033558854323140207 := by
  unfold tailWord_3636139
  simp only [CollatzResearch.WordTrace]
  refine ⟨132620884573896880945727471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88413923049264587297151647 132620884573896880945727471)
  ·
    refine ⟨198931326860845321418591207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132620884573896880945727471 198931326860845321418591207)
    ·
      refine ⟨298396990291267982127886811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198931326860845321418591207 298396990291267982127886811)
      ·
        refine ⟨447595485436901973191830217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298396990291267982127886811 447595485436901973191830217)
        ·
          refine ⟨335696614077676479893872663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447595485436901973191830217 335696614077676479893872663)
          ·
            refine ⟨503544921116514719840808995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335696614077676479893872663 503544921116514719840808995)
            ·
              refine ⟨755317381674772079761213493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503544921116514719840808995 755317381674772079761213493)
              ·
                refine ⟨70811004532009882477613765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 755317381674772079761213493 70811004532009882477613765)
                ·
                  refine ⟨13277063349751852964552581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70811004532009882477613765 13277063349751852964552581)
                  ·
                    refine ⟨2489449378078472430853609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13277063349751852964552581 2489449378078472430853609)
                    ·
                      refine ⟨1867087033558854323140207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2489449378078472430853609 1867087033558854323140207)
                      ·
                        rfl

theorem cell23_3636139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 4, 2].length) (baseStart_3636139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636139 prefixEnd_3636139 := by exact prefixLift 3636139
  have htrace : WordTrace (prefixWord ++ tailWord_3636139) baseStart_3636139 baseEnd_3636139 := by
    simpa [prefixWord, tailWord_3636139, baseEnd_3636139] using wordTrace_append hprefix tailTrace_3636139
  have hstable : (prefixWord ++ tailWord_3636139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636139).length < 2 ^ (prefixWord ++ tailWord_3636139).sum := by decide
  have hdescent : baseEnd_3636139 < baseStart_3636139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636199 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3636199 : Nat := 118140960795 + 3636199 * 2 ^ 59
def prefixEnd_3636199 : Nat := 4983230072969 + 3 ^ 40 * 3636199 * 2
def baseEnd_3636199 : Nat := 1867117842398124088389931

theorem tailTrace_3636199 : CollatzResearch.WordTrace tailWord_3636199 prefixEnd_3636199 1867117842398124088389931 := by
  unfold tailWord_3636199
  simp only [CollatzResearch.WordTrace]
  refine ⟨132623072953679511192911651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88415381969119674128607767 132623072953679511192911651)
  ·
    refine ⟨198934609430519266789367477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132623072953679511192911651 198934609430519266789367477)
    ·
      refine ⟨18650119634111181261503201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198934609430519266789367477 18650119634111181261503201)
      ·
        refine ⟨13987589725583385946127401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18650119634111181261503201 13987589725583385946127401)
        ·
          refine ⟨10490692294187539459595551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13987589725583385946127401 10490692294187539459595551)
          ·
            refine ⟨15736038441281309189393327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10490692294187539459595551 15736038441281309189393327)
            ·
              refine ⟨23604057661921963784089991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15736038441281309189393327 23604057661921963784089991)
              ·
                refine ⟨35406086492882945676134987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23604057661921963784089991 35406086492882945676134987)
                ·
                  refine ⟨53109129739324418514202481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35406086492882945676134987 53109129739324418514202481)
                  ·
                    refine ⟨39831847304493313885651861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53109129739324418514202481 39831847304493313885651861)
                    ·
                      refine ⟨1867117842398124088389931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39831847304493313885651861 1867117842398124088389931)
                      ·
                        rfl

theorem cell23_3636199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3636199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636199 prefixEnd_3636199 := by exact prefixLift 3636199
  have htrace : WordTrace (prefixWord ++ tailWord_3636199) baseStart_3636199 baseEnd_3636199 := by
    simpa [prefixWord, tailWord_3636199, baseEnd_3636199] using wordTrace_append hprefix tailTrace_3636199
  have hstable : (prefixWord ++ tailWord_3636199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636199).length < 2 ^ (prefixWord ++ tailWord_3636199).sum := by decide
  have hdescent : baseEnd_3636199 < baseStart_3636199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636249 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 5]
def baseStart_3636249 : Nat := 118140960795 + 3636249 * 2 ^ 59
def prefixEnd_3636249 : Nat := 4983230072969 + 3 ^ 40 * 3636249 * 2
def baseEnd_3636249 : Nat := 1867143516430848892764701

theorem tailTrace_3636249 : CollatzResearch.WordTrace tailWord_3636249 prefixEnd_3636249 1867143516430848892764701 := by
  unfold tailWord_3636249
  simp only [CollatzResearch.WordTrace]
  refine ⟨132624896603498369732231801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88416597735665579821487867 132624896603498369732231801)
  ·
    refine ⟨99468672452623777299173851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132624896603498369732231801 99468672452623777299173851)
    ·
      refine ⟨149203008678935665948760777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99468672452623777299173851 149203008678935665948760777)
      ·
        refine ⟨111902256509201749461570583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149203008678935665948760777 111902256509201749461570583)
        ·
          refine ⟨167853384763802624192355875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111902256509201749461570583 167853384763802624192355875)
          ·
            refine ⟨251780077145703936288533813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167853384763802624192355875 251780077145703936288533813)
            ·
              refine ⟨23604382232409744027050045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251780077145703936288533813 23604382232409744027050045)
              ·
                refine ⟨8851643337153654010143767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23604382232409744027050045 8851643337153654010143767)
                ·
                  refine ⟨13277465005730481015215651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8851643337153654010143767 13277465005730481015215651)
                  ·
                    refine ⟨19916197508595721522823477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13277465005730481015215651 19916197508595721522823477)
                    ·
                      refine ⟨1867143516430848892764701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19916197508595721522823477 1867143516430848892764701)
                      ·
                        rfl

theorem cell23_3636249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_3636249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636249 prefixEnd_3636249 := by exact prefixLift 3636249
  have htrace : WordTrace (prefixWord ++ tailWord_3636249) baseStart_3636249 baseEnd_3636249 := by
    simpa [prefixWord, tailWord_3636249, baseEnd_3636249] using wordTrace_append hprefix tailTrace_3636249
  have hstable : (prefixWord ++ tailWord_3636249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636249).length < 2 ^ (prefixWord ++ tailWord_3636249).sum := by decide
  have hdescent : baseEnd_3636249 < baseStart_3636249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636257 : List Nat := [1, 2, 3, 2, 3, 2, 3, 2, 1, 1, 3]
def baseStart_3636257 : Nat := 118140960795 + 3636257 * 2 ^ 59
def prefixEnd_3636257 : Nat := 4983230072969 + 3 ^ 40 * 3636257 * 2
def baseEnd_3636257 : Nat := 1867147624276084861464665

theorem tailTrace_3636257 : CollatzResearch.WordTrace tailWord_3636257 prefixEnd_3636257 1867147624276084861464665 := by
  unfold tailWord_3636257
  simp only [CollatzResearch.WordTrace]
  refine ⟨132625188387469387098523025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88416792258312924732348683 132625188387469387098523025)
  ·
    refine ⟨99468891290602040323892269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132625188387469387098523025 99468891290602040323892269)
    ·
      refine ⟨37300834233975765121459601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99468891290602040323892269 37300834233975765121459601)
      ·
        refine ⟨27975625675481823841094701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37300834233975765121459601 27975625675481823841094701)
        ·
          refine ⟨10490859628305683940410513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27975625675481823841094701 10490859628305683940410513)
          ·
            refine ⟨7868144721229262955307885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10490859628305683940410513 7868144721229262955307885)
            ·
              refine ⟨2950554270460973608240457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7868144721229262955307885 2950554270460973608240457)
              ·
                refine ⟨2212915702845730206180343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2950554270460973608240457 2212915702845730206180343)
                ·
                  refine ⟨3319373554268595309270515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212915702845730206180343 3319373554268595309270515)
                  ·
                    refine ⟨4979060331402892963905773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3319373554268595309270515 4979060331402892963905773)
                    ·
                      refine ⟨1867147624276084861464665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4979060331402892963905773 1867147624276084861464665)
                      ·
                        rfl

theorem cell23_3636257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_3636257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636257 prefixEnd_3636257 := by exact prefixLift 3636257
  have htrace : WordTrace (prefixWord ++ tailWord_3636257) baseStart_3636257 baseEnd_3636257 := by
    simpa [prefixWord, tailWord_3636257, baseEnd_3636257] using wordTrace_append hprefix tailTrace_3636257
  have hstable : (prefixWord ++ tailWord_3636257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636257).length < 2 ^ (prefixWord ++ tailWord_3636257).sum := by decide
  have hdescent : baseEnd_3636257 < baseStart_3636257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636259 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 6]
def baseStart_3636259 : Nat := 118140960795 + 3636259 * 2 ^ 59
def prefixEnd_3636259 : Nat := 4983230072969 + 3 ^ 40 * 3636259 * 2
def baseEnd_3636259 : Nat := 1867148651237393853639655

theorem tailTrace_3636259 : CollatzResearch.WordTrace tailWord_3636259 prefixEnd_3636259 1867148651237393853639655 := by
  unfold tailWord_3636259
  simp only [CollatzResearch.WordTrace]
  refine ⟨132625261333462141440095831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88416840888974760960063887 132625261333462141440095831)
  ·
    refine ⟨198937892000193212160143747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132625261333462141440095831 198937892000193212160143747)
    ·
      refine ⟨298406838000289818240215621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198937892000193212160143747 298406838000289818240215621)
      ·
        refine ⟨55951282125054340920040429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298406838000289818240215621 55951282125054340920040429)
        ·
          refine ⟨20981730796895377845015161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55951282125054340920040429 20981730796895377845015161)
          ·
            refine ⟨15736298097671533383761371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20981730796895377845015161 15736298097671533383761371)
            ·
              refine ⟨23604447146507300075642057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15736298097671533383761371 23604447146507300075642057)
              ·
                refine ⟨17703335359880475056731543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23604447146507300075642057 17703335359880475056731543)
                ·
                  refine ⟨26555003039820712585097315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17703335359880475056731543 26555003039820712585097315)
                  ·
                    refine ⟨39832504559731068877645973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26555003039820712585097315 39832504559731068877645973)
                    ·
                      refine ⟨1867148651237393853639655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39832504559731068877645973 1867148651237393853639655)
                      ·
                        rfl

theorem cell23_3636259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_3636259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636259 prefixEnd_3636259 := by exact prefixLift 3636259
  have htrace : WordTrace (prefixWord ++ tailWord_3636259) baseStart_3636259 baseEnd_3636259 := by
    simpa [prefixWord, tailWord_3636259, baseEnd_3636259] using wordTrace_append hprefix tailTrace_3636259
  have hstable : (prefixWord ++ tailWord_3636259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636259).length < 2 ^ (prefixWord ++ tailWord_3636259).sum := by decide
  have hdescent : baseEnd_3636259 < baseStart_3636259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636286 : List Nat := [4, 2, 1, 3, 1, 1, 2, 9]
def baseStart_3636286 : Nat := 118140960795 + 3636286 * 2 ^ 59
def prefixEnd_3636286 : Nat := 4983230072969 + 3 ^ 40 * 3636286 * 2
def baseEnd_3636286 : Nat := 69154167230187601777853

theorem tailTrace_3636286 : CollatzResearch.WordTrace tailWord_3636286 prefixEnd_3636286 69154167230187601777853 := by
  unfold tailWord_3636286
  simp only [CollatzResearch.WordTrace]
  refine ⟨16578280763045540631416089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88417497402909550034219141 16578280763045540631416089)
  ·
    refine ⟨12433710572284155473562067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16578280763045540631416089 12433710572284155473562067)
    ·
      refine ⟨18650565858426233210343101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12433710572284155473562067 18650565858426233210343101)
      ·
        refine ⟨6993962196909837453878663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18650565858426233210343101 6993962196909837453878663)
        ·
          refine ⟨10490943295364756180817995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6993962196909837453878663 10490943295364756180817995)
          ·
            refine ⟨15736414943047134271226993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10490943295364756180817995 15736414943047134271226993)
            ·
              refine ⟨11802311207285350703420245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15736414943047134271226993 11802311207285350703420245)
              ·
                refine ⟨69154167230187601777853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11802311207285350703420245 69154167230187601777853)
                ·
                  rfl

theorem cell23_3636286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_3636286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636286 prefixEnd_3636286 := by exact prefixLift 3636286
  have htrace : WordTrace (prefixWord ++ tailWord_3636286) baseStart_3636286 baseEnd_3636286 := by
    simpa [prefixWord, tailWord_3636286, baseEnd_3636286] using wordTrace_append hprefix tailTrace_3636286
  have hstable : (prefixWord ++ tailWord_3636286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636286).length < 2 ^ (prefixWord ++ tailWord_3636286).sum := by decide
  have hdescent : baseEnd_3636286 < baseStart_3636286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636296 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_3636296 : Nat := 118140960795 + 3636296 * 2 ^ 59
def prefixEnd_3636296 : Nat := 4983230072969 + 3 ^ 40 * 3636296 * 2
def baseEnd_3636296 : Nat := 1867167650021610208876985

theorem tailTrace_3636296 : CollatzResearch.WordTrace tailWord_3636296 prefixEnd_3636296 1867167650021610208876985 := by
  unfold tailWord_3636296
  simp only [CollatzResearch.WordTrace]
  refine ⟨66313305417164048379596371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88417740556218731172795161 66313305417164048379596371)
  ·
    refine ⟨99469958125746072569394557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66313305417164048379596371 99469958125746072569394557)
    ·
      refine ⟨37301234297154777213522959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99469958125746072569394557 37301234297154777213522959)
      ·
        refine ⟨55951851445732165820284439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37301234297154777213522959 55951851445732165820284439)
        ·
          refine ⟨83927777168598248730426659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55951851445732165820284439 83927777168598248730426659)
          ·
            refine ⟨125891665752897373095639989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83927777168598248730426659 125891665752897373095639989)
            ·
              refine ⟨11802343664334128727716249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125891665752897373095639989 11802343664334128727716249)
              ·
                refine ⟨8851757748250596545787187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11802343664334128727716249 8851757748250596545787187)
                ·
                  refine ⟨13277636622375894818680781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8851757748250596545787187 13277636622375894818680781)
                  ·
                    refine ⟨4979113733390960557005293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13277636622375894818680781 4979113733390960557005293)
                    ·
                      refine ⟨1867167650021610208876985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4979113733390960557005293 1867167650021610208876985)
                      ·
                        rfl

theorem cell23_3636296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_3636296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636296 prefixEnd_3636296 := by exact prefixLift 3636296
  have htrace : WordTrace (prefixWord ++ tailWord_3636296) baseStart_3636296 baseEnd_3636296 := by
    simpa [prefixWord, tailWord_3636296, baseEnd_3636296] using wordTrace_append hprefix tailTrace_3636296
  have hstable : (prefixWord ++ tailWord_3636296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636296).length < 2 ^ (prefixWord ++ tailWord_3636296).sum := by decide
  have hdescent : baseEnd_3636296 < baseStart_3636296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636319 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 4]
def baseStart_3636319 : Nat := 118140960795 + 3636319 * 2 ^ 59
def prefixEnd_3636319 : Nat := 4983230072969 + 3 ^ 40 * 3636319 * 2
def baseEnd_3636319 : Nat := 1867179460076663618889379

theorem tailTrace_3636319 : CollatzResearch.WordTrace tailWord_3636319 prefixEnd_3636319 1867179460076663618889379 := by
  unfold tailWord_3636319
  simp only [CollatzResearch.WordTrace]
  refine ⟨132627449713244771687280011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88418299808829847791520007 132627449713244771687280011)
  ·
    refine ⟨198941174569867157530920017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132627449713244771687280011 198941174569867157530920017)
    ·
      refine ⟨149205880927400368148190013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198941174569867157530920017 149205880927400368148190013)
      ·
        refine ⟨55952205347775138055571255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149205880927400368148190013 55952205347775138055571255)
        ·
          refine ⟨83928308021662707083356883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55952205347775138055571255 83928308021662707083356883)
          ·
            refine ⟨125892462032494060625035325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83928308021662707083356883 125892462032494060625035325)
            ·
              refine ⟨47209673262185272734388247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125892462032494060625035325 47209673262185272734388247)
              ·
                refine ⟨70814509893277909101582371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47209673262185272734388247 70814509893277909101582371)
                ·
                  refine ⟨106221764839916863652373557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70814509893277909101582371 106221764839916863652373557)
                  ·
                    refine ⟨9958290453742205967410021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106221764839916863652373557 9958290453742205967410021)
                    ·
                      refine ⟨1867179460076663618889379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9958290453742205967410021 1867179460076663618889379)
                      ·
                        rfl

theorem cell23_3636319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_3636319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636319 prefixEnd_3636319 := by exact prefixLift 3636319
  have htrace : WordTrace (prefixWord ++ tailWord_3636319) baseStart_3636319 baseEnd_3636319 := by
    simpa [prefixWord, tailWord_3636319, baseEnd_3636319] using wordTrace_append hprefix tailTrace_3636319
  have hstable : (prefixWord ++ tailWord_3636319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636319).length < 2 ^ (prefixWord ++ tailWord_3636319).sum := by decide
  have hdescent : baseEnd_3636319 < baseStart_3636319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636329 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 1, 8]
def baseStart_3636329 : Nat := 118140960795 + 3636329 * 2 ^ 59
def prefixEnd_3636329 : Nat := 4983230072969 + 3 ^ 40 * 3636329 * 2
def baseEnd_3636329 : Nat := 622394864961069526588111

theorem tailTrace_3636329 : CollatzResearch.WordTrace tailWord_3636329 prefixEnd_3636329 622394864961069526588111 := by
  unfold tailWord_3636329
  simp only [CollatzResearch.WordTrace]
  refine ⟨132627814443208543395144041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88418542962139028930096027 132627814443208543395144041)
  ·
    refine ⟨99470860832406407546358031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132627814443208543395144041 99470860832406407546358031)
    ·
      refine ⟨149206291248609611319537047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99470860832406407546358031 149206291248609611319537047)
      ·
        refine ⟨223809436872914416979305571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149206291248609611319537047 223809436872914416979305571)
        ·
          refine ⟨335714155309371625468958357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223809436872914416979305571 335714155309371625468958357)
          ·
            refine ⟨15736601030126794943857423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 335714155309371625468958357 15736601030126794943857423)
            ·
              refine ⟨23604901545190192415786135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15736601030126794943857423 23604901545190192415786135)
              ·
                refine ⟨35407352317785288623679203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23604901545190192415786135 35407352317785288623679203)
                ·
                  refine ⟨53111028476677932935518805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35407352317785288623679203 53111028476677932935518805)
                  ·
                    refine ⟨622394864961069526588111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53111028476677932935518805 622394864961069526588111)
                    ·
                      rfl

theorem cell23_3636329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_3636329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636329 prefixEnd_3636329 := by exact prefixLift 3636329
  have htrace : WordTrace (prefixWord ++ tailWord_3636329) baseStart_3636329 baseEnd_3636329 := by
    simpa [prefixWord, tailWord_3636329, baseEnd_3636329] using wordTrace_append hprefix tailTrace_3636329
  have hstable : (prefixWord ++ tailWord_3636329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636329).length < 2 ^ (prefixWord ++ tailWord_3636329).sum := by decide
  have hdescent : baseEnd_3636329 < baseStart_3636329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636330 : List Nat := [3, 1, 3, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_3636330 : Nat := 118140960795 + 3636330 * 2 ^ 59
def prefixEnd_3636330 : Nat := 4983230072969 + 3 ^ 40 * 3636330 * 2
def baseEnd_3636330 : Nat := 1867185108363863075851829

theorem tailTrace_3636330 : CollatzResearch.WordTrace tailWord_3636330 prefixEnd_3636330 1867185108363863075851829 := by
  unfold tailWord_3636330
  simp only [CollatzResearch.WordTrace]
  refine ⟨33156962729051230141482611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88418567277469947043953629 33156962729051230141482611)
  ·
    refine ⟨49735444093576845212223917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33156962729051230141482611 49735444093576845212223917)
    ·
      refine ⟨18650791535091316954583969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49735444093576845212223917 18650791535091316954583969)
      ·
        refine ⟨13988093651318487715937977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18650791535091316954583969 13988093651318487715937977)
        ·
          refine ⟨10491070238488865786953483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13988093651318487715937977 10491070238488865786953483)
          ·
            refine ⟨15736605357733298680430225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10491070238488865786953483 15736605357733298680430225)
            ·
              refine ⟨11802454018299974010322669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15736605357733298680430225 11802454018299974010322669)
              ·
                refine ⟨4425920256862490253871001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11802454018299974010322669 4425920256862490253871001)
                ·
                  refine ⟨3319440192646867690403251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4425920256862490253871001 3319440192646867690403251)
                  ·
                    refine ⟨4979160288970301535604877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3319440192646867690403251 4979160288970301535604877)
                    ·
                      refine ⟨1867185108363863075851829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4979160288970301535604877 1867185108363863075851829)
                      ·
                        rfl

theorem cell23_3636330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_3636330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636330 prefixEnd_3636330 := by exact prefixLift 3636330
  have htrace : WordTrace (prefixWord ++ tailWord_3636330) baseStart_3636330 baseEnd_3636330 := by
    simpa [prefixWord, tailWord_3636330, baseEnd_3636330] using wordTrace_append hprefix tailTrace_3636330
  have hstable : (prefixWord ++ tailWord_3636330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636330).length < 2 ^ (prefixWord ++ tailWord_3636330).sum := by decide
  have hdescent : baseEnd_3636330 < baseStart_3636330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636359 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 11]
def baseStart_3636359 : Nat := 118140960795 + 3636359 * 2 ^ 59
def prefixEnd_3636359 : Nat := 4983230072969 + 3 ^ 40 * 3636359 * 2
def baseEnd_3636359 : Nat := 207466666589204829154355

theorem tailTrace_3636359 : CollatzResearch.WordTrace tailWord_3636359 prefixEnd_3636359 207466666589204829154355 := by
  unfold tailWord_3636359
  simp only [CollatzResearch.WordTrace]
  refine ⟨132628908633099858518736131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88419272422066572345824087 132628908633099858518736131)
  ·
    refine ⟨198943362949649787778104197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132628908633099858518736131 198943362949649787778104197)
    ·
      refine ⟨37301880553059335208394537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198943362949649787778104197 37301880553059335208394537)
      ·
        refine ⟨27976410414794501406295903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37301880553059335208394537 27976410414794501406295903)
        ·
          refine ⟨41964615622191752109443855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27976410414794501406295903 41964615622191752109443855)
          ·
            refine ⟨62946923433287628164165783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41964615622191752109443855 62946923433287628164165783)
            ·
              refine ⟨94420385149931442246248675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62946923433287628164165783 94420385149931442246248675)
              ·
                refine ⟨141630577724897163369373013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94420385149931442246248675 141630577724897163369373013)
                ·
                  refine ⟨207466666589204829154355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 141630577724897163369373013 207466666589204829154355)
                  ·
                    rfl

theorem cell23_3636359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 11].length) (baseStart_3636359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636359 prefixEnd_3636359 := by exact prefixLift 3636359
  have htrace : WordTrace (prefixWord ++ tailWord_3636359) baseStart_3636359 baseEnd_3636359 := by
    simpa [prefixWord, tailWord_3636359, baseEnd_3636359] using wordTrace_append hprefix tailTrace_3636359
  have hstable : (prefixWord ++ tailWord_3636359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636359).length < 2 ^ (prefixWord ++ tailWord_3636359).sum := by decide
  have hdescent : baseEnd_3636359 < baseStart_3636359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636376 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 7]
def baseStart_3636376 : Nat := 118140960795 + 3636376 * 2 ^ 59
def prefixEnd_3636376 : Nat := 4983230072969 + 3 ^ 40 * 3636376 * 2
def baseEnd_3636376 : Nat := 207467636497107766208513

theorem tailTrace_3636376 : CollatzResearch.WordTrace tailWord_3636376 prefixEnd_3636376 207467636497107766208513 := by
  unfold tailWord_3636376
  simp only [CollatzResearch.WordTrace]
  refine ⟨66314764337019135211052491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88419685782692180281403321 66314764337019135211052491)
  ·
    refine ⟨99472146505528702816578737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66314764337019135211052491 99472146505528702816578737)
    ·
      refine ⟨74604109879146527112434053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99472146505528702816578737 74604109879146527112434053)
      ·
        refine ⟨13988270602339973833581385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74604109879146527112434053 13988270602339973833581385)
        ·
          refine ⟨10491202951754980375186039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13988270602339973833581385 10491202951754980375186039)
          ·
            refine ⟨15736804427632470562779059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10491202951754980375186039 15736804427632470562779059)
            ·
              refine ⟨23605206641448705844168589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15736804427632470562779059 23605206641448705844168589)
              ·
                refine ⟨8851952490543264691563221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23605206641448705844168589 8851952490543264691563221)
                ·
                  refine ⟨207467636497107766208513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8851952490543264691563221 207467636497107766208513)
                  ·
                    rfl

theorem cell23_3636376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 7].length) (baseStart_3636376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636376 prefixEnd_3636376 := by exact prefixLift 3636376
  have htrace : WordTrace (prefixWord ++ tailWord_3636376) baseStart_3636376 baseEnd_3636376 := by
    simpa [prefixWord, tailWord_3636376, baseEnd_3636376] using wordTrace_append hprefix tailTrace_3636376
  have hstable : (prefixWord ++ tailWord_3636376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636376).length < 2 ^ (prefixWord ++ tailWord_3636376).sum := by decide
  have hdescent : baseEnd_3636376 < baseStart_3636376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636438 : List Nat := [5, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_3636438 : Nat := 118140960795 + 3636438 * 2 ^ 59
def prefixEnd_3636438 : Nat := 4983230072969 + 3 ^ 40 * 3636438 * 2
def baseEnd_3636438 : Nat := 1867240564274548653301333

theorem tailTrace_3636438 : CollatzResearch.WordTrace tailWord_3636438 prefixEnd_3636438 1867240564274548653301333 := by
  unfold tailWord_3636438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8289486874988353438178873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88421193333209103340574645 8289486874988353438178873)
  ·
    refine ⟨6217115156241265078634155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8289486874988353438178873 6217115156241265078634155)
    ·
      refine ⟨9325672734361897617951233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6217115156241265078634155 9325672734361897617951233)
      ·
        refine ⟨6994254550771423213463425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9325672734361897617951233 6994254550771423213463425)
        ·
          refine ⟨5245690913078567410097569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6994254550771423213463425 5245690913078567410097569)
          ·
            refine ⟨3934268184808925557573177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5245690913078567410097569 3934268184808925557573177)
            ·
              refine ⟨2950701138606694168179883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3934268184808925557573177 2950701138606694168179883)
              ·
                refine ⟨4426051707910041252269825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950701138606694168179883 4426051707910041252269825)
                ·
                  refine ⟨3319538780932530939202369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4426051707910041252269825 3319538780932530939202369)
                  ·
                    refine ⟨2489654085699398204401777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3319538780932530939202369 2489654085699398204401777)
                    ·
                      refine ⟨1867240564274548653301333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2489654085699398204401777 1867240564274548653301333)
                      ·
                        rfl

theorem cell23_3636438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_3636438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636438 prefixEnd_3636438 := by exact prefixLift 3636438
  have htrace : WordTrace (prefixWord ++ tailWord_3636438) baseStart_3636438 baseEnd_3636438 := by
    simpa [prefixWord, tailWord_3636438, baseEnd_3636438] using wordTrace_append hprefix tailTrace_3636438
  have hstable : (prefixWord ++ tailWord_3636438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636438).length < 2 ^ (prefixWord ++ tailWord_3636438).sum := by decide
  have hdescent : baseEnd_3636438 < baseStart_3636438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636483 : List Nat := [1, 1, 1, 3, 2, 5, 2, 2, 6]
def baseStart_3636483 : Nat := 118140960795 + 3636483 * 2 ^ 59
def prefixEnd_3636483 : Nat := 4983230072969 + 3 ^ 40 * 3636483 * 2
def baseEnd_3636483 : Nat := 207473741211555664137625

theorem tailTrace_3636483 : CollatzResearch.WordTrace tailWord_3636483 prefixEnd_3636483 207473741211555664137625 := by
  unfold tailWord_3636483
  simp only [CollatzResearch.WordTrace]
  refine ⟨132633431284650627696250103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88422287523100418464166735 132633431284650627696250103)
  ·
    refine ⟨198950146926975941544375155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132633431284650627696250103 198950146926975941544375155)
    ·
      refine ⟨298425220390463912316562733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198950146926975941544375155 298425220390463912316562733)
      ·
        refine ⟨111909457646423967118711025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298425220390463912316562733 111909457646423967118711025)
        ·
          refine ⟨83932093234817975339033269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111909457646423967118711025 83932093234817975339033269)
          ·
            refine ⟨7868633740764185188034369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83932093234817975339033269 7868633740764185188034369)
            ·
              refine ⟨5901475305573138891025777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7868633740764185188034369 5901475305573138891025777)
              ·
                refine ⟨4426106479179854168269333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5901475305573138891025777 4426106479179854168269333)
                ·
                  refine ⟨207473741211555664137625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4426106479179854168269333 207473741211555664137625)
                  ·
                    rfl

theorem cell23_3636483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 6].length) (baseStart_3636483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636483 prefixEnd_3636483 := by exact prefixLift 3636483
  have htrace : WordTrace (prefixWord ++ tailWord_3636483) baseStart_3636483 baseEnd_3636483 := by
    simpa [prefixWord, tailWord_3636483, baseEnd_3636483] using wordTrace_append hprefix tailTrace_3636483
  have hstable : (prefixWord ++ tailWord_3636483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636483).length < 2 ^ (prefixWord ++ tailWord_3636483).sum := by decide
  have hdescent : baseEnd_3636483 < baseStart_3636483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636513 : List Nat := [1, 2, 3, 2, 1, 1, 1, 6, 1, 5]
def baseStart_3636513 : Nat := 118140960795 + 3636513 * 2 ^ 59
def prefixEnd_3636513 : Nat := 4983230072969 + 3 ^ 40 * 3636513 * 2
def baseEnd_3636513 : Nat := 622426358441211953287829

theorem tailTrace_3636513 : CollatzResearch.WordTrace tailWord_3636513 prefixEnd_3636513 622426358441211953287829 := by
  unfold tailWord_3636513
  simp only [CollatzResearch.WordTrace]
  refine ⟨132634525474541942819842193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88423016983027961879894795 132634525474541942819842193)
  ·
    refine ⟨99475894105906457114881645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132634525474541942819842193 99475894105906457114881645)
    ·
      refine ⟨37303460289714921418080617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99475894105906457114881645 37303460289714921418080617)
      ·
        refine ⟨27977595217286191063560463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37303460289714921418080617 27977595217286191063560463)
        ·
          refine ⟨41966392825929286595340695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27977595217286191063560463 41966392825929286595340695)
          ·
            refine ⟨62949589238893929893011043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41966392825929286595340695 62949589238893929893011043)
            ·
              refine ⟨94424383858340894839516565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62949589238893929893011043 94424383858340894839516565)
              ·
                refine ⟨4426142993359729445602339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94424383858340894839516565 4426142993359729445602339)
                ·
                  refine ⟨6639214490039594168403509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426142993359729445602339 6639214490039594168403509)
                  ·
                    refine ⟨622426358441211953287829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6639214490039594168403509 622426358441211953287829)
                    ·
                      rfl

theorem cell23_3636513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_3636513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636513 prefixEnd_3636513 := by exact prefixLift 3636513
  have htrace : WordTrace (prefixWord ++ tailWord_3636513) baseStart_3636513 baseEnd_3636513 := by
    simpa [prefixWord, tailWord_3636513, baseEnd_3636513] using wordTrace_append hprefix tailTrace_3636513
  have hstable : (prefixWord ++ tailWord_3636513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636513).length < 2 ^ (prefixWord ++ tailWord_3636513).sum := by decide
  have hdescent : baseEnd_3636513 < baseStart_3636513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636514 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_3636514 : Nat := 118140960795 + 3636514 * 2 ^ 59
def prefixEnd_3636514 : Nat := 4983230072969 + 3 ^ 40 * 3636514 * 2
def baseEnd_3636514 : Nat := 1867279588804290355950983

theorem tailTrace_3636514 : CollatzResearch.WordTrace tailWord_3636514 prefixEnd_3636514 1867279588804290355950983 := by
  unfold tailWord_3636514
  simp only [CollatzResearch.WordTrace]
  refine ⟨33158640486884579997657149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88423041298358879993752397 33158640486884579997657149)
  ·
    refine ⟨12434490182581717499121431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33158640486884579997657149 12434490182581717499121431)
    ·
      refine ⟨18651735273872576248682147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12434490182581717499121431 18651735273872576248682147)
      ·
        refine ⟨27977602910808864373023221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18651735273872576248682147 27977602910808864373023221)
        ·
          refine ⟨2622900272888331034970927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27977602910808864373023221 2622900272888331034970927)
          ·
            refine ⟨3934350409332496552456391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622900272888331034970927 3934350409332496552456391)
            ·
              refine ⟨5901525613998744828684587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3934350409332496552456391 5901525613998744828684587)
              ·
                refine ⟨8852288420998117243026881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5901525613998744828684587 8852288420998117243026881)
                ·
                  refine ⟨6639216315748587932270161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8852288420998117243026881 6639216315748587932270161)
                  ·
                    refine ⟨4979412236811440949202621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6639216315748587932270161 4979412236811440949202621)
                    ·
                      refine ⟨1867279588804290355950983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4979412236811440949202621 1867279588804290355950983)
                      ·
                        rfl

theorem cell23_3636514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_3636514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636514 prefixEnd_3636514 := by exact prefixLift 3636514
  have htrace : WordTrace (prefixWord ++ tailWord_3636514) baseStart_3636514 baseEnd_3636514 := by
    simpa [prefixWord, tailWord_3636514, baseEnd_3636514] using wordTrace_append hprefix tailTrace_3636514
  have hstable : (prefixWord ++ tailWord_3636514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636514).length < 2 ^ (prefixWord ++ tailWord_3636514).sum := by decide
  have hdescent : baseEnd_3636514 < baseStart_3636514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636530 : List Nat := [3, 2, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_3636530 : Nat := 118140960795 + 3636530 * 2 ^ 59
def prefixEnd_3636530 : Nat := 4983230072969 + 3 ^ 40 * 3636530 * 2
def baseEnd_3636530 : Nat := 622429268164920764450303

theorem tailTrace_3636530 : CollatzResearch.WordTrace tailWord_3636530 prefixEnd_3636530 622429268164920764450303 := by
  unfold tailWord_3636530
  simp only [CollatzResearch.WordTrace]
  refine ⟨33158786378870088680802761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88423430343653569815474029 33158786378870088680802761)
  ·
    refine ⟨24869089784152566510602071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33158786378870088680802761 24869089784152566510602071)
    ·
      refine ⟨37303634676228849765903107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24869089784152566510602071 37303634676228849765903107)
      ·
        refine ⟨55955452014343274648854661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37303634676228849765903107 55955452014343274648854661)
        ·
          refine ⟨10491647252689363996660249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55955452014343274648854661 10491647252689363996660249)
          ·
            refine ⟨7868735439517022997495187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10491647252689363996660249 7868735439517022997495187)
            ·
              refine ⟨11803103159275534496242781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7868735439517022997495187 11803103159275534496242781)
              ·
                refine ⟨4426163684728325436091043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11803103159275534496242781 4426163684728325436091043)
                ·
                  refine ⟨6639245527092488154136565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426163684728325436091043 6639245527092488154136565)
                  ·
                    refine ⟨622429268164920764450303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6639245527092488154136565 622429268164920764450303)
                    ·
                      rfl

theorem cell23_3636530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_3636530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636530 prefixEnd_3636530 := by exact prefixLift 3636530
  have htrace : WordTrace (prefixWord ++ tailWord_3636530) baseStart_3636530 baseEnd_3636530 := by
    simpa [prefixWord, tailWord_3636530, baseEnd_3636530] using wordTrace_append hprefix tailTrace_3636530
  have hstable : (prefixWord ++ tailWord_3636530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636530).length < 2 ^ (prefixWord ++ tailWord_3636530).sum := by decide
  have hdescent : baseEnd_3636530 < baseStart_3636530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636534 : List Nat := [5, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_3636534 : Nat := 118140960795 + 3636534 * 2 ^ 59
def prefixEnd_3636534 : Nat := 4983230072969 + 3 ^ 40 * 3636534 * 2
def baseEnd_3636534 : Nat := 207476650935264475300099

theorem tailTrace_3636534 : CollatzResearch.WordTrace tailWord_3636534 prefixEnd_3636534 207476650935264475300099 := by
  unfold tailWord_3636534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8289705712966616462897291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88423527604977242270904437 8289705712966616462897291)
  ·
    refine ⟨12434558569449924694345937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8289705712966616462897291 12434558569449924694345937)
    ·
      refine ⟨9325918927087443520759453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12434558569449924694345937 9325918927087443520759453)
      ·
        refine ⟨3497219597657791320284795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9325918927087443520759453 3497219597657791320284795)
        ·
          refine ⟨5245829396486686980427193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3497219597657791320284795 5245829396486686980427193)
          ·
            refine ⟨3934372047365015235320395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5245829396486686980427193 3934372047365015235320395)
            ·
              refine ⟨5901558071047522852980593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3934372047365015235320395 5901558071047522852980593)
              ·
                refine ⟨4426168553285642139735445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5901558071047522852980593 4426168553285642139735445)
                ·
                  refine ⟨207476650935264475300099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4426168553285642139735445 207476650935264475300099)
                  ·
                    rfl

theorem cell23_3636534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_3636534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636534 prefixEnd_3636534 := by exact prefixLift 3636534
  have htrace : WordTrace (prefixWord ++ tailWord_3636534) baseStart_3636534 baseEnd_3636534 := by
    simpa [prefixWord, tailWord_3636534, baseEnd_3636534] using wordTrace_append hprefix tailTrace_3636534
  have hstable : (prefixWord ++ tailWord_3636534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636534).length < 2 ^ (prefixWord ++ tailWord_3636534).sum := by decide
  have hdescent : baseEnd_3636534 < baseStart_3636534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636553 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 5, 2, 3]
def baseStart_3636553 : Nat := 118140960795 + 3636553 * 2 ^ 59
def prefixEnd_3636553 : Nat := 4983230072969 + 3 ^ 40 * 3636553 * 2
def baseEnd_3636553 : Nat := 1867299614549815703363303

theorem tailTrace_3636553 : CollatzResearch.WordTrace tailWord_3636553 prefixEnd_3636553 1867299614549815703363303 := by
  unfold tailWord_3636553
  simp only [CollatzResearch.WordTrace]
  refine ⟨132635984394397029651298313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88423989596264686434198875 132635984394397029651298313)
  ·
    refine ⟨99476988295797772238473735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132635984394397029651298313 99476988295797772238473735)
    ·
      refine ⟨149215482443696658357710603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99476988295797772238473735 149215482443696658357710603)
      ·
        refine ⟨223823223665544987536565905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149215482443696658357710603 223823223665544987536565905)
        ·
          refine ⟨167867417749158740652424429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223823223665544987536565905 167867417749158740652424429)
          ·
            refine ⟨62950281655934527744659161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167867417749158740652424429 62950281655934527744659161)
            ·
              refine ⟨47212711241950895808494371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62950281655934527744659161 47212711241950895808494371)
              ·
                refine ⟨70819066862926343712741557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47212711241950895808494371 70819066862926343712741557)
                ·
                  refine ⟨6639287518399344723069521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70819066862926343712741557 6639287518399344723069521)
                  ·
                    refine ⟨4979465638799508542302141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6639287518399344723069521 4979465638799508542302141)
                    ·
                      refine ⟨1867299614549815703363303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4979465638799508542302141 1867299614549815703363303)
                      ·
                        rfl

theorem cell23_3636553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 2, 3].length) (baseStart_3636553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636553 prefixEnd_3636553 := by exact prefixLift 3636553
  have htrace : WordTrace (prefixWord ++ tailWord_3636553) baseStart_3636553 baseEnd_3636553 := by
    simpa [prefixWord, tailWord_3636553, baseEnd_3636553] using wordTrace_append hprefix tailTrace_3636553
  have hstable : (prefixWord ++ tailWord_3636553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636553).length < 2 ^ (prefixWord ++ tailWord_3636553).sum := by decide
  have hdescent : baseEnd_3636553 < baseStart_3636553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636567 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 3, 2, 2]
def baseStart_3636567 : Nat := 118140960795 + 3636567 * 2 ^ 59
def prefixEnd_3636567 : Nat := 4983230072969 + 3 ^ 40 * 3636567 * 2
def baseEnd_3636567 : Nat := 1867306803278978648588239

theorem tailTrace_3636567 : CollatzResearch.WordTrace tailWord_3636567 prefixEnd_3636567 1867306803278978648588239 := by
  unfold tailWord_3636567
  simp only [CollatzResearch.WordTrace]
  refine ⟨132636495016346310042307955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88424330010897540028205303 132636495016346310042307955)
  ·
    refine ⟨198954742524519465063461933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132636495016346310042307955 198954742524519465063461933)
    ·
      refine ⟨74608028446694799398798225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198954742524519465063461933 74608028446694799398798225)
      ·
        refine ⟨55956021335021099549098669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74608028446694799398798225 55956021335021099549098669)
        ·
          refine ⟨20983508000632912330912001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55956021335021099549098669 20983508000632912330912001)
          ·
            refine ⟨15737631000474684248184001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20983508000632912330912001 15737631000474684248184001)
            ·
              refine ⟨11803223250356013186138001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15737631000474684248184001 11803223250356013186138001)
              ·
                refine ⟨8852417437767009889603501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11803223250356013186138001 8852417437767009889603501)
                ·
                  refine ⟨3319656539162628708601313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8852417437767009889603501 3319656539162628708601313)
                  ·
                    refine ⟨2489742404371971531450985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3319656539162628708601313 2489742404371971531450985)
                    ·
                      refine ⟨1867306803278978648588239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2489742404371971531450985 1867306803278978648588239)
                      ·
                        rfl

theorem cell23_3636567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_3636567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636567 prefixEnd_3636567 := by exact prefixLift 3636567
  have htrace : WordTrace (prefixWord ++ tailWord_3636567) baseStart_3636567 baseEnd_3636567 := by
    simpa [prefixWord, tailWord_3636567, baseEnd_3636567] using wordTrace_append hprefix tailTrace_3636567
  have hstable : (prefixWord ++ tailWord_3636567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636567).length < 2 ^ (prefixWord ++ tailWord_3636567).sum := by decide
  have hdescent : baseEnd_3636567 < baseStart_3636567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636570 : List Nat := [3, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3]
def baseStart_3636570 : Nat := 118140960795 + 3636570 * 2 ^ 59
def prefixEnd_3636570 : Nat := 4983230072969 + 3 ^ 40 * 3636570 * 2
def baseEnd_3636570 : Nat := 1867308343720942136850725

theorem tailTrace_3636570 : CollatzResearch.WordTrace tailWord_3636570 prefixEnd_3636570 1867308343720942136850725 := by
  unfold tailWord_3636570
  simp only [CollatzResearch.WordTrace]
  refine ⟨33159151108833860388666791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88424402956890294369778109 33159151108833860388666791)
  ·
    refine ⟨49738726663250790583000187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33159151108833860388666791 49738726663250790583000187)
    ·
      refine ⟨74608089994876185874500281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49738726663250790583000187 74608089994876185874500281)
      ·
        refine ⟨55956067496157139405875211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74608089994876185874500281 55956067496157139405875211)
        ·
          refine ⟨83934101244235709108812817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55956067496157139405875211 83934101244235709108812817)
          ·
            refine ⟨62950575933176781831609613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83934101244235709108812817 62950575933176781831609613)
            ·
              refine ⟨23606465974941293186853605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62950575933176781831609613 23606465974941293186853605)
              ·
                refine ⟨4426212370301492472535051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23606465974941293186853605 4426212370301492472535051)
                ·
                  refine ⟨6639318555452238708802577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426212370301492472535051 6639318555452238708802577)
                  ·
                    refine ⟨4979488916589179031601933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6639318555452238708802577 4979488916589179031601933)
                    ·
                      refine ⟨1867308343720942136850725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4979488916589179031601933 1867308343720942136850725)
                      ·
                        rfl

theorem cell23_3636570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_3636570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636570 prefixEnd_3636570 := by exact prefixLift 3636570
  have htrace : WordTrace (prefixWord ++ tailWord_3636570) baseStart_3636570 baseEnd_3636570 := by
    simpa [prefixWord, tailWord_3636570, baseEnd_3636570] using wordTrace_append hprefix tailTrace_3636570
  have hstable : (prefixWord ++ tailWord_3636570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636570).length < 2 ^ (prefixWord ++ tailWord_3636570).sum := by decide
  have hdescent : baseEnd_3636570 < baseStart_3636570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636643 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 5]
def baseStart_3636643 : Nat := 118140960795 + 3636643 * 2 ^ 59
def prefixEnd_3636643 : Nat := 4983230072969 + 3 ^ 40 * 3636643 * 2
def baseEnd_3636643 : Nat := 1867345827808720351237889

theorem tailTrace_3636643 : CollatzResearch.WordTrace tailWord_3636643 prefixEnd_3636643 1867345827808720351237889 := by
  unfold tailWord_3636643
  simp only [CollatzResearch.WordTrace]
  refine ⟨132639266964070975022074583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88426177976047316681383055 132639266964070975022074583)
  ·
    refine ⟨198958900446106462533111875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132639266964070975022074583 198958900446106462533111875)
    ·
      refine ⟨298438350669159693799667813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198958900446106462533111875 298438350669159693799667813)
      ·
        refine ⟨55957190750467442587437715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298438350669159693799667813 55957190750467442587437715)
        ·
          refine ⟨83935786125701163881156573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55957190750467442587437715 83935786125701163881156573)
          ·
            refine ⟨31475919797137936455433715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83935786125701163881156573 31475919797137936455433715)
            ·
              refine ⟨47213879695706904683150573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31475919797137936455433715 47213879695706904683150573)
              ·
                refine ⟨17705204885890089256181465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47213879695706904683150573 17705204885890089256181465)
                ·
                  refine ⟨13278903664417566942136099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17705204885890089256181465 13278903664417566942136099)
                  ·
                    refine ⟨19918355496626350413204149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13278903664417566942136099 19918355496626350413204149)
                    ·
                      refine ⟨1867345827808720351237889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19918355496626350413204149 1867345827808720351237889)
                      ·
                        rfl

theorem cell23_3636643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_3636643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636643 prefixEnd_3636643 := by exact prefixLift 3636643
  have htrace : WordTrace (prefixWord ++ tailWord_3636643) baseStart_3636643 baseEnd_3636643 := by
    simpa [prefixWord, tailWord_3636643, baseEnd_3636643] using wordTrace_append hprefix tailTrace_3636643
  have hstable : (prefixWord ++ tailWord_3636643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636643).length < 2 ^ (prefixWord ++ tailWord_3636643).sum := by decide
  have hdescent : baseEnd_3636643 < baseStart_3636643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636663 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 7]
def baseStart_3636663 : Nat := 118140960795 + 3636663 * 2 ^ 59
def prefixEnd_3636663 : Nat := 4983230072969 + 3 ^ 40 * 3636663 * 2
def baseEnd_3636663 : Nat := 207484010824645585887533

theorem tailTrace_3636663 : CollatzResearch.WordTrace tailWord_3636663 prefixEnd_3636663 207484010824645585887533 := by
  unfold tailWord_3636663
  simp only [CollatzResearch.WordTrace]
  refine ⟨132639996423998518437802643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88426664282665678958535095 132639996423998518437802643)
  ·
    refine ⟨198959994635997777656703965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132639996423998518437802643 198959994635997777656703965)
    ·
      refine ⟨74609997988499166621263987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198959994635997777656703965 74609997988499166621263987)
      ·
        refine ⟨111914996982748749931895981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74609997988499166621263987 111914996982748749931895981)
        ·
          refine ⟨41968123868530781224460993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111914996982748749931895981 41968123868530781224460993)
          ·
            refine ⟨31476092901398085918345745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41968123868530781224460993 31476092901398085918345745)
            ·
              refine ⟨23607069676048564438759309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31476092901398085918345745 23607069676048564438759309)
              ·
                refine ⟨8852651128518211664534741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23607069676048564438759309 8852651128518211664534741)
                ·
                  refine ⟨207484010824645585887533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8852651128518211664534741 207484010824645585887533)
                  ·
                    rfl

theorem cell23_3636663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 7].length) (baseStart_3636663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636663 prefixEnd_3636663 := by exact prefixLift 3636663
  have htrace : WordTrace (prefixWord ++ tailWord_3636663) baseStart_3636663 baseEnd_3636663 := by
    simpa [prefixWord, tailWord_3636663, baseEnd_3636663] using wordTrace_append hprefix tailTrace_3636663
  have hstable : (prefixWord ++ tailWord_3636663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636663).length < 2 ^ (prefixWord ++ tailWord_3636663).sum := by decide
  have hdescent : baseEnd_3636663 < baseStart_3636663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636697 : List Nat := [1, 2, 1, 2, 4, 3, 2, 3, 5]
def baseStart_3636697 : Nat := 118140960795 + 3636697 * 2 ^ 59
def prefixEnd_3636697 : Nat := 4983230072969 + 3 ^ 40 * 3636697 * 2
def baseEnd_3636697 : Nat := 207485950640451459995849

theorem tailTrace_3636697 : CollatzResearch.WordTrace tailWord_3636697 prefixEnd_3636697 207485950640451459995849 := by
  unfold tailWord_3636697
  simp only [CollatzResearch.WordTrace]
  refine ⟨132641236505875342244540345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88427491003916894829693563 132641236505875342244540345)
  ·
    refine ⟨99480927379406506683405259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132641236505875342244540345 99480927379406506683405259)
    ·
      refine ⟨149221391069109760025107889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99480927379406506683405259 149221391069109760025107889)
      ·
        refine ⟨111916043301832320018830917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149221391069109760025107889 111916043301832320018830917)
        ·
          refine ⟨20984258119093560003530797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111916043301832320018830917 20984258119093560003530797)
          ·
            refine ⟨7869096794660085001324049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20984258119093560003530797 7869096794660085001324049)
            ·
              refine ⟨5901822595995063750993037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7869096794660085001324049 5901822595995063750993037)
              ·
                refine ⟨2213183473498148906622389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5901822595995063750993037 2213183473498148906622389)
                ·
                  refine ⟨207485950640451459995849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2213183473498148906622389 207485950640451459995849)
                  ·
                    rfl

theorem cell23_3636697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 5].length) (baseStart_3636697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636697 prefixEnd_3636697 := by exact prefixLift 3636697
  have htrace : WordTrace (prefixWord ++ tailWord_3636697) baseStart_3636697 baseEnd_3636697 := by
    simpa [prefixWord, tailWord_3636697, baseEnd_3636697] using wordTrace_append hprefix tailTrace_3636697
  have hstable : (prefixWord ++ tailWord_3636697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636697).length < 2 ^ (prefixWord ++ tailWord_3636697).sum := by decide
  have hdescent : baseEnd_3636697 < baseStart_3636697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636753 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 10]
def baseStart_3636753 : Nat := 118140960795 + 3636753 * 2 ^ 59
def prefixEnd_3636753 : Nat := 4983230072969 + 3 ^ 40 * 3636753 * 2
def baseEnd_3636753 : Nat := 207489145631190546762487

theorem tailTrace_3636753 : CollatzResearch.WordTrace tailWord_3636753 prefixEnd_3636753 207489145631190546762487 := by
  unfold tailWord_3636753
  simp only [CollatzResearch.WordTrace]
  refine ⟨132643278993672463808578913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88428852662448309205719275 132643278993672463808578913)
  ·
    refine ⟨99482459245254347856434185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132643278993672463808578913 99482459245254347856434185)
    ·
      refine ⟨74611844433940760892325639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99482459245254347856434185 74611844433940760892325639)
      ·
        refine ⟨111917766650911141338488459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74611844433940760892325639 111917766650911141338488459)
        ·
          refine ⟨167876649976366712007732689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111917766650911141338488459 167876649976366712007732689)
          ·
            refine ⟨125907487482275034005799517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167876649976366712007732689 125907487482275034005799517)
            ·
              refine ⟨47215307805853137752174819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125907487482275034005799517 47215307805853137752174819)
              ·
                refine ⟨70822961708779706628262229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47215307805853137752174819 70822961708779706628262229)
                ·
                  refine ⟨207489145631190546762487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 70822961708779706628262229 207489145631190546762487)
                  ·
                    rfl

theorem cell23_3636753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 10].length) (baseStart_3636753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636753 prefixEnd_3636753 := by exact prefixLift 3636753
  have htrace : WordTrace (prefixWord ++ tailWord_3636753) baseStart_3636753 baseEnd_3636753 := by
    simpa [prefixWord, tailWord_3636753, baseEnd_3636753] using wordTrace_append hprefix tailTrace_3636753
  have hstable : (prefixWord ++ tailWord_3636753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636753).length < 2 ^ (prefixWord ++ tailWord_3636753).sum := by decide
  have hdescent : baseEnd_3636753 < baseStart_3636753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636770 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 8]
def baseStart_3636770 : Nat := 118140960795 + 3636770 * 2 ^ 59
def prefixEnd_3636770 : Nat := 4983230072969 + 3 ^ 40 * 3636770 * 2
def baseEnd_3636770 : Nat := 207490115539093483816645

theorem tailTrace_3636770 : CollatzResearch.WordTrace tailWord_3636770 prefixEnd_3636770 207490115539093483816645 := by
  unfold tailWord_3636770
  simp only [CollatzResearch.WordTrace]
  refine ⟨33160974758652718927986941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88429266023073917141298509 33160974758652718927986941)
  ·
    refine ⟨12435365534494769597995103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33160974758652718927986941 12435365534494769597995103)
    ·
      refine ⟨18653048301742154396992655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12435365534494769597995103 18653048301742154396992655)
      ·
        refine ⟨27979572452613231595488983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18653048301742154396992655 27979572452613231595488983)
        ·
          refine ⟨41969358678919847393233475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27979572452613231595488983 41969358678919847393233475)
          ·
            refine ⟨62954038018379771089850213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41969358678919847393233475 62954038018379771089850213)
            ·
              refine ⟨11803882128446207079346915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62954038018379771089850213 11803882128446207079346915)
              ·
                refine ⟨17705823192669310619020373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11803882128446207079346915 17705823192669310619020373)
                ·
                  refine ⟨207490115539093483816645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17705823192669310619020373 207490115539093483816645)
                  ·
                    rfl

theorem cell23_3636770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_3636770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636770 prefixEnd_3636770 := by exact prefixLift 3636770
  have htrace : WordTrace (prefixWord ++ tailWord_3636770) baseStart_3636770 baseEnd_3636770 := by
    simpa [prefixWord, tailWord_3636770, baseEnd_3636770] using wordTrace_append hprefix tailTrace_3636770
  have hstable : (prefixWord ++ tailWord_3636770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636770).length < 2 ^ (prefixWord ++ tailWord_3636770).sum := by decide
  have hdescent : baseEnd_3636770 < baseStart_3636770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636787 : List Nat := [1, 1, 1, 2, 4, 3, 4, 1, 6]
def baseStart_3636787 : Nat := 118140960795 + 3636787 * 2 ^ 59
def prefixEnd_3636787 : Nat := 4983230072969 + 3 ^ 40 * 3636787 * 2
def baseEnd_3636787 : Nat := 207491085446996420870803

theorem tailTrace_3636787 : CollatzResearch.WordTrace tailWord_3636787 prefixEnd_3636787 207491085446996420870803 := by
  unfold tailWord_3636787
  simp only [CollatzResearch.WordTrace]
  refine ⟨132644519075549287615316615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88429679383699525076877743 132644519075549287615316615)
  ·
    refine ⟨198966778613323931422974923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132644519075549287615316615 198966778613323931422974923)
    ·
      refine ⟨298450167919985897134462385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198966778613323931422974923 298450167919985897134462385)
      ·
        refine ⟨223837625939989422850846789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298450167919985897134462385 223837625939989422850846789)
        ·
          refine ⟨41969554863748016784533773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223837625939989422850846789 41969554863748016784533773)
          ·
            refine ⟨15738583073905506294200165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41969554863748016784533773 15738583073905506294200165)
            ·
              refine ⟨2950984326357282430162531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15738583073905506294200165 2950984326357282430162531)
              ·
                refine ⟨4426476489535923645243797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950984326357282430162531 4426476489535923645243797)
                ·
                  refine ⟨207491085446996420870803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4426476489535923645243797 207491085446996420870803)
                  ·
                    rfl

theorem cell23_3636787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 6].length) (baseStart_3636787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636787 prefixEnd_3636787 := by exact prefixLift 3636787
  have htrace : WordTrace (prefixWord ++ tailWord_3636787) baseStart_3636787 baseEnd_3636787 := by
    simpa [prefixWord, tailWord_3636787, baseEnd_3636787] using wordTrace_append hprefix tailTrace_3636787
  have hstable : (prefixWord ++ tailWord_3636787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636787).length < 2 ^ (prefixWord ++ tailWord_3636787).sum := by decide
  have hdescent : baseEnd_3636787 < baseStart_3636787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636837 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_3636837 : Nat := 118140960795 + 3636837 * 2 ^ 59
def prefixEnd_3636837 : Nat := 4983230072969 + 3 ^ 40 * 3636837 * 2
def baseEnd_3636837 : Nat := 1867445443055692592211997

theorem tailTrace_3636837 : CollatzResearch.WordTrace tailWord_3636837 prefixEnd_3636837 1867445443055692592211997 := by
  unfold tailWord_3636837
  simp only [CollatzResearch.WordTrace]
  refine ⟨132646342725368146154636765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88430895150245430769757843 132646342725368146154636765)
  ·
    refine ⟨49742378522013054807988787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132646342725368146154636765 49742378522013054807988787)
    ·
      refine ⟨74613567783019582211983181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49742378522013054807988787 74613567783019582211983181)
      ·
        refine ⟨27980087918632343329493693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74613567783019582211983181 27980087918632343329493693)
        ·
          refine ⟨10492532969487128748560135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27980087918632343329493693 10492532969487128748560135)
          ·
            refine ⟨15738799454230693122840203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10492532969487128748560135 15738799454230693122840203)
            ·
              refine ⟨23608199181346039684260305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15738799454230693122840203 23608199181346039684260305)
              ·
                refine ⟨17706149386009529763195229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23608199181346039684260305 17706149386009529763195229)
                ·
                  refine ⟨6639806019753573661198211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17706149386009529763195229 6639806019753573661198211)
                  ·
                    refine ⟨9959709029630360491797317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6639806019753573661198211 9959709029630360491797317)
                    ·
                      refine ⟨1867445443055692592211997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9959709029630360491797317 1867445443055692592211997)
                      ·
                        rfl

theorem cell23_3636837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_3636837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636837 prefixEnd_3636837 := by exact prefixLift 3636837
  have htrace : WordTrace (prefixWord ++ tailWord_3636837) baseStart_3636837 baseEnd_3636837 := by
    simpa [prefixWord, tailWord_3636837, baseEnd_3636837] using wordTrace_append hprefix tailTrace_3636837
  have hstable : (prefixWord ++ tailWord_3636837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636837).length < 2 ^ (prefixWord ++ tailWord_3636837).sum := by decide
  have hdescent : baseEnd_3636837 < baseStart_3636837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636854 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3636854 : Nat := 118140960795 + 3636854 * 2 ^ 59
def prefixEnd_3636854 : Nat := 4983230072969 + 3 ^ 40 * 3636854 * 2
def baseEnd_3636854 : Nat := 1867454172226819025699419

theorem tailTrace_3636854 : CollatzResearch.WordTrace tailWord_3636854 prefixEnd_3636854 1867454172226819025699419 := by
  unfold tailWord_3636854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8290435172894159878625351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88431308510871038705337077 8290435172894159878625351)
  ·
    refine ⟨12435652759341239817938027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8290435172894159878625351 12435652759341239817938027)
    ·
      refine ⟨18653479139011859726907041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12435652759341239817938027 18653479139011859726907041)
      ·
        refine ⟨13990109354258894795180281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18653479139011859726907041 13990109354258894795180281)
        ·
          refine ⟨10492582015694171096385211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13990109354258894795180281 10492582015694171096385211)
          ·
            refine ⟨15738873023541256644577817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10492582015694171096385211 15738873023541256644577817)
            ·
              refine ⟨11804154767655942483433363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15738873023541256644577817 11804154767655942483433363)
              ·
                refine ⟨17706232151483913725150045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11804154767655942483433363 17706232151483913725150045)
                ·
                  refine ⟨6639837056806467646931267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17706232151483913725150045 6639837056806467646931267)
                  ·
                    refine ⟨9959755585209701470396901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6639837056806467646931267 9959755585209701470396901)
                    ·
                      refine ⟨1867454172226819025699419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9959755585209701470396901 1867454172226819025699419)
                      ·
                        rfl

theorem cell23_3636854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3636854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636854 prefixEnd_3636854 := by exact prefixLift 3636854
  have htrace : WordTrace (prefixWord ++ tailWord_3636854) baseStart_3636854 baseEnd_3636854 := by
    simpa [prefixWord, tailWord_3636854, baseEnd_3636854] using wordTrace_append hprefix tailTrace_3636854
  have hstable : (prefixWord ++ tailWord_3636854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636854).length < 2 ^ (prefixWord ++ tailWord_3636854).sum := by decide
  have hdescent : baseEnd_3636854 < baseStart_3636854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636857 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 3, 2, 3]
def baseStart_3636857 : Nat := 118140960795 + 3636857 * 2 ^ 59
def prefixEnd_3636857 : Nat := 4983230072969 + 3 ^ 40 * 3636857 * 2
def baseEnd_3636857 : Nat := 1867455712668782513961905

theorem tailTrace_3636857 : CollatzResearch.WordTrace tailWord_3636857 prefixEnd_3636857 1867455712668782513961905 := by
  unfold tailWord_3636857
  simp only [CollatzResearch.WordTrace]
  refine ⟨132647072185295689570364825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88431381456863793046909883 132647072185295689570364825)
  ·
    refine ⟨99485304138971767177773619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132647072185295689570364825 99485304138971767177773619)
    ·
      refine ⟨149227956208457650766660429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99485304138971767177773619 149227956208457650766660429)
      ·
        refine ⟨55960483578171619037497661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149227956208457650766660429 55960483578171619037497661)
        ·
          refine ⟨20985181341814357139061623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55960483578171619037497661 20985181341814357139061623)
          ·
            refine ⟨31477772012721535708592435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20985181341814357139061623 31477772012721535708592435)
            ·
              refine ⟨47216658019082303562888653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31477772012721535708592435 47216658019082303562888653)
              ·
                refine ⟨17706246757155863836083245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47216658019082303562888653 17706246757155863836083245)
                ·
                  refine ⟨6639842533933448938531217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17706246757155863836083245 6639842533933448938531217)
                  ·
                    refine ⟨4979881900450086703898413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6639842533933448938531217 4979881900450086703898413)
                    ·
                      refine ⟨1867455712668782513961905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4979881900450086703898413 1867455712668782513961905)
                      ·
                        rfl

theorem cell23_3636857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_3636857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636857 prefixEnd_3636857 := by exact prefixLift 3636857
  have htrace : WordTrace (prefixWord ++ tailWord_3636857) baseStart_3636857 baseEnd_3636857 := by
    simpa [prefixWord, tailWord_3636857, baseEnd_3636857] using wordTrace_append hprefix tailTrace_3636857
  have hstable : (prefixWord ++ tailWord_3636857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636857).length < 2 ^ (prefixWord ++ tailWord_3636857).sum := by decide
  have hdescent : baseEnd_3636857 < baseStart_3636857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636868 : List Nat := [2, 3, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_3636868 : Nat := 118140960795 + 3636868 * 2 ^ 59
def prefixEnd_3636868 : Nat := 4983230072969 + 3 ^ 40 * 3636868 * 2
def baseEnd_3636868 : Nat := 622487120318660656974785

theorem tailTrace_3636868 : CollatzResearch.WordTrace tailWord_3636868 prefixEnd_3636868 622487120318660656974785 := by
  unfold tailWord_3636868
  simp only [CollatzResearch.WordTrace]
  refine ⟨66323736694127919224507629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88431648925503892299343505 66323736694127919224507629)
  ·
    refine ⟨24871401260297969709190361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66323736694127919224507629 24871401260297969709190361)
    ·
      refine ⟨18653550945223477281892771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24871401260297969709190361 18653550945223477281892771)
      ·
        refine ⟨27980326417835215922839157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18653550945223477281892771 27980326417835215922839157)
        ·
          refine ⟨2623155601672051492766171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27980326417835215922839157 2623155601672051492766171)
          ·
            refine ⟨3934733402508077239149257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623155601672051492766171 3934733402508077239149257)
            ·
              refine ⟨2951050051881057929361943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3934733402508077239149257 2951050051881057929361943)
              ·
                refine ⟨4426575077821586894042915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2951050051881057929361943 4426575077821586894042915)
                ·
                  refine ⟨6639862616732380341064373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426575077821586894042915 6639862616732380341064373)
                  ·
                    refine ⟨622487120318660656974785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6639862616732380341064373 622487120318660656974785)
                    ·
                      rfl

theorem cell23_3636868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_3636868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636868 prefixEnd_3636868 := by exact prefixLift 3636868
  have htrace : WordTrace (prefixWord ++ tailWord_3636868) baseStart_3636868 baseEnd_3636868 := by
    simpa [prefixWord, tailWord_3636868, baseEnd_3636868] using wordTrace_append hprefix tailTrace_3636868
  have hstable : (prefixWord ++ tailWord_3636868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636868).length < 2 ^ (prefixWord ++ tailWord_3636868).sum := by decide
  have hdescent : baseEnd_3636868 < baseStart_3636868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636871 : List Nat := [1, 1, 4, 2, 1, 5, 2, 1, 1, 1, 4]
def baseStart_3636871 : Nat := 118140960795 + 3636871 * 2 ^ 59
def prefixEnd_3636871 : Nat := 4983230072969 + 3 ^ 40 * 3636871 * 2
def baseEnd_3636871 : Nat := 1867462901397945459186841

theorem tailTrace_3636871 : CollatzResearch.WordTrace tailWord_3636871 prefixEnd_3636871 1867462901397945459186841 := by
  unfold tailWord_3636871
  simp only [CollatzResearch.WordTrace]
  refine ⟨132647582807244969961374467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88431721871496646640916311 132647582807244969961374467)
  ·
    refine ⟨198971374210867454942061701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132647582807244969961374467 198971374210867454942061701)
    ·
      refine ⟨37307132664537647801636569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198971374210867454942061701 37307132664537647801636569)
      ·
        refine ⟨27980349498403235851227427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37307132664537647801636569 27980349498403235851227427)
        ·
          refine ⟨41970524247604853776841141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27980349498403235851227427 41970524247604853776841141)
          ·
            refine ⟨3934736648212955041578857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41970524247604853776841141 3934736648212955041578857)
            ·
              refine ⟨2951052486159716281184143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3934736648212955041578857 2951052486159716281184143)
              ·
                refine ⟨4426578729239574421776215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2951052486159716281184143 4426578729239574421776215)
                ·
                  refine ⟨6639868093859361632664323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426578729239574421776215 6639868093859361632664323)
                  ·
                    refine ⟨9959802140789042448996485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6639868093859361632664323 9959802140789042448996485)
                    ·
                      refine ⟨1867462901397945459186841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9959802140789042448996485 1867462901397945459186841)
                      ·
                        rfl

theorem cell23_3636871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_3636871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636871 prefixEnd_3636871 := by exact prefixLift 3636871
  have htrace : WordTrace (prefixWord ++ tailWord_3636871) baseStart_3636871 baseEnd_3636871 := by
    simpa [prefixWord, tailWord_3636871, baseEnd_3636871] using wordTrace_append hprefix tailTrace_3636871
  have hstable : (prefixWord ++ tailWord_3636871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636871).length < 2 ^ (prefixWord ++ tailWord_3636871).sum := by decide
  have hdescent : baseEnd_3636871 < baseStart_3636871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636888 : List Nat := [2, 1, 2, 4, 1, 2, 2, 4, 1, 2, 2]
def baseStart_3636888 : Nat := 118140960795 + 3636888 * 2 ^ 59
def prefixEnd_3636888 : Nat := 4983230072969 + 3 ^ 40 * 3636888 * 2
def baseEnd_3636888 : Nat := 1867471630569071892674263

theorem tailTrace_3636888 : CollatzResearch.WordTrace tailWord_3636888 prefixEnd_3636888 1867471630569071892674263 := by
  unfold tailWord_3636888
  simp only [CollatzResearch.WordTrace]
  refine ⟨66324101424091690932371659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88432135232122254576495545 66324101424091690932371659)
  ·
    refine ⟨99486152136137536398557489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66324101424091690932371659 99486152136137536398557489)
    ·
      refine ⟨74614614102103152298918117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99486152136137536398557489 74614614102103152298918117)
      ·
        refine ⟨13990240144144341056047147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74614614102103152298918117 13990240144144341056047147)
        ·
          refine ⟨20985360216216511584070721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13990240144144341056047147 20985360216216511584070721)
          ·
            refine ⟨15739020162162383688053041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20985360216216511584070721 15739020162162383688053041)
            ·
              refine ⟨11804265121621787766039781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15739020162162383688053041 11804265121621787766039781)
              ·
                refine ⟨2213299710304085206132459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11804265121621787766039781 2213299710304085206132459)
                ·
                  refine ⟨3319949565456127809198689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213299710304085206132459 3319949565456127809198689)
                  ·
                    refine ⟨2489962174092095856899017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3319949565456127809198689 2489962174092095856899017)
                    ·
                      refine ⟨1867471630569071892674263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2489962174092095856899017 1867471630569071892674263)
                      ·
                        rfl

theorem cell23_3636888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_3636888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636888 prefixEnd_3636888 := by exact prefixLift 3636888
  have htrace : WordTrace (prefixWord ++ tailWord_3636888) baseStart_3636888 baseEnd_3636888 := by
    simpa [prefixWord, tailWord_3636888, baseEnd_3636888] using wordTrace_append hprefix tailTrace_3636888
  have hstable : (prefixWord ++ tailWord_3636888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636888).length < 2 ^ (prefixWord ++ tailWord_3636888).sum := by decide
  have hdescent : baseEnd_3636888 < baseStart_3636888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636898 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_3636898 : Nat := 118140960795 + 3636898 * 2 ^ 59
def prefixEnd_3636898 : Nat := 4983230072969 + 3 ^ 40 * 3636898 * 2
def baseEnd_3636898 : Nat := 622492255125205617849739

theorem tailTrace_3636898 : CollatzResearch.WordTrace tailWord_3636898 prefixEnd_3636898 622492255125205617849739 := by
  unfold tailWord_3636898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33162141894536788393151837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88432378385431435715071565 33162141894536788393151837)
  ·
    refine ⟨12435803210451295647431939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33162141894536788393151837 12435803210451295647431939)
    ·
      refine ⟨18653704815676943471147909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12435803210451295647431939 18653704815676943471147909)
      ·
        refine ⟨3497569652939426900840233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18653704815676943471147909 3497569652939426900840233)
        ·
          refine ⟨2623177239704570175630175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3497569652939426900840233 2623177239704570175630175)
          ·
            refine ⟨3934765859556855263445263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623177239704570175630175 3934765859556855263445263)
            ·
              refine ⟨5902148789335282895167895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3934765859556855263445263 5902148789335282895167895)
              ·
                refine ⟨8853223184002924342751843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5902148789335282895167895 8853223184002924342751843)
                ·
                  refine ⟨13279834776004386514127765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8853223184002924342751843 13279834776004386514127765)
                  ·
                    refine ⟨622492255125205617849739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13279834776004386514127765 622492255125205617849739)
                    ·
                      rfl

theorem cell23_3636898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_3636898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636898 prefixEnd_3636898 := by exact prefixLift 3636898
  have htrace : WordTrace (prefixWord ++ tailWord_3636898) baseStart_3636898 baseEnd_3636898 := by
    simpa [prefixWord, tailWord_3636898, baseEnd_3636898] using wordTrace_append hprefix tailTrace_3636898
  have hstable : (prefixWord ++ tailWord_3636898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636898).length < 2 ^ (prefixWord ++ tailWord_3636898).sum := by decide
  have hdescent : baseEnd_3636898 < baseStart_3636898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636914 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2]
def baseStart_3636914 : Nat := 118140960795 + 3636914 * 2 ^ 59
def prefixEnd_3636914 : Nat := 4983230072969 + 3 ^ 40 * 3636914 * 2
def baseEnd_3636914 : Nat := 1867484981066088790949143

theorem tailTrace_3636914 : CollatzResearch.WordTrace tailWord_3636914 prefixEnd_3636914 1867484981066088790949143 := by
  unfold tailWord_3636914
  simp only [CollatzResearch.WordTrace]
  refine ⟨33162287786522297076297449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88432767430726125536793197 33162287786522297076297449)
  ·
    refine ⟨24871715839891722807223087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33162287786522297076297449 24871715839891722807223087)
    ·
      refine ⟨37307573759837584210834631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24871715839891722807223087 37307573759837584210834631)
      ·
        refine ⟨55961360639756376316251947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37307573759837584210834631 55961360639756376316251947)
        ·
          refine ⟨83942040959634564474377921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55961360639756376316251947 83942040959634564474377921)
          ·
            refine ⟨62956530719725923355783441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83942040959634564474377921 62956530719725923355783441)
            ·
              refine ⟨47217398039794442516837581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62956530719725923355783441 47217398039794442516837581)
              ·
                refine ⟨17706524264922915943814093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47217398039794442516837581 17706524264922915943814093)
                ·
                  refine ⟨6639946599346093478930285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17706524264922915943814093 6639946599346093478930285)
                  ·
                    refine ⟨2489979974754785054598857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6639946599346093478930285 2489979974754785054598857)
                    ·
                      refine ⟨1867484981066088790949143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2489979974754785054598857 1867484981066088790949143)
                      ·
                        rfl

theorem cell23_3636914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_3636914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636914 prefixEnd_3636914 := by exact prefixLift 3636914
  have htrace : WordTrace (prefixWord ++ tailWord_3636914) baseStart_3636914 baseEnd_3636914 := by
    simpa [prefixWord, tailWord_3636914, baseEnd_3636914] using wordTrace_append hprefix tailTrace_3636914
  have hstable : (prefixWord ++ tailWord_3636914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636914).length < 2 ^ (prefixWord ++ tailWord_3636914).sum := by decide
  have hdescent : baseEnd_3636914 < baseStart_3636914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3636920 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 1, 8]
def baseStart_3636920 : Nat := 118140960795 + 3636920 * 2 ^ 59
def prefixEnd_3636920 : Nat := 4983230072969 + 3 ^ 40 * 3636920 * 2
def baseEnd_3636920 : Nat := 622496020650005255824705

theorem tailTrace_3636920 : CollatzResearch.WordTrace tailWord_3636920 prefixEnd_3636920 622496020650005255824705 := by
  unfold tailWord_3636920
  simp only [CollatzResearch.WordTrace]
  refine ⟨66324684992033725664954107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88432913322711634219938809 66324684992033725664954107)
  ·
    refine ⟨99487027488050588497431161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66324684992033725664954107 99487027488050588497431161)
    ·
      refine ⟨74615270616037941373073371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99487027488050588497431161 74615270616037941373073371)
      ·
        refine ⟨111922905924056912059610057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74615270616037941373073371 111922905924056912059610057)
        ·
          refine ⟨83942179443042684044707543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111922905924056912059610057 83942179443042684044707543)
          ·
            refine ⟨125913269164564026067061315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83942179443042684044707543 125913269164564026067061315)
            ·
              refine ⟨188869903746846039100591973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125913269164564026067061315 188869903746846039100591973)
              ·
                refine ⟨35413106952533632331360995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188869903746846039100591973 35413106952533632331360995)
                ·
                  refine ⟨53119660428800448497041493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35413106952533632331360995 53119660428800448497041493)
                  ·
                    refine ⟨622496020650005255824705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53119660428800448497041493 622496020650005255824705)
                    ·
                      rfl

theorem cell23_3636920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_3636920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3636920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3636920 prefixEnd_3636920 := by exact prefixLift 3636920
  have htrace : WordTrace (prefixWord ++ tailWord_3636920) baseStart_3636920 baseEnd_3636920 := by
    simpa [prefixWord, tailWord_3636920, baseEnd_3636920] using wordTrace_append hprefix tailTrace_3636920
  have hstable : (prefixWord ++ tailWord_3636920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3636920).length < 2 ^ (prefixWord ++ tailWord_3636920).sum := by decide
  have hdescent : baseEnd_3636920 < baseStart_3636920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3636920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637004 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 2, 5, 2]
def baseStart_3637004 : Nat := 118140960795 + 3637004 * 2 ^ 59
def prefixEnd_3637004 : Nat := 4983230072969 + 3 ^ 40 * 3637004 * 2
def baseEnd_3637004 : Nat := 1867531194324993438823729

theorem tailTrace_3637004 : CollatzResearch.WordTrace tailWord_3637004 prefixEnd_3637004 1867531194324993438823729 := by
  unfold tailWord_3637004
  simp only [CollatzResearch.WordTrace]
  refine ⟨66326216857881566837983033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88434955810508755783977377 66326216857881566837983033)
  ·
    refine ⟨49744662643411175128487275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66326216857881566837983033 49744662643411175128487275)
    ·
      refine ⟨74616993965116762692730913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49744662643411175128487275 74616993965116762692730913)
      ·
        refine ⟨55962745473837572019548185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74616993965116762692730913 55962745473837572019548185)
        ·
          refine ⟨41972059105378179014661139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55962745473837572019548185 41972059105378179014661139)
          ·
            refine ⟨62958088658067268521991709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41972059105378179014661139 62958088658067268521991709)
            ·
              refine ⟨23609283246775225695746891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62958088658067268521991709 23609283246775225695746891)
              ·
                refine ⟨35413924870162838543620337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23609283246775225695746891 35413924870162838543620337)
                ·
                  refine ⟨26560443652622128907715253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35413924870162838543620337 26560443652622128907715253)
                  ·
                    refine ⟨2490041592433324585098305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26560443652622128907715253 2490041592433324585098305)
                    ·
                      refine ⟨1867531194324993438823729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2490041592433324585098305 1867531194324993438823729)
                      ·
                        rfl

theorem cell23_3637004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_3637004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637004 prefixEnd_3637004 := by exact prefixLift 3637004
  have htrace : WordTrace (prefixWord ++ tailWord_3637004) baseStart_3637004 baseEnd_3637004 := by
    simpa [prefixWord, tailWord_3637004, baseEnd_3637004] using wordTrace_append hprefix tailTrace_3637004
  have hstable : (prefixWord ++ tailWord_3637004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637004).length < 2 ^ (prefixWord ++ tailWord_3637004).sum := by decide
  have hdescent : baseEnd_3637004 < baseStart_3637004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637005 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3637005 : Nat := 118140960795 + 3637005 * 2 ^ 59
def prefixEnd_3637005 : Nat := 4983230072969 + 3 ^ 40 * 3637005 * 2
def baseEnd_3637005 : Nat := 622510569268549311637075

theorem tailTrace_3637005 : CollatzResearch.WordTrace tailWord_3637005 prefixEnd_3637005 622510569268549311637075 := by
  unfold tailWord_3637005
  simp only [CollatzResearch.WordTrace]
  refine ⟨132652470188759510846752469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88434980125839673897834979 132652470188759510846752469)
  ·
    refine ⟨3109042270049051035470761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 132652470188759510846752469 3109042270049051035470761)
    ·
      refine ⟨2331781702536788276603071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3109042270049051035470761 2331781702536788276603071)
      ·
        refine ⟨3497672553805182414904607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2331781702536788276603071 3497672553805182414904607)
        ·
          refine ⟨5246508830707773622356911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3497672553805182414904607 5246508830707773622356911)
          ·
            refine ⟨7869763246061660433535367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5246508830707773622356911 7869763246061660433535367)
            ·
              refine ⟨11804644869092490650303051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7869763246061660433535367 11804644869092490650303051)
              ·
                refine ⟨17706967303638735975454577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11804644869092490650303051 17706967303638735975454577)
                ·
                  refine ⟨13280225477729051981590933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17706967303638735975454577 13280225477729051981590933)
                  ·
                    refine ⟨622510569268549311637075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13280225477729051981590933 622510569268549311637075)
                    ·
                      rfl

theorem cell23_3637005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3637005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637005 prefixEnd_3637005 := by exact prefixLift 3637005
  have htrace : WordTrace (prefixWord ++ tailWord_3637005) baseStart_3637005 baseEnd_3637005 := by
    simpa [prefixWord, tailWord_3637005, baseEnd_3637005] using wordTrace_append hprefix tailTrace_3637005
  have hstable : (prefixWord ++ tailWord_3637005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637005).length < 2 ^ (prefixWord ++ tailWord_3637005).sum := by decide
  have hdescent : baseEnd_3637005 < baseStart_3637005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637012 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3637012 : Nat := 118140960795 + 3637012 * 2 ^ 59
def prefixEnd_3637012 : Nat := 4983230072969 + 3 ^ 40 * 3637012 * 2
def baseEnd_3637012 : Nat := 1867535302170229407523693

theorem tailTrace_3637012 : CollatzResearch.WordTrace tailWord_3637012 prefixEnd_3637012 1867535302170229407523693 := by
  unfold tailWord_3637012
  simp only [CollatzResearch.WordTrace]
  refine ⟨66326362749867075521128645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88435150333156100694838193 66326362749867075521128645)
  ·
    refine ⟨12436193015600076660211621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66326362749867075521128645 12436193015600076660211621)
    ·
      refine ⟨2331786190425014373789679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12436193015600076660211621 2331786190425014373789679)
      ·
        refine ⟨3497679285637521560684519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2331786190425014373789679 3497679285637521560684519)
        ·
          refine ⟨5246518928456282341026779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3497679285637521560684519 5246518928456282341026779)
          ·
            refine ⟨7869778392684423511540169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5246518928456282341026779 7869778392684423511540169)
            ·
              refine ⟨5902333794513317633655127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7869778392684423511540169 5902333794513317633655127)
              ·
                refine ⟨8853500691769976450482691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5902333794513317633655127 8853500691769976450482691)
                ·
                  refine ⟨13280251037654964675724037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8853500691769976450482691 13280251037654964675724037)
                  ·
                    refine ⟨2490047069560305876698257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13280251037654964675724037 2490047069560305876698257)
                    ·
                      refine ⟨1867535302170229407523693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2490047069560305876698257 1867535302170229407523693)
                      ·
                        rfl

theorem cell23_3637012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3637012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637012 prefixEnd_3637012 := by exact prefixLift 3637012
  have htrace : WordTrace (prefixWord ++ tailWord_3637012) baseStart_3637012 baseEnd_3637012 := by
    simpa [prefixWord, tailWord_3637012, baseEnd_3637012] using wordTrace_append hprefix tailTrace_3637012
  have hstable : (prefixWord ++ tailWord_3637012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637012).length < 2 ^ (prefixWord ++ tailWord_3637012).sum := by decide
  have hdescent : baseEnd_3637012 < baseStart_3637012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637061 : List Nat := [1, 3, 1, 1, 1, 2, 3, 6, 1, 4]
def baseStart_3637061 : Nat := 118140960795 + 3637061 * 2 ^ 59
def prefixEnd_3637061 : Nat := 4983230072969 + 3 ^ 40 * 3637061 * 2
def baseEnd_3637061 : Nat := 622520154240766571936989

theorem tailTrace_3637061 : CollatzResearch.WordTrace tailWord_3637061 prefixEnd_3637061 622520154240766571936989 := by
  unfold tailWord_3637061
  simp only [CollatzResearch.WordTrace]
  refine ⟨132654512676556632410791037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88436341784371088273860691 132654512676556632410791037)
  ·
    refine ⟨49745442253708737154046639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132654512676556632410791037 49745442253708737154046639)
    ·
      refine ⟨74618163380563105731069959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49745442253708737154046639 74618163380563105731069959)
      ·
        refine ⟨111927245070844658596604939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74618163380563105731069959 111927245070844658596604939)
        ·
          refine ⟨167890867606266987894907409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111927245070844658596604939 167890867606266987894907409)
          ·
            refine ⟨125918150704700240921180557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167890867606266987894907409 125918150704700240921180557)
            ·
              refine ⟨47219306514262590345442709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125918150704700240921180557 47219306514262590345442709)
              ·
                refine ⟨2213404992856058922442627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47219306514262590345442709 2213404992856058922442627)
                ·
                  refine ⟨3320107489284088383663941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213404992856058922442627 3320107489284088383663941)
                  ·
                    refine ⟨622520154240766571936989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3320107489284088383663941 622520154240766571936989)
                    ·
                      rfl

theorem cell23_3637061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_3637061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637061 prefixEnd_3637061 := by exact prefixLift 3637061
  have htrace : WordTrace (prefixWord ++ tailWord_3637061) baseStart_3637061 baseEnd_3637061 := by
    simpa [prefixWord, tailWord_3637061, baseEnd_3637061] using wordTrace_append hprefix tailTrace_3637061
  have hstable : (prefixWord ++ tailWord_3637061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637061).length < 2 ^ (prefixWord ++ tailWord_3637061).sum := by decide
  have hdescent : baseEnd_3637061 < baseStart_3637061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
