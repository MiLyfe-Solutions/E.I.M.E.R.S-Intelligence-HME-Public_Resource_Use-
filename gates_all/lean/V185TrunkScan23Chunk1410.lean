import V185TrunkScan23Chunk1409

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8352100 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_8352100 : Nat := 118140960795 + 8352100 * 2 ^ 59
def prefixEnd_8352100 : Nat := 4983230072969 + 3 ^ 40 * 8352100 * 2
def baseEnd_8352100 : Nat := 4288641774416877604039397

theorem tailTrace_8352100 : CollatzResearch.WordTrace tailWord_8352100 prefixEnd_8352100 4288641774416877604039397 := by
  unfold tailWord_8352100
  simp only [CollatzResearch.WordTrace]
  refine ⟨152313056520887799980802877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203084075361183733307737169 152313056520887799980802877)
  ·
    refine ⟨57117396195332924992801079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152313056520887799980802877 57117396195332924992801079)
    ·
      refine ⟨85676094292999387489201619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57117396195332924992801079 85676094292999387489201619)
      ·
        refine ⟨128514141439499081233802429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85676094292999387489201619 128514141439499081233802429)
        ·
          refine ⟨48192803039812155462675911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128514141439499081233802429 48192803039812155462675911)
          ·
            refine ⟨72289204559718233194013867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48192803039812155462675911 72289204559718233194013867)
            ·
              refine ⟨108433806839577349791020801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72289204559718233194013867 108433806839577349791020801)
              ·
                refine ⟨81325355129683012343265601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108433806839577349791020801 81325355129683012343265601)
                ·
                  refine ⟨60994016347262259257449201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81325355129683012343265601 60994016347262259257449201)
                  ·
                    refine ⟨45745512260446694443086901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60994016347262259257449201 45745512260446694443086901)
                    ·
                      refine ⟨4288641774416877604039397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45745512260446694443086901 4288641774416877604039397)
                      ·
                        rfl

theorem cell23_8352100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_8352100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352100 prefixEnd_8352100 := by exact prefixLift 8352100
  have htrace : WordTrace (prefixWord ++ tailWord_8352100) baseStart_8352100 baseEnd_8352100 := by
    simpa [prefixWord, tailWord_8352100, baseEnd_8352100] using wordTrace_append hprefix tailTrace_8352100
  have hstable : (prefixWord ++ tailWord_8352100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352100).length < 2 ^ (prefixWord ++ tailWord_8352100).sum := by decide
  have hdescent : baseEnd_8352100 < baseStart_8352100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352104 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_8352104 : Nat := 118140960795 + 8352104 * 2 ^ 59
def prefixEnd_8352104 : Nat := 4983230072969 + 3 ^ 40 * 8352104 * 2
def baseEnd_8352104 : Nat := 4288643828339495588389379

theorem tailTrace_8352104 : CollatzResearch.WordTrace tailWord_8352104 prefixEnd_8352104 4288643828339495588389379 := by
  unfold tailWord_8352104
  simp only [CollatzResearch.WordTrace]
  refine ⟨152313129466880554322375683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203084172622507405763167577 152313129466880554322375683)
  ·
    refine ⟨228469694200320831483563525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152313129466880554322375683 228469694200320831483563525)
    ·
      refine ⟨42838067662560155903168161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228469694200320831483563525 42838067662560155903168161)
      ·
        refine ⟨32128550746920116927376121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42838067662560155903168161 32128550746920116927376121)
        ·
          refine ⟨24096413060190087695532091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32128550746920116927376121 24096413060190087695532091)
          ·
            refine ⟨36144619590285131543298137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24096413060190087695532091 36144619590285131543298137)
            ·
              refine ⟨27108464692713848657473603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36144619590285131543298137 27108464692713848657473603)
              ·
                refine ⟨40662697039070772986210405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27108464692713848657473603 40662697039070772986210405)
                ·
                  refine ⟨7624255694825769934914451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40662697039070772986210405 7624255694825769934914451)
                  ·
                    refine ⟨11436383542238654902371677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7624255694825769934914451 11436383542238654902371677)
                    ·
                      refine ⟨4288643828339495588389379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11436383542238654902371677 4288643828339495588389379)
                      ·
                        rfl

theorem cell23_8352104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_8352104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352104 prefixEnd_8352104 := by exact prefixLift 8352104
  have htrace : WordTrace (prefixWord ++ tailWord_8352104) baseStart_8352104 baseEnd_8352104 := by
    simpa [prefixWord, tailWord_8352104, baseEnd_8352104] using wordTrace_append hprefix tailTrace_8352104
  have hstable : (prefixWord ++ tailWord_8352104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352104).length < 2 ^ (prefixWord ++ tailWord_8352104).sum := by decide
  have hdescent : baseEnd_8352104 < baseStart_8352104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352177 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 1, 5, 3]
def baseStart_8352177 : Nat := 118140960795 + 8352177 * 2 ^ 59
def prefixEnd_8352177 : Nat := 4983230072969 + 3 ^ 40 * 8352177 * 2
def baseEnd_8352177 : Nat := 4288681312427273802776543

theorem tailTrace_8352177 : CollatzResearch.WordTrace tailWord_8352177 prefixEnd_8352177 4288681312427273802776543 := by
  unfold tailWord_8352177
  simp only [CollatzResearch.WordTrace]
  refine ⟨304628921462496642112158785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203085947641664428074772523 304628921462496642112158785)
  ·
    refine ⟨228471691096872481584119089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304628921462496642112158785 228471691096872481584119089)
    ·
      refine ⟨171353768322654361188089317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228471691096872481584119089 171353768322654361188089317)
      ·
        refine ⟨32128831560497692722766747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171353768322654361188089317 32128831560497692722766747)
        ·
          refine ⟨48193247340746539084150121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32128831560497692722766747 48193247340746539084150121)
          ·
            refine ⟨36144935505559904313112591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48193247340746539084150121 36144935505559904313112591)
            ·
              refine ⟨54217403258339856469668887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36144935505559904313112591 54217403258339856469668887)
              ·
                refine ⟨81326104887509784704503331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54217403258339856469668887 81326104887509784704503331)
                ·
                  refine ⟨121989157331264677056754997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81326104887509784704503331 121989157331264677056754997)
                  ·
                    refine ⟨11436483499806063474070781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121989157331264677056754997 11436483499806063474070781)
                    ·
                      refine ⟨4288681312427273802776543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11436483499806063474070781 4288681312427273802776543)
                      ·
                        rfl

theorem cell23_8352177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_8352177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352177 prefixEnd_8352177 := by exact prefixLift 8352177
  have htrace : WordTrace (prefixWord ++ tailWord_8352177) baseStart_8352177 baseEnd_8352177 := by
    simpa [prefixWord, tailWord_8352177, baseEnd_8352177] using wordTrace_append hprefix tailTrace_8352177
  have hstable : (prefixWord ++ tailWord_8352177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352177).length < 2 ^ (prefixWord ++ tailWord_8352177).sum := by decide
  have hdescent : baseEnd_8352177 < baseStart_8352177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352214 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_8352214 : Nat := 118140960795 + 8352214 * 2 ^ 59
def prefixEnd_8352214 : Nat := 4983230072969 + 3 ^ 40 * 8352214 * 2
def baseEnd_8352214 : Nat := 1429566770403830052671291

theorem tailTrace_8352214 : CollatzResearch.WordTrace tailWord_8352214 prefixEnd_8352214 1429566770403830052671291 := by
  unfold tailWord_8352214
  simp only [CollatzResearch.WordTrace]
  refine ⟨19039391935210162339453481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203086847308908398287503797 19039391935210162339453481)
  ·
    refine ⟨14279543951407621754590111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19039391935210162339453481 14279543951407621754590111)
    ·
      refine ⟨21419315927111432631885167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14279543951407621754590111 21419315927111432631885167)
      ·
        refine ⟨32128973890667148947827751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21419315927111432631885167 32128973890667148947827751)
        ·
          refine ⟨48193460836000723421741627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32128973890667148947827751 48193460836000723421741627)
          ·
            refine ⟨72290191254001085132612441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48193460836000723421741627 72290191254001085132612441)
            ·
              refine ⟨54217643440500813849459331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72290191254001085132612441 54217643440500813849459331)
              ·
                refine ⟨81326465160751220774188997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54217643440500813849459331 81326465160751220774188997)
                ·
                  refine ⟨15248712217640853895160437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81326465160751220774188997 15248712217640853895160437)
                  ·
                    refine ⟨1429566770403830052671291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15248712217640853895160437 1429566770403830052671291)
                    ·
                      rfl

theorem cell23_8352214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_8352214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352214 prefixEnd_8352214 := by exact prefixLift 8352214
  have htrace : WordTrace (prefixWord ++ tailWord_8352214) baseStart_8352214 baseEnd_8352214 := by
    simpa [prefixWord, tailWord_8352214, baseEnd_8352214] using wordTrace_append hprefix tailTrace_8352214
  have hstable : (prefixWord ++ tailWord_8352214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352214).length < 2 ^ (prefixWord ++ tailWord_8352214).sum := by decide
  have hdescent : baseEnd_8352214 < baseStart_8352214 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352217 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 4, 1, 4]
def baseStart_8352217 : Nat := 118140960795 + 8352217 * 2 ^ 59
def prefixEnd_8352217 : Nat := 4983230072969 + 3 ^ 40 * 8352217 * 2
def baseEnd_8352217 : Nat := 4288701851653453646276359

theorem tailTrace_8352217 : CollatzResearch.WordTrace tailWord_8352217 prefixEnd_8352217 4288701851653453646276359 := by
  unfold tailWord_8352217
  simp only [CollatzResearch.WordTrace]
  refine ⟨304630380382351728943614905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203086920254901152629076603 304630380382351728943614905)
  ·
    refine ⟨228472785286763796707711179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304630380382351728943614905 228472785286763796707711179)
    ·
      refine ⟨342709177930145695061566769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228472785286763796707711179 342709177930145695061566769)
      ·
        refine ⟨257031883447609271296175077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342709177930145695061566769 257031883447609271296175077)
        ·
          refine ⟨48193478146426738368032827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257031883447609271296175077 48193478146426738368032827)
          ·
            refine ⟨72290217219640107552049241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48193478146426738368032827 72290217219640107552049241)
            ·
              refine ⟨54217662914730080664036931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72290217219640107552049241 54217662914730080664036931)
              ·
                refine ⟨81326494372095120996055397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54217662914730080664036931 81326494372095120996055397)
                ·
                  refine ⟨15248717694767835186760387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81326494372095120996055397 15248717694767835186760387)
                  ·
                    refine ⟨22873076542151752780140581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15248717694767835186760387 22873076542151752780140581)
                    ·
                      refine ⟨4288701851653453646276359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22873076542151752780140581 4288701851653453646276359)
                      ·
                        rfl

theorem cell23_8352217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_8352217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352217 prefixEnd_8352217 := by exact prefixLift 8352217
  have htrace : WordTrace (prefixWord ++ tailWord_8352217) baseStart_8352217 baseEnd_8352217 := by
    simpa [prefixWord, tailWord_8352217, baseEnd_8352217] using wordTrace_append hprefix tailTrace_8352217
  have hstable : (prefixWord ++ tailWord_8352217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352217).length < 2 ^ (prefixWord ++ tailWord_8352217).sum := by decide
  have hdescent : baseEnd_8352217 < baseStart_8352217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352257 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 8]
def baseStart_8352257 : Nat := 118140960795 + 8352257 * 2 ^ 59
def prefixEnd_8352257 : Nat := 4983230072969 + 3 ^ 40 * 8352257 * 2
def baseEnd_8352257 : Nat := 476524710097737054419575

theorem tailTrace_8352257 : CollatzResearch.WordTrace tailWord_8352257 prefixEnd_8352257 476524710097737054419575 := by
  unfold tailWord_8352257
  simp only [CollatzResearch.WordTrace]
  refine ⟨304631839302206815775071025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203087892868137877183380683 304631839302206815775071025)
  ·
    refine ⟨228473879476655111831303269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304631839302206815775071025 228473879476655111831303269)
    ·
      refine ⟨42838852401872833468369363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228473879476655111831303269 42838852401872833468369363)
      ·
        refine ⟨64258278602809250202554045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42838852401872833468369363 64258278602809250202554045)
        ·
          refine ⟨24096854476053468825957767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64258278602809250202554045 24096854476053468825957767)
          ·
            refine ⟨36145281714080203238936651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24096854476053468825957767 36145281714080203238936651)
            ·
              refine ⟨54217922571120304858404977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36145281714080203238936651 54217922571120304858404977)
              ·
                refine ⟨40663441928340228643803733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54217922571120304858404977 40663441928340228643803733)
                ·
                  refine ⟨476524710097737054419575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40663441928340228643803733 476524710097737054419575)
                  ·
                    rfl

theorem cell23_8352257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 8].length) (baseStart_8352257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352257 prefixEnd_8352257 := by exact prefixLift 8352257
  have htrace : WordTrace (prefixWord ++ tailWord_8352257) baseStart_8352257 baseEnd_8352257 := by
    simpa [prefixWord, tailWord_8352257, baseEnd_8352257] using wordTrace_append hprefix tailTrace_8352257
  have hstable : (prefixWord ++ tailWord_8352257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352257).length < 2 ^ (prefixWord ++ tailWord_8352257).sum := by decide
  have hdescent : baseEnd_8352257 < baseStart_8352257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352261 : List Nat := [1, 3, 1, 1, 2, 2, 5, 3, 1, 4]
def baseStart_8352261 : Nat := 118140960795 + 8352261 * 2 ^ 59
def prefixEnd_8352261 : Nat := 4983230072969 + 3 ^ 40 * 8352261 * 2
def baseEnd_8352261 : Nat := 1429574814934083824708719

theorem tailTrace_8352261 : CollatzResearch.WordTrace tailWord_8352261 prefixEnd_8352261 1429574814934083824708719 := by
  unfold tailWord_8352261
  simp only [CollatzResearch.WordTrace]
  refine ⟨304631985194192324458216637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203087990129461549638811091 304631985194192324458216637)
  ·
    refine ⟨114236994447822121671831239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304631985194192324458216637 114236994447822121671831239)
    ·
      refine ⟨171355491671733182507746859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114236994447822121671831239 171355491671733182507746859)
      ·
        refine ⟨257033237507599773761620289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171355491671733182507746859 257033237507599773761620289)
        ·
          refine ⟨192774928130699830321215217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257033237507599773761620289 192774928130699830321215217)
          ·
            refine ⟨144581196098024872740911413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192774928130699830321215217 144581196098024872740911413)
            ·
              refine ⟨13554487134189831819460445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144581196098024872740911413 13554487134189831819460445)
              ·
                refine ⟨5082932675321186932297667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13554487134189831819460445 5082932675321186932297667)
                ·
                  refine ⟨7624399012981780398446501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5082932675321186932297667 7624399012981780398446501)
                  ·
                    refine ⟨1429574814934083824708719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7624399012981780398446501 1429574814934083824708719)
                    ·
                      rfl

theorem cell23_8352261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_8352261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352261 prefixEnd_8352261 := by exact prefixLift 8352261
  have htrace : WordTrace (prefixWord ++ tailWord_8352261) baseStart_8352261 baseEnd_8352261 := by
    simpa [prefixWord, tailWord_8352261, baseEnd_8352261] using wordTrace_append hprefix tailTrace_8352261
  have hstable : (prefixWord ++ tailWord_8352261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352261).length < 2 ^ (prefixWord ++ tailWord_8352261).sum := by decide
  have hdescent : baseEnd_8352261 < baseStart_8352261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352287 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 3, 5]
def baseStart_8352287 : Nat := 118140960795 + 8352287 * 2 ^ 59
def prefixEnd_8352287 : Nat := 4983230072969 + 3 ^ 40 * 8352287 * 2
def baseEnd_8352287 : Nat := 1429579265099756124133679

theorem tailTrace_8352287 : CollatzResearch.WordTrace tailWord_8352287 prefixEnd_8352287 1429579265099756124133679 := by
  unfold tailWord_8352287
  simp only [CollatzResearch.WordTrace]
  refine ⟨304632933492098130898663115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203088622328065420599108743 304632933492098130898663115)
  ·
    refine ⟨456949400238147196347994673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304632933492098130898663115 456949400238147196347994673)
    ·
      refine ⟨342712050178610397260996005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456949400238147196347994673 342712050178610397260996005)
      ·
        refine ⟨64258509408489449486436751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342712050178610397260996005 64258509408489449486436751)
        ·
          refine ⟨96387764112734174229655127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64258509408489449486436751 96387764112734174229655127)
          ·
            refine ⟨144581646169101261344482691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96387764112734174229655127 144581646169101261344482691)
            ·
              refine ⟨216872469253651892016724037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144581646169101261344482691 216872469253651892016724037)
              ·
                refine ⟨40663587985059729753135757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216872469253651892016724037 40663587985059729753135757)
                ·
                  refine ⟨15248845494397398657425909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40663587985059729753135757 15248845494397398657425909)
                  ·
                    refine ⟨1429579265099756124133679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15248845494397398657425909 1429579265099756124133679)
                    ·
                      rfl

theorem cell23_8352287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 5].length) (baseStart_8352287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352287 prefixEnd_8352287 := by exact prefixLift 8352287
  have htrace : WordTrace (prefixWord ++ tailWord_8352287) baseStart_8352287 baseEnd_8352287 := by
    simpa [prefixWord, tailWord_8352287, baseEnd_8352287] using wordTrace_append hprefix tailTrace_8352287
  have hstable : (prefixWord ++ tailWord_8352287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352287).length < 2 ^ (prefixWord ++ tailWord_8352287).sum := by decide
  have hdescent : baseEnd_8352287 < baseStart_8352287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352291 : List Nat := [1, 1, 1, 4, 4, 3, 2, 1, 6]
def baseStart_8352291 : Nat := 118140960795 + 8352291 * 2 ^ 59
def prefixEnd_8352291 : Nat := 4983230072969 + 3 ^ 40 * 8352291 * 2
def baseEnd_8352291 : Nat := 476526649913542928527891

theorem tailTrace_8352291 : CollatzResearch.WordTrace tailWord_8352291 prefixEnd_8352291 476526649913542928527891 := by
  unfold tailWord_8352291
  simp only [CollatzResearch.WordTrace]
  refine ⟨304633079384083639581808727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203088719589389093054539151 304633079384083639581808727)
  ·
    refine ⟨456949619076125459372713091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304633079384083639581808727 456949619076125459372713091)
    ·
      refine ⟨685424428614188189059069637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456949619076125459372713091 685424428614188189059069637)
      ·
        refine ⟨128517080365160285448575557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 685424428614188189059069637 128517080365160285448575557)
        ·
          refine ⟨24096952568467553521607917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128517080365160285448575557 24096952568467553521607917)
          ·
            refine ⟨9036357213175332570602969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24096952568467553521607917 9036357213175332570602969)
            ·
              refine ⟨6777267909881499427952227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9036357213175332570602969 6777267909881499427952227)
              ·
                refine ⟨10165901864822249141928341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6777267909881499427952227 10165901864822249141928341)
                ·
                  refine ⟨476526649913542928527891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10165901864822249141928341 476526649913542928527891)
                  ·
                    rfl

theorem cell23_8352291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 6].length) (baseStart_8352291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352291 prefixEnd_8352291 := by exact prefixLift 8352291
  have htrace : WordTrace (prefixWord ++ tailWord_8352291) baseStart_8352291 baseEnd_8352291 := by
    simpa [prefixWord, tailWord_8352291, baseEnd_8352291] using wordTrace_append hprefix tailTrace_8352291
  have hstable : (prefixWord ++ tailWord_8352291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352291).length < 2 ^ (prefixWord ++ tailWord_8352291).sum := by decide
  have hdescent : baseEnd_8352291 < baseStart_8352291 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352304 : List Nat := [2, 1, 1, 1, 2, 3, 5, 2, 1, 5]
def baseStart_8352304 : Nat := 118140960795 + 8352304 * 2 ^ 59
def prefixEnd_8352304 : Nat := 4983230072969 + 3 ^ 40 * 8352304 * 2
def baseEnd_8352304 : Nat := 1429582174823464935296153

theorem tailTrace_8352304 : CollatzResearch.WordTrace tailWord_8352304 prefixEnd_8352304 1429582174823464935296153 := by
  unfold tailWord_8352304
  simp only [CollatzResearch.WordTrace]
  refine ⟨152316776766518271401015983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203089035688691028534687977 152316776766518271401015983)
  ·
    refine ⟨228475165149777407101523975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152316776766518271401015983 228475165149777407101523975)
    ·
      refine ⟨342712747724666110652285963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228475165149777407101523975 342712747724666110652285963)
      ·
        refine ⟨514069121586999165978428945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342712747724666110652285963 514069121586999165978428945)
        ·
          refine ⟨385551841190249374483821709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514069121586999165978428945 385551841190249374483821709)
          ·
            refine ⟨144581940446343515431433141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385551841190249374483821709 144581940446343515431433141)
            ·
              refine ⟨13554556916844704571696857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144581940446343515431433141 13554556916844704571696857)
              ·
                refine ⟨10165917687633528428772643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13554556916844704571696857 10165917687633528428772643)
                ·
                  refine ⟨15248876531450292643158965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10165917687633528428772643 15248876531450292643158965)
                  ·
                    refine ⟨1429582174823464935296153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15248876531450292643158965 1429582174823464935296153)
                    ·
                      rfl

theorem cell23_8352304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 1, 5].length) (baseStart_8352304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352304 prefixEnd_8352304 := by exact prefixLift 8352304
  have htrace : WordTrace (prefixWord ++ tailWord_8352304) baseStart_8352304 baseEnd_8352304 := by
    simpa [prefixWord, tailWord_8352304, baseEnd_8352304] using wordTrace_append hprefix tailTrace_8352304
  have hstable : (prefixWord ++ tailWord_8352304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352304).length < 2 ^ (prefixWord ++ tailWord_8352304).sum := by decide
  have hdescent : baseEnd_8352304 < baseStart_8352304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352311 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 2, 3, 2]
def baseStart_8352311 : Nat := 118140960795 + 8352311 * 2 ^ 59
def prefixEnd_8352311 : Nat := 4983230072969 + 3 ^ 40 * 8352311 * 2
def baseEnd_8352311 : Nat := 4288750118834976278500927

theorem tailTrace_8352311 : CollatzResearch.WordTrace tailWord_8352311 prefixEnd_8352311 4288750118834976278500927 := by
  unfold tailWord_8352311
  simp only [CollatzResearch.WordTrace]
  refine ⟨304633808844011182997536787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203089205896007455331691191 304633808844011182997536787)
  ·
    refine ⟨456950713266016774496305181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304633808844011182997536787 456950713266016774496305181)
    ·
      refine ⟨171356517474756290436114443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456950713266016774496305181 171356517474756290436114443)
      ·
        refine ⟨257034776212134435654171665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171356517474756290436114443 257034776212134435654171665)
        ·
          refine ⟨192776082159100826740628749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257034776212134435654171665 192776082159100826740628749)
          ·
            refine ⟨72291030809662810027735781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192776082159100826740628749 72291030809662810027735781)
            ·
              refine ⟨13554568276811776880200459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72291030809662810027735781 13554568276811776880200459)
              ·
                refine ⟨20331852415217665320300689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13554568276811776880200459 20331852415217665320300689)
                ·
                  refine ⟨15248889311413248990225517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20331852415217665320300689 15248889311413248990225517)
                  ·
                    refine ⟨5718333491779968371334569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15248889311413248990225517 5718333491779968371334569)
                    ·
                      refine ⟨4288750118834976278500927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5718333491779968371334569 4288750118834976278500927)
                      ·
                        rfl

theorem cell23_8352311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 3, 2].length) (baseStart_8352311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352311 prefixEnd_8352311 := by exact prefixLift 8352311
  have htrace : WordTrace (prefixWord ++ tailWord_8352311) baseStart_8352311 baseEnd_8352311 := by
    simpa [prefixWord, tailWord_8352311, baseEnd_8352311] using wordTrace_append hprefix tailTrace_8352311
  have hstable : (prefixWord ++ tailWord_8352311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352311).length < 2 ^ (prefixWord ++ tailWord_8352311).sum := by decide
  have hdescent : baseEnd_8352311 < baseStart_8352311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352334 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_8352334 : Nat := 118140960795 + 8352334 * 2 ^ 59
def prefixEnd_8352334 : Nat := 4983230072969 + 3 ^ 40 * 8352334 * 2
def baseEnd_8352334 : Nat := 1429587309630009896171107

theorem tailTrace_8352334 : CollatzResearch.WordTrace tailWord_8352334 prefixEnd_8352334 1429587309630009896171107 := by
  unfold tailWord_8352334
  simp only [CollatzResearch.WordTrace]
  refine ⟨38079330965365982240703007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203089765148618571950416037 38079330965365982240703007)
  ·
    refine ⟨57118996448048973361054511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38079330965365982240703007 57118996448048973361054511)
    ·
      refine ⟨85678494672073460041581767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57118996448048973361054511 85678494672073460041581767)
      ·
        refine ⟨128517742008110190062372651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85678494672073460041581767 128517742008110190062372651)
        ·
          refine ⟨192776613012165285093558977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128517742008110190062372651 192776613012165285093558977)
          ·
            refine ⟨144582459759123963820169233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192776613012165285093558977 144582459759123963820169233)
            ·
              refine ⟨108436844819342972865126925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144582459759123963820169233 108436844819342972865126925)
              ·
                refine ⟨40663816807253614824422597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108436844819342972865126925 40663816807253614824422597)
                ·
                  refine ⟨7624465651360052779579237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40663816807253614824422597 7624465651360052779579237)
                  ·
                    refine ⟨1429587309630009896171107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7624465651360052779579237 1429587309630009896171107)
                    ·
                      rfl

theorem cell23_8352334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_8352334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352334 prefixEnd_8352334 := by exact prefixLift 8352334
  have htrace : WordTrace (prefixWord ++ tailWord_8352334) baseStart_8352334 baseEnd_8352334 := by
    simpa [prefixWord, tailWord_8352334, baseEnd_8352334] using wordTrace_append hprefix tailTrace_8352334
  have hstable : (prefixWord ++ tailWord_8352334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352334).length < 2 ^ (prefixWord ++ tailWord_8352334).sum := by decide
  have hdescent : baseEnd_8352334 < baseStart_8352334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352344 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 3, 2, 3]
def baseStart_8352344 : Nat := 118140960795 + 8352344 * 2 ^ 59
def prefixEnd_8352344 : Nat := 4983230072969 + 3 ^ 40 * 8352344 * 2
def baseEnd_8352344 : Nat := 4288767063696574649388275

theorem tailTrace_8352344 : CollatzResearch.WordTrace tailWord_8352344 prefixEnd_8352344 4288767063696574649388275 := by
  unfold tailWord_8352344
  simp only [CollatzResearch.WordTrace]
  refine ⟨152317506226445814816744043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203090008301927753088992057 152317506226445814816744043)
  ·
    refine ⟨228476259339668722225116065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152317506226445814816744043 228476259339668722225116065)
    ·
      refine ⟨171357194504751541668837049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228476259339668722225116065 171357194504751541668837049)
      ·
        refine ⟨128517895878563656251627787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171357194504751541668837049 128517895878563656251627787)
        ·
          refine ⟨192776843817845484377441681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128517895878563656251627787 192776843817845484377441681)
          ·
            refine ⟨144582632863384113283081261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192776843817845484377441681 144582632863384113283081261)
            ·
              refine ⟨54218487323769042481155473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144582632863384113283081261 54218487323769042481155473)
              ·
                refine ⟨40663865492826781860866605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54218487323769042481155473 40663865492826781860866605)
                ·
                  refine ⟨15248949559810043197824977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40663865492826781860866605 15248949559810043197824977)
                  ·
                    refine ⟨11436712169857532398368733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15248949559810043197824977 11436712169857532398368733)
                    ·
                      refine ⟨4288767063696574649388275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11436712169857532398368733 4288767063696574649388275)
                      ·
                        rfl

theorem cell23_8352344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_8352344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352344 prefixEnd_8352344 := by exact prefixLift 8352344
  have htrace : WordTrace (prefixWord ++ tailWord_8352344) baseStart_8352344 baseEnd_8352344 := by
    simpa [prefixWord, tailWord_8352344, baseEnd_8352344] using wordTrace_append hprefix tailTrace_8352344
  have hstable : (prefixWord ++ tailWord_8352344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352344).length < 2 ^ (prefixWord ++ tailWord_8352344).sum := by decide
  have hdescent : baseEnd_8352344 < baseStart_8352344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352391 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_8352391 : Nat := 118140960795 + 8352391 * 2 ^ 59
def prefixEnd_8352391 : Nat := 4983230072969 + 3 ^ 40 * 8352391 * 2
def baseEnd_8352391 : Nat := 4288791197287335965500559

theorem tailTrace_8352391 : CollatzResearch.WordTrace tailWord_8352391 prefixEnd_8352391 4288791197287335965500559 := by
  unfold tailWord_8352391
  simp only [CollatzResearch.WordTrace]
  refine ⟨304636726683721356660449027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203091151122480904440299351 304636726683721356660449027)
  ·
    refine ⟨456955090025582034990673541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304636726683721356660449027 456955090025582034990673541)
    ·
      refine ⟨85679079379796631560751289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456955090025582034990673541 85679079379796631560751289)
      ·
        refine ⟨64259309534847473670563467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85679079379796631560751289 64259309534847473670563467)
        ·
          refine ⟨96388964302271210505845201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64259309534847473670563467 96388964302271210505845201)
          ·
            refine ⟨72291723226703407879383901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96388964302271210505845201 72291723226703407879383901)
            ·
              refine ⟨27109396210013777954768963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72291723226703407879383901 27109396210013777954768963)
              ·
                refine ⟨40664094315020666932153445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27109396210013777954768963 40664094315020666932153445)
                ·
                  refine ⟨7624517684066375049778771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40664094315020666932153445 7624517684066375049778771)
                  ·
                    refine ⟨11436776526099562574668157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7624517684066375049778771 11436776526099562574668157)
                    ·
                      refine ⟨4288791197287335965500559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11436776526099562574668157 4288791197287335965500559)
                      ·
                        rfl

theorem cell23_8352391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_8352391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352391 prefixEnd_8352391 := by exact prefixLift 8352391
  have htrace : WordTrace (prefixWord ++ tailWord_8352391) baseStart_8352391 baseEnd_8352391 := by
    simpa [prefixWord, tailWord_8352391, baseEnd_8352391] using wordTrace_append hprefix tailTrace_8352391
  have hstable : (prefixWord ++ tailWord_8352391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352391).length < 2 ^ (prefixWord ++ tailWord_8352391).sum := by decide
  have hdescent : baseEnd_8352391 < baseStart_8352391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352426 : List Nat := [3, 1, 5, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_8352426 : Nat := 118140960795 + 8352426 * 2 ^ 59
def prefixEnd_8352426 : Nat := 4983230072969 + 3 ^ 40 * 8352426 * 2
def baseEnd_8352426 : Nat := 4288809169110243328562899

theorem tailTrace_8352426 : CollatzResearch.WordTrace tailWord_8352426 prefixEnd_8352426 4288809169110243328562899 := by
  unfold tailWord_8352426
  simp only [CollatzResearch.WordTrace]
  refine ⟨76159500809648639409493283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203092002159063038425315421 76159500809648639409493283)
  ·
    refine ⟨114239251214472959114239925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76159500809648639409493283 114239251214472959114239925)
    ·
      refine ⟨10709929801356839916959993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114239251214472959114239925 10709929801356839916959993)
      ·
        refine ⟨8032447351017629937719995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10709929801356839916959993 8032447351017629937719995)
        ·
          refine ⟨12048671026526444906579993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8032447351017629937719995 12048671026526444906579993)
          ·
            refine ⟨9036503269894833679934995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12048671026526444906579993 9036503269894833679934995)
            ·
              refine ⟨13554754904842250519902493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9036503269894833679934995 13554754904842250519902493)
              ·
                refine ⟨5083033089315843944963435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13554754904842250519902493 5083033089315843944963435)
                ·
                  refine ⟨7624549633973765917445153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5083033089315843944963435 7624549633973765917445153)
                  ·
                    refine ⟨5718412225480324438083865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7624549633973765917445153 5718412225480324438083865)
                    ·
                      refine ⟨4288809169110243328562899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5718412225480324438083865 4288809169110243328562899)
                      ·
                        rfl

theorem cell23_8352426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_8352426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352426 prefixEnd_8352426 := by exact prefixLift 8352426
  have htrace : WordTrace (prefixWord ++ tailWord_8352426) baseStart_8352426 baseEnd_8352426 := by
    simpa [prefixWord, tailWord_8352426, baseEnd_8352426] using wordTrace_append hprefix tailTrace_8352426
  have hstable : (prefixWord ++ tailWord_8352426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352426).length < 2 ^ (prefixWord ++ tailWord_8352426).sum := by decide
  have hdescent : baseEnd_8352426 < baseStart_8352426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352434 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_8352434 : Nat := 118140960795 + 8352434 * 2 ^ 59
def prefixEnd_8352434 : Nat := 4983230072969 + 3 ^ 40 * 8352434 * 2
def baseEnd_8352434 : Nat := 4288813276955479297262861

theorem tailTrace_8352434 : CollatzResearch.WordTrace tailWord_8352434 prefixEnd_8352434 4288813276955479297262861 := by
  unfold tailWord_8352434
  simp only [CollatzResearch.WordTrace]
  refine ⟨76159573755641393751066089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203092196681710383336176237 76159573755641393751066089)
  ·
    refine ⟨57119680316731045313299567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76159573755641393751066089 57119680316731045313299567)
    ·
      refine ⟨85679520475096567969949351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57119680316731045313299567 85679520475096567969949351)
      ·
        refine ⟨128519280712644851954924027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85679520475096567969949351 128519280712644851954924027)
        ·
          refine ⟨192778921068967277932386041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128519280712644851954924027 192778921068967277932386041)
          ·
            refine ⟨144584190801725458449289531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192778921068967277932386041 144584190801725458449289531)
            ·
              refine ⟨216876286202588187673934297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144584190801725458449289531 216876286202588187673934297)
              ·
                refine ⟨162657214651941140755450723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216876286202588187673934297 162657214651941140755450723)
                ·
                  refine ⟨243985821977911711133176085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162657214651941140755450723 243985821977911711133176085)
                  ·
                    refine ⟨11436835405214611459367629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 243985821977911711133176085 11436835405214611459367629)
                    ·
                      refine ⟨4288813276955479297262861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11436835405214611459367629 4288813276955479297262861)
                      ·
                        rfl

theorem cell23_8352434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_8352434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352434 prefixEnd_8352434 := by exact prefixLift 8352434
  have htrace : WordTrace (prefixWord ++ tailWord_8352434) baseStart_8352434 baseEnd_8352434 := by
    simpa [prefixWord, tailWord_8352434, baseEnd_8352434] using wordTrace_append hprefix tailTrace_8352434
  have hstable : (prefixWord ++ tailWord_8352434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352434).length < 2 ^ (prefixWord ++ tailWord_8352434).sum := by decide
  have hdescent : baseEnd_8352434 < baseStart_8352434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352448 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 4, 2, 2]
def baseStart_8352448 : Nat := 118140960795 + 8352448 * 2 ^ 59
def prefixEnd_8352448 : Nat := 4983230072969 + 3 ^ 40 * 8352448 * 2
def baseEnd_8352448 : Nat := 4288820465684642242487797

theorem tailTrace_8352448 : CollatzResearch.WordTrace tailWord_8352448 prefixEnd_8352448 4288820465684642242487797 := by
  unfold tailWord_8352448
  simp only [CollatzResearch.WordTrace]
  refine ⟨152319402822257427697636999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203092537096343236930182665 152319402822257427697636999)
  ·
    refine ⟨228479104233386141546455499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152319402822257427697636999 228479104233386141546455499)
    ·
      refine ⟨342718656350079212319683249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228479104233386141546455499 342718656350079212319683249)
      ·
        refine ⟨257038992262559409239762437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342718656350079212319683249 257038992262559409239762437)
        ·
          refine ⟨48194811049229889232455457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257038992262559409239762437 48194811049229889232455457)
          ·
            refine ⟨36146108286922416924341593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48194811049229889232455457 36146108286922416924341593)
            ·
              refine ⟨27109581215191812693256195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36146108286922416924341593 27109581215191812693256195)
              ·
                refine ⟨40664371822787719039884293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27109581215191812693256195 40664371822787719039884293)
                ·
                  refine ⟨7624569716772697319978305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40664371822787719039884293 7624569716772697319978305)
                  ·
                    refine ⟨5718427287579522989983729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7624569716772697319978305 5718427287579522989983729)
                    ·
                      refine ⟨4288820465684642242487797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5718427287579522989983729 4288820465684642242487797)
                      ·
                        rfl

theorem cell23_8352448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 4, 2, 2].length) (baseStart_8352448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352448 prefixEnd_8352448 := by exact prefixLift 8352448
  have htrace : WordTrace (prefixWord ++ tailWord_8352448) baseStart_8352448 baseEnd_8352448 := by
    simpa [prefixWord, tailWord_8352448, baseEnd_8352448] using wordTrace_append hprefix tailTrace_8352448
  have hstable : (prefixWord ++ tailWord_8352448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352448).length < 2 ^ (prefixWord ++ tailWord_8352448).sum := by decide
  have hdescent : baseEnd_8352448 < baseStart_8352448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352464 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 3]
def baseStart_8352464 : Nat := 118140960795 + 8352464 * 2 ^ 59
def prefixEnd_8352464 : Nat := 4983230072969 + 3 ^ 40 * 8352464 * 2
def baseEnd_8352464 : Nat := 4288828681375114179887723

theorem tailTrace_8352464 : CollatzResearch.WordTrace tailWord_8352464 prefixEnd_8352464 4288828681375114179887723 := by
  unfold tailWord_8352464
  simp only [CollatzResearch.WordTrace]
  refine ⟨152319694606228445063928223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203092926141637926751904297 152319694606228445063928223)
  ·
    refine ⟨228479541909342667595892335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152319694606228445063928223 228479541909342667595892335)
    ·
      refine ⟨342719312864014001393838503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228479541909342667595892335 342719312864014001393838503)
      ·
        refine ⟨514078969296021002090757755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342719312864014001393838503 514078969296021002090757755)
        ·
          refine ⟨771118453944031503136136633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514078969296021002090757755 771118453944031503136136633)
          ·
            refine ⟨578338840458023627352102475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 771118453944031503136136633 578338840458023627352102475)
            ·
              refine ⟨867508260687035441028153713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578338840458023627352102475 867508260687035441028153713)
              ·
                refine ⟨650631195515276580771115285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 867508260687035441028153713 650631195515276580771115285)
                ·
                  refine ⟨30498337289778589723646029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 650631195515276580771115285 30498337289778589723646029)
                  ·
                    refine ⟨11436876483666971146367261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30498337289778589723646029 11436876483666971146367261)
                    ·
                      refine ⟨4288828681375114179887723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11436876483666971146367261 4288828681375114179887723)
                      ·
                        rfl

theorem cell23_8352464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 3].length) (baseStart_8352464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352464 prefixEnd_8352464 := by exact prefixLift 8352464
  have htrace : WordTrace (prefixWord ++ tailWord_8352464) baseStart_8352464 baseEnd_8352464 := by
    simpa [prefixWord, tailWord_8352464, baseEnd_8352464] using wordTrace_append hprefix tailTrace_8352464
  have hstable : (prefixWord ++ tailWord_8352464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352464).length < 2 ^ (prefixWord ++ tailWord_8352464).sum := by decide
  have hdescent : baseEnd_8352464 < baseStart_8352464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352469 : List Nat := [1, 3, 2, 5, 2, 1, 1, 2, 1, 3, 2]
def baseStart_8352469 : Nat := 118140960795 + 8352469 * 2 ^ 59
def prefixEnd_8352469 : Nat := 4983230072969 + 3 ^ 40 * 8352469 * 2
def baseEnd_8352469 : Nat := 4288831248778386660325201

theorem tailTrace_8352469 : CollatzResearch.WordTrace tailWord_8352469 prefixEnd_8352469 4288831248778386660325201 := by
  unfold tailWord_8352469
  simp only [CollatzResearch.WordTrace]
  refine ⟨304639571577438775981788461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203093047718292517321192307 304639571577438775981788461)
  ·
    refine ⟨114239839341539540993170673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304639571577438775981788461 114239839341539540993170673)
    ·
      refine ⟨85679879506154655744878005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114239839341539540993170673 85679879506154655744878005)
      ·
        refine ⟨8032488703701998976082313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85679879506154655744878005 8032488703701998976082313)
        ·
          refine ⟨6024366527776499232061735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8032488703701998976082313 6024366527776499232061735)
          ·
            refine ⟨9036549791664748848092603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024366527776499232061735 9036549791664748848092603)
            ·
              refine ⟨13554824687497123272138905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9036549791664748848092603 13554824687497123272138905)
              ·
                refine ⟨10166118515622842454104179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13554824687497123272138905 10166118515622842454104179)
                ·
                  refine ⟨15249177773434263681156269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10166118515622842454104179 15249177773434263681156269)
                  ·
                    refine ⟨5718441665037848880433601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15249177773434263681156269 5718441665037848880433601)
                    ·
                      refine ⟨4288831248778386660325201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5718441665037848880433601 4288831248778386660325201)
                      ·
                        rfl

theorem cell23_8352469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_8352469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352469 prefixEnd_8352469 := by exact prefixLift 8352469
  have htrace : WordTrace (prefixWord ++ tailWord_8352469) baseStart_8352469 baseEnd_8352469 := by
    simpa [prefixWord, tailWord_8352469, baseEnd_8352469] using wordTrace_append hprefix tailTrace_8352469
  have hstable : (prefixWord ++ tailWord_8352469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352469).length < 2 ^ (prefixWord ++ tailWord_8352469).sum := by decide
  have hdescent : baseEnd_8352469 < baseStart_8352469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352521 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 1, 6, 2]
def baseStart_8352521 : Nat := 118140960795 + 8352521 * 2 ^ 59
def prefixEnd_8352521 : Nat := 4983230072969 + 3 ^ 40 * 8352521 * 2
def baseEnd_8352521 : Nat := 4288857949772420456874961

theorem tailTrace_8352521 : CollatzResearch.WordTrace tailWord_8352521 prefixEnd_8352521 4288857949772420456874961 := by
  unfold tailWord_8352521
  simp only [CollatzResearch.WordTrace]
  refine ⟨304641468173250388862681417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203094312115500259241787611 304641468173250388862681417)
  ·
    refine ⟨228481101129937791647011063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304641468173250388862681417 228481101129937791647011063)
    ·
      refine ⟨342721651694906687470516595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228481101129937791647011063 342721651694906687470516595)
      ·
        refine ⟨514082477542360031205774893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342721651694906687470516595 514082477542360031205774893)
        ·
          refine ⟨192780929078385011702165585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 514082477542360031205774893 192780929078385011702165585)
          ·
            refine ⟨144585696808788758776624189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192780929078385011702165585 144585696808788758776624189)
            ·
              refine ⟨54219636303295784541234071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144585696808788758776624189 54219636303295784541234071)
              ·
                refine ⟨81329454454943676811851107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54219636303295784541234071 81329454454943676811851107)
                ·
                  refine ⟨121994181682415515217776661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81329454454943676811851107 121994181682415515217776661)
                  ·
                    refine ⟨5718477266363227275833281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121994181682415515217776661 5718477266363227275833281)
                    ·
                      refine ⟨4288857949772420456874961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5718477266363227275833281 4288857949772420456874961)
                      ·
                        rfl

theorem cell23_8352521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 6, 2].length) (baseStart_8352521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352521 prefixEnd_8352521 := by exact prefixLift 8352521
  have htrace : WordTrace (prefixWord ++ tailWord_8352521) baseStart_8352521 baseEnd_8352521 := by
    simpa [prefixWord, tailWord_8352521, baseEnd_8352521] using wordTrace_append hprefix tailTrace_8352521
  have hstable : (prefixWord ++ tailWord_8352521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352521).length < 2 ^ (prefixWord ++ tailWord_8352521).sum := by decide
  have hdescent : baseEnd_8352521 < baseStart_8352521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352531 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 3, 4]
def baseStart_8352531 : Nat := 118140960795 + 8352531 * 2 ^ 59
def prefixEnd_8352531 : Nat := 4983230072969 + 3 ^ 40 * 8352531 * 2
def baseEnd_8352531 : Nat := 1429621028192988472583305

theorem tailTrace_8352531 : CollatzResearch.WordTrace tailWord_8352531 prefixEnd_8352531 1429621028192988472583305 := by
  unfold tailWord_8352531
  simp only [CollatzResearch.WordTrace]
  refine ⟨304641832903214160570545447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203094555268809440380363631 304641832903214160570545447)
  ·
    refine ⟨456962749354821240855818171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304641832903214160570545447 456962749354821240855818171)
    ·
      refine ⟨685444124032231861283727257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456962749354821240855818171 685444124032231861283727257)
      ·
        refine ⟨514083093024173895962795443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685444124032231861283727257 514083093024173895962795443)
        ·
          refine ⟨771124639536260843944193165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514083093024173895962795443 771124639536260843944193165)
          ·
            refine ⟨289171739826097816479072437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 771124639536260843944193165 289171739826097816479072437)
            ·
              refine ⟨27109850608696670294913041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289171739826097816479072437 27109850608696670294913041)
              ·
                refine ⟨20332387956522502721184781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27109850608696670294913041 20332387956522502721184781)
                ·
                  refine ⟨7624645483695938520444293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20332387956522502721184781 7624645483695938520444293)
                  ·
                    refine ⟨1429621028192988472583305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7624645483695938520444293 1429621028192988472583305)
                    ·
                      rfl

theorem cell23_8352531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 4].length) (baseStart_8352531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352531 prefixEnd_8352531 := by exact prefixLift 8352531
  have htrace : WordTrace (prefixWord ++ tailWord_8352531) baseStart_8352531 baseEnd_8352531 := by
    simpa [prefixWord, tailWord_8352531, baseEnd_8352531] using wordTrace_append hprefix tailTrace_8352531
  have hstable : (prefixWord ++ tailWord_8352531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352531).length < 2 ^ (prefixWord ++ tailWord_8352531).sum := by decide
  have hdescent : baseEnd_8352531 < baseStart_8352531 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352535 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 2, 5]
def baseStart_8352535 : Nat := 118140960795 + 8352535 * 2 ^ 59
def prefixEnd_8352535 : Nat := 4983230072969 + 3 ^ 40 * 8352535 * 2
def baseEnd_8352535 : Nat := 1429621712833861134033299

theorem tailTrace_8352535 : CollatzResearch.WordTrace tailWord_8352535 prefixEnd_8352535 1429621712833861134033299 := by
  unfold tailWord_8352535
  simp only [CollatzResearch.WordTrace]
  refine ⟨304641978795199669253691059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203094652530133112835794039 304641978795199669253691059)
  ·
    refine ⟨456962968192799503880536589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304641978795199669253691059 456962968192799503880536589)
    ·
      refine ⟨171361113072299813955201221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456962968192799503880536589 171361113072299813955201221)
      ·
        refine ⟨32130208701056215116600229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171361113072299813955201221 32130208701056215116600229)
        ·
          refine ⟨6024414131448040334362543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32130208701056215116600229 6024414131448040334362543)
          ·
            refine ⟨9036621197172060501543815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024414131448040334362543 9036621197172060501543815)
            ·
              refine ⟨13554931795758090752315723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9036621197172060501543815 13554931795758090752315723)
              ·
                refine ⟨20332397693637136128473585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13554931795758090752315723 20332397693637136128473585)
                ·
                  refine ⟨15249298270227852096355189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20332397693637136128473585 15249298270227852096355189)
                  ·
                    refine ⟨1429621712833861134033299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15249298270227852096355189 1429621712833861134033299)
                    ·
                      rfl

theorem cell23_8352535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_8352535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352535 prefixEnd_8352535 := by exact prefixLift 8352535
  have htrace : WordTrace (prefixWord ++ tailWord_8352535) baseStart_8352535 baseEnd_8352535 := by
    simpa [prefixWord, tailWord_8352535, baseEnd_8352535] using wordTrace_append hprefix tailTrace_8352535
  have hstable : (prefixWord ++ tailWord_8352535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352535).length < 2 ^ (prefixWord ++ tailWord_8352535).sum := by decide
  have hdescent : baseEnd_8352535 < baseStart_8352535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352565 : List Nat := [1, 3, 3, 1, 3, 1, 2, 4, 1, 4]
def baseStart_8352565 : Nat := 118140960795 + 8352565 * 2 ^ 59
def prefixEnd_8352565 : Nat := 4983230072969 + 3 ^ 40 * 8352565 * 2
def baseEnd_8352565 : Nat := 1429626847640406094908253

theorem tailTrace_8352565 : CollatzResearch.WordTrace tailWord_8352565 prefixEnd_8352565 1429626847640406094908253 := by
  unfold tailWord_8352565
  simp only [CollatzResearch.WordTrace]
  refine ⟨304643072985090984377283149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203095381990060656251522099 304643072985090984377283149)
  ·
    refine ⟨114241152369409119141481181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304643072985090984377283149 114241152369409119141481181)
    ·
      refine ⟨42840432138528419678055443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114241152369409119141481181 42840432138528419678055443)
      ·
        refine ⟨64260648207792629517083165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42840432138528419678055443 64260648207792629517083165)
        ·
          refine ⟨24097743077922236068906187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64260648207792629517083165 24097743077922236068906187)
          ·
            refine ⟨36146614616883354103359281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24097743077922236068906187 36146614616883354103359281)
            ·
              refine ⟨27109960962662515577519461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36146614616883354103359281 27109960962662515577519461)
              ·
                refine ⟨5083117680499221670784899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27109960962662515577519461 5083117680499221670784899)
                ·
                  refine ⟨7624676520748832506177349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5083117680499221670784899 7624676520748832506177349)
                  ·
                    refine ⟨1429626847640406094908253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7624676520748832506177349 1429626847640406094908253)
                    ·
                      rfl

theorem cell23_8352565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_8352565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352565 prefixEnd_8352565 := by exact prefixLift 8352565
  have htrace : WordTrace (prefixWord ++ tailWord_8352565) baseStart_8352565 baseEnd_8352565 := by
    simpa [prefixWord, tailWord_8352565, baseEnd_8352565] using wordTrace_append hprefix tailTrace_8352565
  have hstable : (prefixWord ++ tailWord_8352565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352565).length < 2 ^ (prefixWord ++ tailWord_8352565).sum := by decide
  have hdescent : baseEnd_8352565 < baseStart_8352565 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352615 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_8352615 : Nat := 118140960795 + 8352615 * 2 ^ 59
def prefixEnd_8352615 : Nat := 4983230072969 + 3 ^ 40 * 8352615 * 2
def baseEnd_8352615 : Nat := 4288906216953943089099529

theorem tailTrace_8352615 : CollatzResearch.WordTrace tailWord_8352615 prefixEnd_8352615 4288906216953943089099529 := by
  unfold tailWord_8352615
  simp only [CollatzResearch.WordTrace]
  refine ⟨304644896634909842916603299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203096597756606561944402199 304644896634909842916603299)
  ·
    refine ⟨456967344952364764374904949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304644896634909842916603299 456967344952364764374904949)
    ·
      refine ⟨42840688589284196660147339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 456967344952364764374904949 42840688589284196660147339)
      ·
        refine ⟨64261032883926294990221009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42840688589284196660147339 64261032883926294990221009)
        ·
          refine ⟨48195774662944721242665757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64261032883926294990221009 48195774662944721242665757)
          ·
            refine ⟨18073415498604270465999659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48195774662944721242665757 18073415498604270465999659)
            ·
              refine ⟨27110123247906405698999489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18073415498604270465999659 27110123247906405698999489)
              ·
                refine ⟨20332592435929804274249617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27110123247906405698999489 20332592435929804274249617)
                ·
                  refine ⟨15249444326947353205687213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20332592435929804274249617 15249444326947353205687213)
                  ·
                    refine ⟨5718541622605257452132705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15249444326947353205687213 5718541622605257452132705)
                    ·
                      refine ⟨4288906216953943089099529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5718541622605257452132705 4288906216953943089099529)
                      ·
                        rfl

theorem cell23_8352615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_8352615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352615 prefixEnd_8352615 := by exact prefixLift 8352615
  have htrace : WordTrace (prefixWord ++ tailWord_8352615) baseStart_8352615 baseEnd_8352615 := by
    simpa [prefixWord, tailWord_8352615, baseEnd_8352615] using wordTrace_append hprefix tailTrace_8352615
  have hstable : (prefixWord ++ tailWord_8352615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352615).length < 2 ^ (prefixWord ++ tailWord_8352615).sum := by decide
  have hdescent : baseEnd_8352615 < baseStart_8352615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352642 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_8352642 : Nat := 118140960795 + 8352642 * 2 ^ 59
def prefixEnd_8352642 : Nat := 4983230072969 + 3 ^ 40 * 8352642 * 2
def baseEnd_8352642 : Nat := 1429640026977204827820635

theorem tailTrace_8352642 : CollatzResearch.WordTrace tailWord_8352642 prefixEnd_8352642 1429640026977204827820635 := by
  unfold tailWord_8352642
  simp only [CollatzResearch.WordTrace]
  refine ⟨76161470351453006631959045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203097254270541351018557453 76161470351453006631959045)
  ·
    refine ⟨14280275690897438743492321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76161470351453006631959045 14280275690897438743492321)
    ·
      refine ⟨10710206768173079057619241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14280275690897438743492321 10710206768173079057619241)
      ·
        refine ⟨8032655076129809293214431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10710206768173079057619241 8032655076129809293214431)
        ·
          refine ⟨12048982614194713939821647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8032655076129809293214431 12048982614194713939821647)
          ·
            refine ⟨18073473921292070909732471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12048982614194713939821647 18073473921292070909732471)
            ·
              refine ⟨27110210881938106364598707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18073473921292070909732471 27110210881938106364598707)
              ·
                refine ⟨40665316322907159546898061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27110210881938106364598707 40665316322907159546898061)
                ·
                  refine ⟨15249493621090184830086773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40665316322907159546898061 15249493621090184830086773)
                  ·
                    refine ⟨1429640026977204827820635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15249493621090184830086773 1429640026977204827820635)
                    ·
                      rfl

theorem cell23_8352642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_8352642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352642 prefixEnd_8352642 := by exact prefixLift 8352642
  have htrace : WordTrace (prefixWord ++ tailWord_8352642) baseStart_8352642 baseEnd_8352642 := by
    simpa [prefixWord, tailWord_8352642, baseEnd_8352642] using wordTrace_append hprefix tailTrace_8352642
  have hstable : (prefixWord ++ tailWord_8352642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352642).length < 2 ^ (prefixWord ++ tailWord_8352642).sum := by decide
  have hdescent : baseEnd_8352642 < baseStart_8352642 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352645 : List Nat := [1, 3, 1, 1, 3, 5, 1, 2, 1, 1, 4]
def baseStart_8352645 : Nat := 118140960795 + 8352645 * 2 ^ 59
def prefixEnd_8352645 : Nat := 4983230072969 + 3 ^ 40 * 8352645 * 2
def baseEnd_8352645 : Nat := 4288921621373577971724391

theorem tailTrace_8352645 : CollatzResearch.WordTrace tailWord_8352645 prefixEnd_8352645 4288921621373577971724391 := by
  unfold tailWord_8352645
  simp only [CollatzResearch.WordTrace]
  refine ⟨304645990824801158040195389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203097327216534105360130259 304645990824801158040195389)
  ·
    refine ⟨114242246559300434265073271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304645990824801158040195389 114242246559300434265073271)
    ·
      refine ⟨171363369838950651397609907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114242246559300434265073271 171363369838950651397609907)
      ·
        refine ⟨257045054758425977096414861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171363369838950651397609907 257045054758425977096414861)
        ·
          refine ⟨96391895534409741411155573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257045054758425977096414861 96391895534409741411155573)
          ·
            refine ⟨9036740206350913257295835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96391895534409741411155573 9036740206350913257295835)
            ·
              refine ⟨13555110309526369885943753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9036740206350913257295835 13555110309526369885943753)
              ·
                refine ⟨10166332732144777414457815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13555110309526369885943753 10166332732144777414457815)
                ·
                  refine ⟨15249499098217166121686723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10166332732144777414457815 15249499098217166121686723)
                  ·
                    refine ⟨22874248647325749182530085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15249499098217166121686723 22874248647325749182530085)
                    ·
                      refine ⟨4288921621373577971724391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22874248647325749182530085 4288921621373577971724391)
                      ·
                        rfl

theorem cell23_8352645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_8352645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352645 prefixEnd_8352645 := by exact prefixLift 8352645
  have htrace : WordTrace (prefixWord ++ tailWord_8352645) baseStart_8352645 baseEnd_8352645 := by
    simpa [prefixWord, tailWord_8352645, baseEnd_8352645] using wordTrace_append hprefix tailTrace_8352645
  have hstable : (prefixWord ++ tailWord_8352645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352645).length < 2 ^ (prefixWord ++ tailWord_8352645).sum := by decide
  have hdescent : baseEnd_8352645 < baseStart_8352645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352668 : List Nat := [2, 2, 3, 3, 3, 10]
def baseStart_8352668 : Nat := 118140960795 + 8352668 * 2 ^ 59
def prefixEnd_8352668 : Nat := 4983230072969 + 3 ^ 40 * 8352668 * 2
def baseEnd_8352668 : Nat := 17649931816578729965995

theorem tailTrace_8352668 : CollatzResearch.WordTrace tailWord_8352668 prefixEnd_8352668 17649931816578729965995 := by
  unfold tailWord_8352668
  simp only [CollatzResearch.WordTrace]
  refine ⟨152323414851858916484141329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203097886469145221978855105 152323414851858916484141329)
  ·
    refine ⟨114242561138894187363105997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152323414851858916484141329 114242561138894187363105997)
    ·
      refine ⟨42840960427085320261164749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114242561138894187363105997 42840960427085320261164749)
      ·
        refine ⟨16065360160156995097936781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42840960427085320261164749 16065360160156995097936781)
        ·
          refine ⟨6024510060058873161726293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16065360160156995097936781 6024510060058873161726293)
          ·
            refine ⟨17649931816578729965995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 6024510060058873161726293 17649931816578729965995)
            ·
              rfl

theorem cell23_8352668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 10].length) (baseStart_8352668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352668 prefixEnd_8352668 := by exact prefixLift 8352668
  have htrace : WordTrace (prefixWord ++ tailWord_8352668) baseStart_8352668 baseEnd_8352668 := by
    simpa [prefixWord, tailWord_8352668, baseEnd_8352668] using wordTrace_append hprefix tailTrace_8352668
  have hstable : (prefixWord ++ tailWord_8352668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352668).length < 2 ^ (prefixWord ++ tailWord_8352668).sum := by decide
  have hdescent : baseEnd_8352668 < baseStart_8352668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352692 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_8352692 : Nat := 118140960795 + 8352692 * 2 ^ 59
def prefixEnd_8352692 : Nat := 4983230072969 + 3 ^ 40 * 8352692 * 2
def baseEnd_8352692 : Nat := 4288945754964339287836675

theorem tailTrace_8352692 : CollatzResearch.WordTrace tailWord_8352692 prefixEnd_8352692 4288945754964339287836675 := by
  unfold tailWord_8352692
  simp only [CollatzResearch.WordTrace]
  refine ⟨152323852527815442533578165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203098470037087256711437553 152323852527815442533578165)
  ·
    refine ⟨14280361174482697737522953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152323852527815442533578165 14280361174482697737522953)
    ·
      refine ⟨10710270880862023303142215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14280361174482697737522953 10710270880862023303142215)
      ·
        refine ⟨16065406321293034954713323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10710270880862023303142215 16065406321293034954713323)
        ·
          refine ⟨24098109481939552432069985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16065406321293034954713323 24098109481939552432069985)
          ·
            refine ⟨18073582111454664324052489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24098109481939552432069985 18073582111454664324052489)
            ·
              refine ⟨13555186583590998243039367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18073582111454664324052489 13555186583590998243039367)
              ·
                refine ⟨20332779875386497364559051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13555186583590998243039367 20332779875386497364559051)
                ·
                  refine ⟨30499169813079746046838577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20332779875386497364559051 30499169813079746046838577)
                  ·
                    refine ⟨22874377359809809535128933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30499169813079746046838577 22874377359809809535128933)
                    ·
                      refine ⟨4288945754964339287836675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22874377359809809535128933 4288945754964339287836675)
                      ·
                        rfl

theorem cell23_8352692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_8352692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352692 prefixEnd_8352692 := by exact prefixLift 8352692
  have htrace : WordTrace (prefixWord ++ tailWord_8352692) baseStart_8352692 baseEnd_8352692 := by
    simpa [prefixWord, tailWord_8352692, baseEnd_8352692] using wordTrace_append hprefix tailTrace_8352692
  have hstable : (prefixWord ++ tailWord_8352692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352692).length < 2 ^ (prefixWord ++ tailWord_8352692).sum := by decide
  have hdescent : baseEnd_8352692 < baseStart_8352692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352695 : List Nat := [1, 1, 3, 1, 3, 1, 4, 3, 2, 1, 3]
def baseStart_8352695 : Nat := 118140960795 + 8352695 * 2 ^ 59
def prefixEnd_8352695 : Nat := 4983230072969 + 3 ^ 40 * 8352695 * 2
def baseEnd_8352695 : Nat := 4288947295406302776099161

theorem tailTrace_8352695 : CollatzResearch.WordTrace tailWord_8352695 prefixEnd_8352695 4288947295406302776099161 := by
  unfold tailWord_8352695
  simp only [CollatzResearch.WordTrace]
  refine ⟨304647814474620016579515539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203098542983080011053010359 304647814474620016579515539)
  ·
    refine ⟨456971721711930024869273309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304647814474620016579515539 456971721711930024869273309)
    ·
      refine ⟨171364395641973759325977491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456971721711930024869273309 171364395641973759325977491)
      ·
        refine ⟨257046593462960638988966237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171364395641973759325977491 257046593462960638988966237)
        ·
          refine ⟨96392472548610239620862339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257046593462960638988966237 96392472548610239620862339)
          ·
            refine ⟨144588708822915359431293509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96392472548610239620862339 144588708822915359431293509)
            ·
              refine ⟨27110382904296629893367533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144588708822915359431293509 27110382904296629893367533)
              ·
                refine ⟨10166393589111236210012825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27110382904296629893367533 10166393589111236210012825)
                ·
                  refine ⟨7624795191833427157509619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10166393589111236210012825 7624795191833427157509619)
                  ·
                    refine ⟨11437192787750140736264429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7624795191833427157509619 11437192787750140736264429)
                    ·
                      refine ⟨4288947295406302776099161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11437192787750140736264429 4288947295406302776099161)
                      ·
                        rfl

theorem cell23_8352695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_8352695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352695 prefixEnd_8352695 := by exact prefixLift 8352695
  have htrace : WordTrace (prefixWord ++ tailWord_8352695) baseStart_8352695 baseEnd_8352695 := by
    simpa [prefixWord, tailWord_8352695, baseEnd_8352695] using wordTrace_append hprefix tailTrace_8352695
  have hstable : (prefixWord ++ tailWord_8352695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352695).length < 2 ^ (prefixWord ++ tailWord_8352695).sum := by decide
  have hdescent : baseEnd_8352695 < baseStart_8352695 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352710 : List Nat := [6, 1, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_8352710 : Nat := 118140960795 + 8352710 * 2 ^ 59
def prefixEnd_8352710 : Nat := 4983230072969 + 3 ^ 40 * 8352710 * 2
def baseEnd_8352710 : Nat := 1429651665872040072470531

theorem tailTrace_8352710 : CollatzResearch.WordTrace tailWord_8352710 prefixEnd_8352710 1429651665872040072470531 := by
  unfold tailWord_8352710
  simp only [CollatzResearch.WordTrace]
  refine ⟨9520261299048927316915987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203098907713043782760874389 9520261299048927316915987)
  ·
    refine ⟨14280391948573390975373981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9520261299048927316915987 14280391948573390975373981)
    ·
      refine ⟨5355146980715021615765243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14280391948573390975373981 5355146980715021615765243)
      ·
        refine ⟨8032720471072532423647865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5355146980715021615765243 8032720471072532423647865)
        ·
          refine ⟨6024540353304399317735899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8032720471072532423647865 6024540353304399317735899)
          ·
            refine ⟨9036810529956598976603849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024540353304399317735899 9036810529956598976603849)
            ·
              refine ⟨6777607897467449232452887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9036810529956598976603849 6777607897467449232452887)
              ·
                refine ⟨10166411846201173848679331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6777607897467449232452887 10166411846201173848679331)
                ·
                  refine ⟨15249617769301760773018997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10166411846201173848679331 15249617769301760773018997)
                  ·
                    refine ⟨1429651665872040072470531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15249617769301760773018997 1429651665872040072470531)
                    ·
                      rfl

theorem cell23_8352710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_8352710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352710 prefixEnd_8352710 := by exact prefixLift 8352710
  have htrace : WordTrace (prefixWord ++ tailWord_8352710) baseStart_8352710 baseEnd_8352710 := by
    simpa [prefixWord, tailWord_8352710, baseEnd_8352710] using wordTrace_append hprefix tailTrace_8352710
  have hstable : (prefixWord ++ tailWord_8352710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352710).length < 2 ^ (prefixWord ++ tailWord_8352710).sum := by decide
  have hdescent : baseEnd_8352710 < baseStart_8352710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352721 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_8352721 : Nat := 118140960795 + 8352721 * 2 ^ 59
def prefixEnd_8352721 : Nat := 4983230072969 + 3 ^ 40 * 8352721 * 2
def baseEnd_8352721 : Nat := 4288960645903319674374041

theorem tailTrace_8352721 : CollatzResearch.WordTrace tailWord_8352721 prefixEnd_8352721 4288960645903319674374041 := by
  unfold tailWord_8352721
  simp only [CollatzResearch.WordTrace]
  refine ⟨304648762772525823019962017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203099175181683882013308011 304648762772525823019962017)
  ·
    refine ⟨228486572079394367264971513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304648762772525823019962017 228486572079394367264971513)
    ·
      refine ⟨171364929059545775448728635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228486572079394367264971513 171364929059545775448728635)
      ·
        refine ⟨257047393589318663173092953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171364929059545775448728635 257047393589318663173092953)
        ·
          refine ⟨192785545191988997379819715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257047393589318663173092953 192785545191988997379819715)
          ·
            refine ⟨289178317787983496069729573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192785545191988997379819715 289178317787983496069729573)
            ·
              refine ⟨54220934585246905513074295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289178317787983496069729573 54220934585246905513074295)
              ·
                refine ⟨81331401877870358269611443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54220934585246905513074295 81331401877870358269611443)
                ·
                  refine ⟨121997102816805537404417165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81331401877870358269611443 121997102816805537404417165)
                  ·
                    refine ⟨45748913556302076526656437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121997102816805537404417165 45748913556302076526656437)
                    ·
                      refine ⟨4288960645903319674374041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45748913556302076526656437 4288960645903319674374041)
                      ·
                        rfl

theorem cell23_8352721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_8352721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352721 prefixEnd_8352721 := by exact prefixLift 8352721
  have htrace : WordTrace (prefixWord ++ tailWord_8352721) baseStart_8352721 baseEnd_8352721 := by
    simpa [prefixWord, tailWord_8352721, baseEnd_8352721] using wordTrace_append hprefix tailTrace_8352721
  have hstable : (prefixWord ++ tailWord_8352721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352721).length < 2 ^ (prefixWord ++ tailWord_8352721).sum := by decide
  have hdescent : baseEnd_8352721 < baseStart_8352721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352792 : List Nat := [2, 1, 2, 3, 2, 3, 3, 2, 5]
def baseStart_8352792 : Nat := 118140960795 + 8352792 * 2 ^ 59
def prefixEnd_8352792 : Nat := 4983230072969 + 3 ^ 40 * 8352792 * 2
def baseEnd_8352792 : Nat := 476555233669976544065135

theorem tailTrace_8352792 : CollatzResearch.WordTrace tailWord_8352792 prefixEnd_8352792 476555233669976544065135 := by
  unfold tailWord_8352792
  simp only [CollatzResearch.WordTrace]
  refine ⟨152325676177634301072898315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203100901570179068097197753 152325676177634301072898315)
  ·
    refine ⟨228488514266451451609347473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152325676177634301072898315 228488514266451451609347473)
    ·
      refine ⟨171366385699838588707010605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228488514266451451609347473 171366385699838588707010605)
      ·
        refine ⟨64262394637439470765128977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171366385699838588707010605 64262394637439470765128977)
        ·
          refine ⟨48196795978079603073846733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64262394637439470765128977 48196795978079603073846733)
          ·
            refine ⟨18073798491779851152692525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48196795978079603073846733 18073798491779851152692525)
            ·
              refine ⟨6777674434417444182259697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18073798491779851152692525 6777674434417444182259697)
              ·
                refine ⟨5083255825813083136694773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6777674434417444182259697 5083255825813083136694773)
                ·
                  refine ⟨476555233669976544065135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5083255825813083136694773 476555233669976544065135)
                  ·
                    rfl

theorem cell23_8352792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 5].length) (baseStart_8352792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352792 prefixEnd_8352792 := by exact prefixLift 8352792
  have htrace : WordTrace (prefixWord ++ tailWord_8352792) baseStart_8352792 baseEnd_8352792 := by
    simpa [prefixWord, tailWord_8352792, baseEnd_8352792] using wordTrace_append hprefix tailTrace_8352792
  have hstable : (prefixWord ++ tailWord_8352792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352792).length < 2 ^ (prefixWord ++ tailWord_8352792).sum := by decide
  have hdescent : baseEnd_8352792 < baseStart_8352792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352822 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_8352822 : Nat := 118140960795 + 8352822 * 2 ^ 59
def prefixEnd_8352822 : Nat := 4983230072969 + 3 ^ 40 * 8352822 * 2
def baseEnd_8352822 : Nat := 1429670835816474593070359

theorem tailTrace_8352822 : CollatzResearch.WordTrace tailWord_8352822 prefixEnd_8352822 1429670835816474593070359 := by
  unfold tailWord_8352822
  simp only [CollatzResearch.WordTrace]
  refine ⟨19040777909072494829336795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203101631030106611512925813 19040777909072494829336795)
  ·
    refine ⟨28561166863608742244005193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19040777909072494829336795 28561166863608742244005193)
    ·
      refine ⟨21420875147706556683003895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28561166863608742244005193 21420875147706556683003895)
      ·
        refine ⟨32131312721559835024505843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21420875147706556683003895 32131312721559835024505843)
        ·
          refine ⟨48196969082339752536758765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32131312721559835024505843 48196969082339752536758765)
          ·
            refine ⟨18073863405877407201284537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48196969082339752536758765 18073863405877407201284537)
            ·
              refine ⟨13555397554408055400963403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18073863405877407201284537 13555397554408055400963403)
              ·
                refine ⟨20333096331612083101445105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13555397554408055400963403 20333096331612083101445105)
                ·
                  refine ⟨15249822248709062326083829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20333096331612083101445105 15249822248709062326083829)
                  ·
                    refine ⟨1429670835816474593070359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15249822248709062326083829 1429670835816474593070359)
                    ·
                      rfl

theorem cell23_8352822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_8352822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352822 prefixEnd_8352822 := by exact prefixLift 8352822
  have htrace : WordTrace (prefixWord ++ tailWord_8352822) baseStart_8352822 baseEnd_8352822 := by
    simpa [prefixWord, tailWord_8352822, baseEnd_8352822] using wordTrace_append hprefix tailTrace_8352822
  have hstable : (prefixWord ++ tailWord_8352822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352822).length < 2 ^ (prefixWord ++ tailWord_8352822).sum := by decide
  have hdescent : baseEnd_8352822 < baseStart_8352822 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352825 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 2, 1, 4]
def baseStart_8352825 : Nat := 118140960795 + 8352825 * 2 ^ 59
def prefixEnd_8352825 : Nat := 4983230072969 + 3 ^ 40 * 8352825 * 2
def baseEnd_8352825 : Nat := 4289014047891387267473563

theorem tailTrace_8352825 : CollatzResearch.WordTrace tailWord_8352825 prefixEnd_8352825 4289014047891387267473563 := by
  unfold tailWord_8352825
  simp only [CollatzResearch.WordTrace]
  refine ⟨304652555964149048781747929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203101703976099365854498619 304652555964149048781747929)
  ·
    refine ⟨228489416973111786586310947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304652555964149048781747929 228489416973111786586310947)
    ·
      refine ⟨342734125459667679879466421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228489416973111786586310947 342734125459667679879466421)
      ·
        refine ⟨32131324261843844988699977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 342734125459667679879466421 32131324261843844988699977)
        ·
          refine ⟨24098493196382883741524983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32131324261843844988699977 24098493196382883741524983)
          ·
            refine ⟨36147739794574325612287475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24098493196382883741524983 36147739794574325612287475)
            ·
              refine ⟨54221609691861488418431213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36147739794574325612287475 54221609691861488418431213)
              ·
                refine ⟨20333103634448058156911705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54221609691861488418431213 20333103634448058156911705)
                ·
                  refine ⟨15249827725836043617683779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20333103634448058156911705 15249827725836043617683779)
                  ·
                    refine ⟨22874741588754065426525669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15249827725836043617683779 22874741588754065426525669)
                    ·
                      refine ⟨4289014047891387267473563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22874741588754065426525669 4289014047891387267473563)
                      ·
                        rfl

theorem cell23_8352825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_8352825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352825 prefixEnd_8352825 := by exact prefixLift 8352825
  have htrace : WordTrace (prefixWord ++ tailWord_8352825) baseStart_8352825 baseEnd_8352825 := by
    simpa [prefixWord, tailWord_8352825, baseEnd_8352825] using wordTrace_append hprefix tailTrace_8352825
  have hstable : (prefixWord ++ tailWord_8352825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352825).length < 2 ^ (prefixWord ++ tailWord_8352825).sum := by decide
  have hdescent : baseEnd_8352825 < baseStart_8352825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352908 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 3, 6]
def baseStart_8352908 : Nat := 118140960795 + 8352908 * 2 ^ 59
def prefixEnd_8352908 : Nat := 4983230072969 + 3 ^ 40 * 8352908 * 2
def baseEnd_8352908 : Nat := 1429685555595236814245227

theorem tailTrace_8352908 : CollatzResearch.WordTrace tailWord_8352908 prefixEnd_8352908 1429685555595236814245227 := by
  unfold tailWord_8352908
  simp only [CollatzResearch.WordTrace]
  refine ⟨152327791611424176978509689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203103722148565569304679585 152327791611424176978509689)
  ·
    refine ⟨114245843708568132733882267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152327791611424176978509689 114245843708568132733882267)
    ·
      refine ⟨171368765562852199100823401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114245843708568132733882267 171368765562852199100823401)
      ·
        refine ⟨128526574172139149325617551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171368765562852199100823401 128526574172139149325617551)
        ·
          refine ⟨192789861258208723988426327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128526574172139149325617551 192789861258208723988426327)
          ·
            refine ⟨289184791887313085982639491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192789861258208723988426327 289184791887313085982639491)
            ·
              refine ⟨433777187830969628973959237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289184791887313085982639491 433777187830969628973959237)
              ·
                refine ⟨81333222718306805432617357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 433777187830969628973959237 81333222718306805432617357)
                ·
                  refine ⟨30499958519365052037231509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81333222718306805432617357 30499958519365052037231509)
                  ·
                    refine ⟨1429685555595236814245227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30499958519365052037231509 1429685555595236814245227)
                    ·
                      rfl

theorem cell23_8352908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_8352908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352908 prefixEnd_8352908 := by exact prefixLift 8352908
  have htrace : WordTrace (prefixWord ++ tailWord_8352908) baseStart_8352908 baseEnd_8352908 := by
    simpa [prefixWord, tailWord_8352908, baseEnd_8352908] using wordTrace_append hprefix tailTrace_8352908
  have hstable : (prefixWord ++ tailWord_8352908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352908).length < 2 ^ (prefixWord ++ tailWord_8352908).sum := by decide
  have hdescent : baseEnd_8352908 < baseStart_8352908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352932 : List Nat := [2, 3, 1, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_8352932 : Nat := 118140960795 + 8352932 * 2 ^ 59
def prefixEnd_8352932 : Nat := 4983230072969 + 3 ^ 40 * 8352932 * 2
def baseEnd_8352932 : Nat := 4289068990321418348835571

theorem tailTrace_8352932 : CollatzResearch.WordTrace tailWord_8352932 prefixEnd_8352932 4289068990321418348835571 := by
  unfold tailWord_8352932
  simp only [CollatzResearch.WordTrace]
  refine ⟨152328229287380703027946525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203104305716507604037262033 152328229287380703027946525)
  ·
    refine ⟨57123085982767763635479947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152328229287380703027946525 57123085982767763635479947)
    ·
      refine ⟨85684628974151645453219921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57123085982767763635479947 85684628974151645453219921)
      ·
        refine ⟨64263471730613734089914941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85684628974151645453219921 64263471730613734089914941)
        ·
          refine ⟨24098801898980150283718103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64263471730613734089914941 24098801898980150283718103)
          ·
            refine ⟨36148202848470225425577155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24098801898980150283718103 36148202848470225425577155)
            ·
              refine ⟨54222304272705338138365733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36148202848470225425577155 54222304272705338138365733)
              ·
                refine ⟨10166682051132250900943575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54222304272705338138365733 10166682051132250900943575)
                ·
                  refine ⟨15250023076698376351415363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10166682051132250900943575 15250023076698376351415363)
                  ·
                    refine ⟨22875034615047564527123045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15250023076698376351415363 22875034615047564527123045)
                    ·
                      refine ⟨4289068990321418348835571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22875034615047564527123045 4289068990321418348835571)
                      ·
                        rfl

theorem cell23_8352932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_8352932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352932 prefixEnd_8352932 := by exact prefixLift 8352932
  have htrace : WordTrace (prefixWord ++ tailWord_8352932) baseStart_8352932 baseEnd_8352932 := by
    simpa [prefixWord, tailWord_8352932, baseEnd_8352932] using wordTrace_append hprefix tailTrace_8352932
  have hstable : (prefixWord ++ tailWord_8352932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352932).length < 2 ^ (prefixWord ++ tailWord_8352932).sum := by decide
  have hdescent : baseEnd_8352932 < baseStart_8352932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8352999 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_8352999 : Nat := 118140960795 + 8352999 * 2 ^ 59
def prefixEnd_8352999 : Nat := 4983230072969 + 3 ^ 40 * 8352999 * 2
def baseEnd_8352999 : Nat := 4289103393525269586697763

theorem tailTrace_8352999 : CollatzResearch.WordTrace tailWord_8352999 prefixEnd_8352999 4289103393525269586697763 := by
  unfold tailWord_8352999
  simp only [CollatzResearch.WordTrace]
  refine ⟨304658902265518676498582051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203105934843679117665721367 304658902265518676498582051)
  ·
    refine ⟨456988353398278014747873077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304658902265518676498582051 456988353398278014747873077)
    ·
      refine ⟨42842658131088563882613101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 456988353398278014747873077 42842658131088563882613101)
      ·
        refine ⟨16065996799158211455979913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42842658131088563882613101 16065996799158211455979913)
        ·
          refine ⟨12049497599368658591984935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16065996799158211455979913 12049497599368658591984935)
          ·
            refine ⟨18074246399052987887977403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12049497599368658591984935 18074246399052987887977403)
            ·
              refine ⟨27111369598579481831966105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18074246399052987887977403 27111369598579481831966105)
              ·
                refine ⟨20333527198934611373974579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27111369598579481831966105 20333527198934611373974579)
                ·
                  refine ⟨30500290798401917060961869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20333527198934611373974579 30500290798401917060961869)
                  ·
                    refine ⟨11437609049400718897860701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30500290798401917060961869 11437609049400718897860701)
                    ·
                      refine ⟨4289103393525269586697763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11437609049400718897860701 4289103393525269586697763)
                      ·
                        rfl

theorem cell23_8352999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_8352999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8352999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8352999 prefixEnd_8352999 := by exact prefixLift 8352999
  have htrace : WordTrace (prefixWord ++ tailWord_8352999) baseStart_8352999 baseEnd_8352999 := by
    simpa [prefixWord, tailWord_8352999, baseEnd_8352999] using wordTrace_append hprefix tailTrace_8352999
  have hstable : (prefixWord ++ tailWord_8352999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8352999).length < 2 ^ (prefixWord ++ tailWord_8352999).sum := by decide
  have hdescent : baseEnd_8352999 < baseStart_8352999 := by decide
  rcases family_descends (prefixWord ++ tailWord_8352999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353022 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_8353022 : Nat := 118140960795 + 8353022 * 2 ^ 59
def prefixEnd_8353022 : Nat := 4983230072969 + 3 ^ 40 * 8353022 * 2
def baseEnd_8353022 : Nat := 4289115203580322996710157

theorem tailTrace_8353022 : CollatzResearch.WordTrace tailWord_8353022 prefixEnd_8353022 4289115203580322996710157 := by
  unfold tailWord_8353022
  simp only [CollatzResearch.WordTrace]
  refine ⟨38082467643054418928333665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203106494096290234284446213 38082467643054418928333665)
  ·
    refine ⟨28561850732290814196250249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38082467643054418928333665 28561850732290814196250249)
    ·
      refine ⟨21421388049218110647187687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28561850732290814196250249 21421388049218110647187687)
      ·
        refine ⟨32132082073827165970781531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21421388049218110647187687 32132082073827165970781531)
        ·
          refine ⟨48198123110740748956172297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32132082073827165970781531 48198123110740748956172297)
          ·
            refine ⟨36148592333055561717129223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48198123110740748956172297 36148592333055561717129223)
            ·
              refine ⟨54222888499583342575693835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36148592333055561717129223 54222888499583342575693835)
              ·
                refine ⟨81334332749375013863540753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54222888499583342575693835 81334332749375013863540753)
                ·
                  refine ⟨61000749562031260397655565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81334332749375013863540753 61000749562031260397655565)
                  ·
                    refine ⟨22875281085761722649120837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61000749562031260397655565 22875281085761722649120837)
                    ·
                      refine ⟨4289115203580322996710157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22875281085761722649120837 4289115203580322996710157)
                      ·
                        rfl

theorem cell23_8353022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_8353022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353022 prefixEnd_8353022 := by exact prefixLift 8353022
  have htrace : WordTrace (prefixWord ++ tailWord_8353022) baseStart_8353022 baseEnd_8353022 := by
    simpa [prefixWord, tailWord_8353022, baseEnd_8353022] using wordTrace_append hprefix tailTrace_8353022
  have hstable : (prefixWord ++ tailWord_8353022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353022).length < 2 ^ (prefixWord ++ tailWord_8353022).sum := by decide
  have hdescent : baseEnd_8353022 < baseStart_8353022 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353032 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 2, 6]
def baseStart_8353032 : Nat := 118140960795 + 8353032 * 2 ^ 59
def prefixEnd_8353032 : Nat := 4983230072969 + 3 ^ 40 * 8353032 * 2
def baseEnd_8353032 : Nat := 1429706779462289319195037

theorem tailTrace_8353032 : CollatzResearch.WordTrace tailWord_8353032 prefixEnd_8353032 1429706779462289319195037 := by
  unfold tailWord_8353032
  simp only [CollatzResearch.WordTrace]
  refine ⟨152330052937199561567266675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203106737249599415423022233 152330052937199561567266675)
  ·
    refine ⟨228495079405799342350900013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152330052937199561567266675 228495079405799342350900013)
    ·
      refine ⟨85685654777174753381587505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228495079405799342350900013 85685654777174753381587505)
      ·
        refine ⟨64264241082881065036190629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85685654777174753381587505 64264241082881065036190629)
        ·
          refine ⟨12049545203040199694285743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64264241082881065036190629 12049545203040199694285743)
          ·
            refine ⟨18074317804560299541428615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12049545203040199694285743 18074317804560299541428615)
            ·
              refine ⟨27111476706840449312142923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18074317804560299541428615 27111476706840449312142923)
              ·
                refine ⟨40667215060260673968214385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27111476706840449312142923 40667215060260673968214385)
                ·
                  refine ⟨30500411295195505476160789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40667215060260673968214385 30500411295195505476160789)
                  ·
                    refine ⟨1429706779462289319195037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30500411295195505476160789 1429706779462289319195037)
                    ·
                      rfl

theorem cell23_8353032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_8353032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353032 prefixEnd_8353032 := by exact prefixLift 8353032
  have htrace : WordTrace (prefixWord ++ tailWord_8353032) baseStart_8353032 baseEnd_8353032 := by
    simpa [prefixWord, tailWord_8353032, baseEnd_8353032] using wordTrace_append hprefix tailTrace_8353032
  have hstable : (prefixWord ++ tailWord_8353032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353032).length < 2 ^ (prefixWord ++ tailWord_8353032).sum := by decide
  have hdescent : baseEnd_8353032 < baseStart_8353032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353035 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 4]
def baseStart_8353035 : Nat := 118140960795 + 8353035 * 2 ^ 59
def prefixEnd_8353035 : Nat := 4983230072969 + 3 ^ 40 * 8353035 * 2
def baseEnd_8353035 : Nat := 4289121878828831445847597

theorem tailTrace_8353035 : CollatzResearch.WordTrace tailWord_8353035 prefixEnd_8353035 4289121878828831445847597 := by
  unfold tailWord_8353035
  simp only [CollatzResearch.WordTrace]
  refine ⟨304660215293388254646892559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203106810195592169764595039 304660215293388254646892559)
  ·
    refine ⟨456990322940082381970338839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304660215293388254646892559 456990322940082381970338839)
    ·
      refine ⟨685485484410123572955508259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456990322940082381970338839 685485484410123572955508259)
      ·
        refine ⟨1028228226615185359433262389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685485484410123572955508259 1028228226615185359433262389)
        ·
          refine ⟨96396396245173627446868349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1028228226615185359433262389 96396396245173627446868349)
          ·
            refine ⟨36148648591940110292575631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96396396245173627446868349 36148648591940110292575631)
            ·
              refine ⟨54222972887910165438863447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36148648591940110292575631 54222972887910165438863447)
              ·
                refine ⟨81334459331865248158295171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54222972887910165438863447 81334459331865248158295171)
                ·
                  refine ⟨122001688997797872237442757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81334459331865248158295171 122001688997797872237442757)
                  ·
                    refine ⟨22875316687087101044520517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122001688997797872237442757 22875316687087101044520517)
                    ·
                      refine ⟨4289121878828831445847597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22875316687087101044520517 4289121878828831445847597)
                      ·
                        rfl

theorem cell23_8353035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 4].length) (baseStart_8353035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353035 prefixEnd_8353035 := by exact prefixLift 8353035
  have htrace : WordTrace (prefixWord ++ tailWord_8353035) baseStart_8353035 baseEnd_8353035 := by
    simpa [prefixWord, tailWord_8353035, baseEnd_8353035] using wordTrace_append hprefix tailTrace_8353035
  have hstable : (prefixWord ++ tailWord_8353035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353035).length < 2 ^ (prefixWord ++ tailWord_8353035).sum := by decide
  have hdescent : baseEnd_8353035 < baseStart_8353035 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353069 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_8353069 : Nat := 118140960795 + 8353069 * 2 ^ 59
def prefixEnd_8353069 : Nat := 4983230072969 + 3 ^ 40 * 8353069 * 2
def baseEnd_8353069 : Nat := 4289139337171084312822441

theorem tailTrace_8353069 : CollatzResearch.WordTrace tailWord_8353069 prefixEnd_8353069 4289139337171084312822441 := by
  unfold tailWord_8353069
  simp only [CollatzResearch.WordTrace]
  refine ⟨304661455375265078453630261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203107636916843385635753507 304661455375265078453630261)
  ·
    refine ⟨28562011441431101105027837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304661455375265078453630261 28562011441431101105027837)
    ·
      refine ⟨10710754290536662914385439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28562011441431101105027837 10710754290536662914385439)
      ·
        refine ⟨16066131435804994371578159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10710754290536662914385439 16066131435804994371578159)
        ·
          refine ⟨24099197153707491557367239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16066131435804994371578159 24099197153707491557367239)
          ·
            refine ⟨36148795730561237336050859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24099197153707491557367239 36148795730561237336050859)
            ·
              refine ⟨54223193595841856004076289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36148795730561237336050859 54223193595841856004076289)
              ·
                refine ⟨40667395196881392003057217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54223193595841856004076289 40667395196881392003057217)
                ·
                  refine ⟨30500546397661044002292913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40667395196881392003057217 30500546397661044002292913)
                  ·
                    refine ⟨22875409798245783001719685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30500546397661044002292913 22875409798245783001719685)
                    ·
                      refine ⟨4289139337171084312822441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22875409798245783001719685 4289139337171084312822441)
                      ·
                        rfl

theorem cell23_8353069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_8353069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353069 prefixEnd_8353069 := by exact prefixLift 8353069
  have htrace : WordTrace (prefixWord ++ tailWord_8353069) baseStart_8353069 baseEnd_8353069 := by
    simpa [prefixWord, tailWord_8353069, baseEnd_8353069] using wordTrace_append hprefix tailTrace_8353069
  have hstable : (prefixWord ++ tailWord_8353069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353069).length < 2 ^ (prefixWord ++ tailWord_8353069).sum := by decide
  have hdescent : baseEnd_8353069 < baseStart_8353069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353073 : List Nat := [1, 2, 2, 3, 3, 3, 1, 2, 2, 2, 2]
def baseStart_8353073 : Nat := 118140960795 + 8353073 * 2 ^ 59
def prefixEnd_8353073 : Nat := 4983230072969 + 3 ^ 40 * 8353073 * 2
def baseEnd_8353073 : Nat := 4289141391093702297172423

theorem tailTrace_8353073 : CollatzResearch.WordTrace tailWord_8353073 prefixEnd_8353073 4289141391093702297172423 := by
  unfold tailWord_8353073
  simp only [CollatzResearch.WordTrace]
  refine ⟨304661601267250587136775873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203107734178167058091183915 304661601267250587136775873)
  ·
    refine ⟨228496200950437940352581905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304661601267250587136775873 228496200950437940352581905)
    ·
      refine ⟨171372150712828455264436429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228496200950437940352581905 171372150712828455264436429)
      ·
        refine ⟨64264556517310670724163661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171372150712828455264436429 64264556517310670724163661)
        ·
          refine ⟨24099208693991501521561373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64264556517310670724163661 24099208693991501521561373)
          ·
            refine ⟨9037203260246813070585515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24099208693991501521561373 9037203260246813070585515)
            ·
              refine ⟨13555804890370219605878273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9037203260246813070585515 13555804890370219605878273)
              ·
                refine ⟨10166853667777664704408705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13555804890370219605878273 10166853667777664704408705)
                ·
                  refine ⟨7625140250833248528306529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10166853667777664704408705 7625140250833248528306529)
                  ·
                    refine ⟨5718855188124936396229897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7625140250833248528306529 5718855188124936396229897)
                    ·
                      refine ⟨4289141391093702297172423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5718855188124936396229897 4289141391093702297172423)
                      ·
                        rfl

theorem cell23_8353073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_8353073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353073 prefixEnd_8353073 := by exact prefixLift 8353073
  have htrace : WordTrace (prefixWord ++ tailWord_8353073) baseStart_8353073 baseEnd_8353073 := by
    simpa [prefixWord, tailWord_8353073, baseEnd_8353073] using wordTrace_append hprefix tailTrace_8353073
  have hstable : (prefixWord ++ tailWord_8353073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353073).length < 2 ^ (prefixWord ++ tailWord_8353073).sum := by decide
  have hdescent : baseEnd_8353073 < baseStart_8353073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353089 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_8353089 : Nat := 118140960795 + 8353089 * 2 ^ 59
def prefixEnd_8353089 : Nat := 4983230072969 + 3 ^ 40 * 8353089 * 2
def baseEnd_8353089 : Nat := 4289149606784174234572349

theorem tailTrace_8353089 : CollatzResearch.WordTrace tailWord_8353089 prefixEnd_8353089 4289149606784174234572349 := by
  unfold tailWord_8353089
  simp only [CollatzResearch.WordTrace]
  refine ⟨304662184835192621869358321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203108123223461747912905547 304662184835192621869358321)
  ·
    refine ⟨228496638626394466402018741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304662184835192621869358321 228496638626394466402018741)
    ·
      refine ⟨21421559871224481225189257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228496638626394466402018741 21421559871224481225189257)
      ·
        refine ⟨16066169903418360918891943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21421559871224481225189257 16066169903418360918891943)
        ·
          refine ⟨24099254855127541378337915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16066169903418360918891943 24099254855127541378337915)
          ·
            refine ⟨36148882282691312067506873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24099254855127541378337915 36148882282691312067506873)
            ·
              refine ⟨27111661712018484050630155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36148882282691312067506873 27111661712018484050630155)
              ·
                refine ⟨40667492568027726075945233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27111661712018484050630155 40667492568027726075945233)
                ·
                  refine ⟨30500619426020794556958925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40667492568027726075945233 30500619426020794556958925)
                  ·
                    refine ⟨11437732284757797958859597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30500619426020794556958925 11437732284757797958859597)
                    ·
                      refine ⟨4289149606784174234572349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11437732284757797958859597 4289149606784174234572349)
                      ·
                        rfl

theorem cell23_8353089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_8353089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353089 prefixEnd_8353089 := by exact prefixLift 8353089
  have htrace : WordTrace (prefixWord ++ tailWord_8353089) baseStart_8353089 baseEnd_8353089 := by
    simpa [prefixWord, tailWord_8353089, baseEnd_8353089] using wordTrace_append hprefix tailTrace_8353089
  have hstable : (prefixWord ++ tailWord_8353089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353089).length < 2 ^ (prefixWord ++ tailWord_8353089).sum := by decide
  have hdescent : baseEnd_8353089 < baseStart_8353089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353105 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 2, 8]
def baseStart_8353105 : Nat := 118140960795 + 8353105 * 2 ^ 59
def prefixEnd_8353105 : Nat := 4983230072969 + 3 ^ 40 * 8353105 * 2
def baseEnd_8353105 : Nat := 1429719274158215390657425

theorem tailTrace_8353105 : CollatzResearch.WordTrace tailWord_8353105 prefixEnd_8353105 1429719274158215390657425 := by
  unfold tailWord_8353105
  simp only [CollatzResearch.WordTrace]
  refine ⟨304662768403134656601940769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203108512268756437734627179 304662768403134656601940769)
  ·
    refine ⟨228497076302350992451455577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304662768403134656601940769 228497076302350992451455577)
    ·
      refine ⟨171372807226763244338591683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228497076302350992451455577 171372807226763244338591683)
      ·
        refine ⟨257059210840144866507887525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171372807226763244338591683 257059210840144866507887525)
        ·
          refine ⟨48198602032527162470228911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257059210840144866507887525 48198602032527162470228911)
          ·
            refine ⟨72297903048790743705343367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48198602032527162470228911 72297903048790743705343367)
            ·
              refine ⟨108446854573186115558015051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72297903048790743705343367 108446854573186115558015051)
              ·
                refine ⟨162670281859779173337022577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108446854573186115558015051 162670281859779173337022577)
                ·
                  refine ⟨122002711394834380002766933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162670281859779173337022577 122002711394834380002766933)
                  ·
                    refine ⟨1429719274158215390657425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122002711394834380002766933 1429719274158215390657425)
                    ·
                      rfl

theorem cell23_8353105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_8353105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353105 prefixEnd_8353105 := by exact prefixLift 8353105
  have htrace : WordTrace (prefixWord ++ tailWord_8353105) baseStart_8353105 baseEnd_8353105 := by
    simpa [prefixWord, tailWord_8353105, baseEnd_8353105] using wordTrace_append hprefix tailTrace_8353105
  have hstable : (prefixWord ++ tailWord_8353105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353105).length < 2 ^ (prefixWord ++ tailWord_8353105).sum := by decide
  have hdescent : baseEnd_8353105 < baseStart_8353105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353112 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_8353112 : Nat := 118140960795 + 8353112 * 2 ^ 59
def prefixEnd_8353112 : Nat := 4983230072969 + 3 ^ 40 * 8353112 * 2
def baseEnd_8353112 : Nat := 4289161416839227644584743

theorem tailTrace_8353112 : CollatzResearch.WordTrace tailWord_8353112 prefixEnd_8353112 4289161416839227644584743 := by
  unfold tailWord_8353112
  simp only [CollatzResearch.WordTrace]
  refine ⟨152331511857054648398722795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203108682476072864531630393 152331511857054648398722795)
  ·
    refine ⟨228497267785581972598084193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152331511857054648398722795 228497267785581972598084193)
    ·
      refine ⟨171372950839186479448563145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228497267785581972598084193 171372950839186479448563145)
      ·
        refine ⟨128529713129389859586422359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171372950839186479448563145 128529713129389859586422359)
        ·
          refine ⟨192794569694084789379633539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128529713129389859586422359 192794569694084789379633539)
          ·
            refine ⟨289191854541127184069450309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192794569694084789379633539 289191854541127184069450309)
            ·
              refine ⟨54223472726461347013021933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289191854541127184069450309 54223472726461347013021933)
              ·
                refine ⟨20333802272423005129883225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54223472726461347013021933 20333802272423005129883225)
                ·
                  refine ⟨15250351704317253847412419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20333802272423005129883225 15250351704317253847412419)
                  ·
                    refine ⟨22875527556475880771118629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15250351704317253847412419 22875527556475880771118629)
                    ·
                      refine ⟨4289161416839227644584743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22875527556475880771118629 4289161416839227644584743)
                      ·
                        rfl

theorem cell23_8353112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_8353112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353112 prefixEnd_8353112 := by exact prefixLift 8353112
  have htrace : WordTrace (prefixWord ++ tailWord_8353112) baseStart_8353112 baseEnd_8353112 := by
    simpa [prefixWord, tailWord_8353112, baseEnd_8353112] using wordTrace_append hprefix tailTrace_8353112
  have hstable : (prefixWord ++ tailWord_8353112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353112).length < 2 ^ (prefixWord ++ tailWord_8353112).sum := by decide
  have hdescent : baseEnd_8353112 < baseStart_8353112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353135 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 8]
def baseStart_8353135 : Nat := 118140960795 + 8353135 * 2 ^ 59
def prefixEnd_8353135 : Nat := 4983230072969 + 3 ^ 40 * 8353135 * 2
def baseEnd_8353135 : Nat := 476574802988253450510793

theorem tailTrace_8353135 : CollatzResearch.WordTrace tailWord_8353135 prefixEnd_8353135 476574802988253450510793 := by
  unfold tailWord_8353135
  simp only [CollatzResearch.WordTrace]
  refine ⟨304663862593025971725532859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203109241728683981150355239 304663862593025971725532859)
  ·
    refine ⟨456995793889538957588299289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304663862593025971725532859 456995793889538957588299289)
    ·
      refine ⟨342746845417154218191224467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456995793889538957588299289 342746845417154218191224467)
      ·
        refine ⟨514120268125731327286836701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342746845417154218191224467 514120268125731327286836701)
        ·
          refine ⟨192795100547149247732563763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 514120268125731327286836701 192795100547149247732563763)
          ·
            refine ⟨289192650820723871598845645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192795100547149247732563763 289192650820723871598845645)
            ·
              refine ⟨108447244057771451849567117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289192650820723871598845645 108447244057771451849567117)
              ·
                refine ⟨40667716521664294443587669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108447244057771451849567117 40667716521664294443587669)
                ·
                  refine ⟨476574802988253450510793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40667716521664294443587669 476574802988253450510793)
                  ·
                    rfl

theorem cell23_8353135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 8].length) (baseStart_8353135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353135 prefixEnd_8353135 := by exact prefixLift 8353135
  have htrace : WordTrace (prefixWord ++ tailWord_8353135) baseStart_8353135 baseEnd_8353135 := by
    simpa [prefixWord, tailWord_8353135, baseEnd_8353135] using wordTrace_append hprefix tailTrace_8353135
  have hstable : (prefixWord ++ tailWord_8353135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353135).length < 2 ^ (prefixWord ++ tailWord_8353135).sum := by decide
  have hdescent : baseEnd_8353135 < baseStart_8353135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353189 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 4, 3, 2]
def baseStart_8353189 : Nat := 118140960795 + 8353189 * 2 ^ 59
def prefixEnd_8353189 : Nat := 4983230072969 + 3 ^ 40 * 8353189 * 2
def baseEnd_8353189 : Nat := 4289200954849623843321889

theorem tailTrace_8353189 : CollatzResearch.WordTrace tailWord_8353189 prefixEnd_8353189 4289200954849623843321889 := by
  unfold tailWord_8353189
  simp only [CollatzResearch.WordTrace]
  refine ⟨304665832134830338947998621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203110554756553559298665747 304665832134830338947998621)
  ·
    refine ⟨114249687050561377105499483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304665832134830338947998621 114249687050561377105499483)
    ·
      refine ⟨171374530575842065658249225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114249687050561377105499483 171374530575842065658249225)
      ·
        refine ⟨128530897931881549243686919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171374530575842065658249225 128530897931881549243686919)
        ·
          refine ⟨192796346897822323865530379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128530897931881549243686919 192796346897822323865530379)
          ·
            refine ⟨289194520346733485798295569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192796346897822323865530379 289194520346733485798295569)
            ·
              refine ⟨216895890260050114348721677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289194520346733485798295569 216895890260050114348721677)
              ·
                refine ⟨81335958847518792880770629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216895890260050114348721677 81335958847518792880770629)
                ·
                  refine ⟨15250492283909773665144493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81335958847518792880770629 15250492283909773665144493)
                  ·
                    refine ⟨5718934606466165124429185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15250492283909773665144493 5718934606466165124429185)
                    ·
                      refine ⟨4289200954849623843321889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5718934606466165124429185 4289200954849623843321889)
                      ·
                        rfl

theorem cell23_8353189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_8353189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353189 prefixEnd_8353189 := by exact prefixLift 8353189
  have htrace : WordTrace (prefixWord ++ tailWord_8353189) baseStart_8353189 baseEnd_8353189 := by
    simpa [prefixWord, tailWord_8353189, baseEnd_8353189] using wordTrace_append hprefix tailTrace_8353189
  have hstable : (prefixWord ++ tailWord_8353189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353189).length < 2 ^ (prefixWord ++ tailWord_8353189).sum := by decide
  have hdescent : baseEnd_8353189 < baseStart_8353189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353242 : List Nat := [3, 1, 1, 2, 3, 3, 10]
def baseStart_8353242 : Nat := 118140960795 + 8353242 * 2 ^ 59
def prefixEnd_8353242 : Nat := 4983230072969 + 3 ^ 40 * 8353242 * 2
def baseEnd_8353242 : Nat := 52953434189189038715545

theorem tailTrace_8353242 : CollatzResearch.WordTrace tailWord_8353242 prefixEnd_8353242 52953434189189038715545 := by
  unfold tailWord_8353242
  simp only [CollatzResearch.WordTrace]
  refine ⟨76166941300909582249919495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203111843469092219333118653 76166941300909582249919495)
  ·
    refine ⟨114250411951364373374879243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76166941300909582249919495 114250411951364373374879243)
    ·
      refine ⟨171375617927046560062318865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114250411951364373374879243 171375617927046560062318865)
      ·
        refine ⟨128531713445284920046739149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171375617927046560062318865 128531713445284920046739149)
        ·
          refine ⟨48199392541981845017527181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128531713445284920046739149 48199392541981845017527181)
          ·
            refine ⟨18074772203243191881572693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48199392541981845017527181 18074772203243191881572693)
            ·
              refine ⟨52953434189189038715545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 18074772203243191881572693 52953434189189038715545)
              ·
                rfl

theorem cell23_8353242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 10].length) (baseStart_8353242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353242 prefixEnd_8353242 := by exact prefixLift 8353242
  have htrace : WordTrace (prefixWord ++ tailWord_8353242) baseStart_8353242 baseEnd_8353242 := by
    simpa [prefixWord, tailWord_8353242, baseEnd_8353242] using wordTrace_append hprefix tailTrace_8353242
  have hstable : (prefixWord ++ tailWord_8353242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353242).length < 2 ^ (prefixWord ++ tailWord_8353242).sum := by decide
  have hdescent : baseEnd_8353242 < baseStart_8353242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353253 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 3, 2, 2]
def baseStart_8353253 : Nat := 118140960795 + 8353253 * 2 ^ 59
def prefixEnd_8353253 : Nat := 4983230072969 + 3 ^ 40 * 8353253 * 2
def baseEnd_8353253 : Nat := 4289233817611511592921595

theorem tailTrace_8353253 : CollatzResearch.WordTrace tailWord_8353253 prefixEnd_8353253 4289233817611511592921595 := by
  unfold tailWord_8353253
  simp only [CollatzResearch.WordTrace]
  refine ⟨304668166406598477878328413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203112110937732318585552275 304668166406598477878328413)
  ·
    refine ⟨114250562402474429204373155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304668166406598477878328413 114250562402474429204373155)
    ·
      refine ⟨171375843603711643806559733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114250562402474429204373155 171375843603711643806559733)
      ·
        refine ⟨16066485337847966606864975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171375843603711643806559733 16066485337847966606864975)
        ·
          refine ⟨24099728006771949910297463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16066485337847966606864975 24099728006771949910297463)
          ·
            refine ⟨36149592010157924865446195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24099728006771949910297463 36149592010157924865446195)
            ·
              refine ⟨54224388015236887298169293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36149592010157924865446195 54224388015236887298169293)
              ·
                refine ⟨20334145505713832736813485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54224388015236887298169293 20334145505713832736813485)
                ·
                  refine ⟨7625304564642687276305057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20334145505713832736813485 7625304564642687276305057)
                  ·
                    refine ⟨5718978423482015457228793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7625304564642687276305057 5718978423482015457228793)
                    ·
                      refine ⟨4289233817611511592921595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5718978423482015457228793 4289233817611511592921595)
                      ·
                        rfl

theorem cell23_8353253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_8353253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353253 prefixEnd_8353253 := by exact prefixLift 8353253
  have htrace : WordTrace (prefixWord ++ tailWord_8353253) baseStart_8353253 baseEnd_8353253 := by
    simpa [prefixWord, tailWord_8353253, baseEnd_8353253] using wordTrace_append hprefix tailTrace_8353253
  have hstable : (prefixWord ++ tailWord_8353253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353253).length < 2 ^ (prefixWord ++ tailWord_8353253).sum := by decide
  have hdescent : baseEnd_8353253 < baseStart_8353253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353266 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_8353266 : Nat := 118140960795 + 8353266 * 2 ^ 59
def prefixEnd_8353266 : Nat := 4983230072969 + 3 ^ 40 * 8353266 * 2
def baseEnd_8353266 : Nat := 4289240492860020042059035

theorem tailTrace_8353266 : CollatzResearch.WordTrace tailWord_8353266 prefixEnd_8353266 4289240492860020042059035 := by
  unfold tailWord_8353266
  simp only [CollatzResearch.WordTrace]
  refine ⟨76167160138887845274637913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203112427037034254065701101 76167160138887845274637913)
  ·
    refine ⟨57125370104165883955978435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76167160138887845274637913 57125370104165883955978435)
    ·
      refine ⟨85688055156248825933967653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57125370104165883955978435 85688055156248825933967653)
      ·
        refine ⟨16066510341796654862618935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85688055156248825933967653 16066510341796654862618935)
        ·
          refine ⟨24099765512694982293928403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16066510341796654862618935 24099765512694982293928403)
          ·
            refine ⟨36149648269042473440892605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24099765512694982293928403 36149648269042473440892605)
            ·
              refine ⟨13556118100890927540334727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36149648269042473440892605 13556118100890927540334727)
              ·
                refine ⟨20334177151336391310502091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13556118100890927540334727 20334177151336391310502091)
                ·
                  refine ⟨30501265727004586965753137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20334177151336391310502091 30501265727004586965753137)
                  ·
                    refine ⟨22875949295253440224314853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30501265727004586965753137 22875949295253440224314853)
                    ·
                      refine ⟨4289240492860020042059035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22875949295253440224314853 4289240492860020042059035)
                      ·
                        rfl

theorem cell23_8353266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_8353266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353266 prefixEnd_8353266 := by exact prefixLift 8353266
  have htrace : WordTrace (prefixWord ++ tailWord_8353266) baseStart_8353266 baseEnd_8353266 := by
    simpa [prefixWord, tailWord_8353266, baseEnd_8353266] using wordTrace_append hprefix tailTrace_8353266
  have hstable : (prefixWord ++ tailWord_8353266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353266).length < 2 ^ (prefixWord ++ tailWord_8353266).sum := by decide
  have hdescent : baseEnd_8353266 < baseStart_8353266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353287 : List Nat := [1, 1, 4, 3, 2, 3, 1, 3, 1, 2, 2]
def baseStart_8353287 : Nat := 118140960795 + 8353287 * 2 ^ 59
def prefixEnd_8353287 : Nat := 4983230072969 + 3 ^ 40 * 8353287 * 2
def baseEnd_8353287 : Nat := 4289251275953764459896439

theorem tailTrace_8353287 : CollatzResearch.WordTrace tailWord_8353287 prefixEnd_8353287 4289251275953764459896439 := by
  unfold tailWord_8353287
  simp only [CollatzResearch.WordTrace]
  refine ⟨304669406488475301685066115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203112937658983534456710743 304669406488475301685066115)
  ·
    refine ⟨457004109732712952527599173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304669406488475301685066115 457004109732712952527599173)
    ·
      refine ⟨85688270574883678598924845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457004109732712952527599173 85688270574883678598924845)
      ·
        refine ⟨32133101465581379474596817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85688270574883678598924845 32133101465581379474596817)
        ·
          refine ⟨24099826099186034605947613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32133101465581379474596817 24099826099186034605947613)
          ·
            refine ⟨9037434787194762977230355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24099826099186034605947613 9037434787194762977230355)
            ·
              refine ⟨13556152180792144465845533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9037434787194762977230355 13556152180792144465845533)
              ·
                refine ⟨5083557067797054174692075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13556152180792144465845533 5083557067797054174692075)
                ·
                  refine ⟨7625335601695581262038113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5083557067797054174692075 7625335601695581262038113)
                  ·
                    refine ⟨5719001701271685946528585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7625335601695581262038113 5719001701271685946528585)
                    ·
                      refine ⟨4289251275953764459896439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5719001701271685946528585 4289251275953764459896439)
                      ·
                        rfl

theorem cell23_8353287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_8353287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353287 prefixEnd_8353287 := by exact prefixLift 8353287
  have htrace : WordTrace (prefixWord ++ tailWord_8353287) baseStart_8353287 baseEnd_8353287 := by
    simpa [prefixWord, tailWord_8353287, baseEnd_8353287] using wordTrace_append hprefix tailTrace_8353287
  have hstable : (prefixWord ++ tailWord_8353287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353287).length < 2 ^ (prefixWord ++ tailWord_8353287).sum := by decide
  have hdescent : baseEnd_8353287 < baseStart_8353287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353293 : List Nat := [1, 7, 1, 1, 2, 2, 9]
def baseStart_8353293 : Nat := 118140960795 + 8353293 * 2 ^ 59
def prefixEnd_8353293 : Nat := 4983230072969 + 3 ^ 40 * 8353293 * 2
def baseEnd_8353293 : Nat := 52953757491823351066931

theorem tailTrace_8353293 : CollatzResearch.WordTrace tailWord_8353293 prefixEnd_8353293 52953757491823351066931 := by
  unfold tailWord_8353293
  simp only [CollatzResearch.WordTrace]
  refine ⟨304669625326453564709784533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203113083550969043139856355 304669625326453564709784533)
  ·
    refine ⟨7140694343588755422885575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 304669625326453564709784533 7140694343588755422885575)
    ·
      refine ⟨10711041515383133134328363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7140694343588755422885575 10711041515383133134328363)
      ·
        refine ⟨16066562273074699701492545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10711041515383133134328363 16066562273074699701492545)
        ·
          refine ⟨12049921704806024776119409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16066562273074699701492545 12049921704806024776119409)
          ·
            refine ⟨9037441278604518582089557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12049921704806024776119409 9037441278604518582089557)
            ·
              refine ⟨52953757491823351066931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9037441278604518582089557 52953757491823351066931)
              ·
                rfl

theorem cell23_8353293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 9].length) (baseStart_8353293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353293 prefixEnd_8353293 := by exact prefixLift 8353293
  have htrace : WordTrace (prefixWord ++ tailWord_8353293) baseStart_8353293 baseEnd_8353293 := by
    simpa [prefixWord, tailWord_8353293, baseEnd_8353293] using wordTrace_append hprefix tailTrace_8353293
  have hstable : (prefixWord ++ tailWord_8353293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353293).length < 2 ^ (prefixWord ++ tailWord_8353293).sum := by decide
  have hdescent : baseEnd_8353293 < baseStart_8353293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353309 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_8353309 : Nat := 118140960795 + 8353309 * 2 ^ 59
def prefixEnd_8353309 : Nat := 4983230072969 + 3 ^ 40 * 8353309 * 2
def baseEnd_8353309 : Nat := 4289262572528163373821337

theorem tailTrace_8353309 : CollatzResearch.WordTrace tailWord_8353309 prefixEnd_8353309 4289262572528163373821337 := by
  unfold tailWord_8353309
  simp only [CollatzResearch.WordTrace]
  refine ⟨304670208894395599442366981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203113472596263732961577987 304670208894395599442366981)
  ·
    refine ⟨57125664167699174895443809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304670208894395599442366981 57125664167699174895443809)
    ·
      refine ⟨42844248125774381171582857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57125664167699174895443809 42844248125774381171582857)
      ·
        refine ⟨32133186094330785878687143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42844248125774381171582857 32133186094330785878687143)
        ·
          refine ⟨48199779141496178818030715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32133186094330785878687143 48199779141496178818030715)
          ·
            refine ⟨72299668712244268227046073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48199779141496178818030715 72299668712244268227046073)
            ·
              refine ⟨54224751534183201170284555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72299668712244268227046073 54224751534183201170284555)
              ·
                refine ⟨81337127301274801755426833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54224751534183201170284555 81337127301274801755426833)
                ·
                  refine ⟨61002845475956101316570125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81337127301274801755426833 61002845475956101316570125)
                  ·
                    refine ⟨22876067053483537993713797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61002845475956101316570125 22876067053483537993713797)
                    ·
                      refine ⟨4289262572528163373821337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22876067053483537993713797 4289262572528163373821337)
                      ·
                        rfl

theorem cell23_8353309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_8353309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353309 prefixEnd_8353309 := by exact prefixLift 8353309
  have htrace : WordTrace (prefixWord ++ tailWord_8353309) baseStart_8353309 baseEnd_8353309 := by
    simpa [prefixWord, tailWord_8353309, baseEnd_8353309] using wordTrace_append hprefix tailTrace_8353309
  have hstable : (prefixWord ++ tailWord_8353309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353309).length < 2 ^ (prefixWord ++ tailWord_8353309).sum := by decide
  have hdescent : baseEnd_8353309 < baseStart_8353309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353310 : List Nat := [4, 3, 3, 1, 1, 1, 2, 8]
def baseStart_8353310 : Nat := 118140960795 + 8353310 * 2 ^ 59
def prefixEnd_8353310 : Nat := 4983230072969 + 3 ^ 40 * 8353310 * 2
def baseEnd_8353310 : Nat := 158861595778104365552179

theorem tailTrace_8353310 : CollatzResearch.WordTrace tailWord_8353310 prefixEnd_8353310 158861595778104365552179 := by
  unfold tailWord_8353310
  simp only [CollatzResearch.WordTrace]
  refine ⟨38083780670923997076644173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203113496911594651075435589 38083780670923997076644173)
  ·
    refine ⟨14281417751596498903741565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38083780670923997076644173 14281417751596498903741565)
    ·
      refine ⟨5355531656848687088903087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14281417751596498903741565 5355531656848687088903087)
      ·
        refine ⟨8033297485273030633354631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5355531656848687088903087 8033297485273030633354631)
        ·
          refine ⟨12049946227909545950031947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8033297485273030633354631 12049946227909545950031947)
          ·
            refine ⟨18074919341864318925047921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12049946227909545950031947 18074919341864318925047921)
            ·
              refine ⟨13556189506398239193785941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18074919341864318925047921 13556189506398239193785941)
              ·
                refine ⟨158861595778104365552179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13556189506398239193785941 158861595778104365552179)
                ·
                  rfl

theorem cell23_8353310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_8353310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353310 prefixEnd_8353310 := by exact prefixLift 8353310
  have htrace : WordTrace (prefixWord ++ tailWord_8353310) baseStart_8353310 baseEnd_8353310 := by
    simpa [prefixWord, tailWord_8353310, baseEnd_8353310] using wordTrace_append hprefix tailTrace_8353310
  have hstable : (prefixWord ++ tailWord_8353310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353310).length < 2 ^ (prefixWord ++ tailWord_8353310).sum := by decide
  have hdescent : baseEnd_8353310 < baseStart_8353310 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353320 : List Nat := [2, 1, 5, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_8353320 : Nat := 118140960795 + 8353320 * 2 ^ 59
def prefixEnd_8353320 : Nat := 4983230072969 + 3 ^ 40 * 8353320 * 2
def baseEnd_8353320 : Nat := 4289268220815362830783787

theorem tailTrace_8353320 : CollatzResearch.WordTrace tailWord_8353320 prefixEnd_8353320 4289268220815362830783787 := by
  unfold tailWord_8353320
  simp only [CollatzResearch.WordTrace]
  refine ⟨152335305048677874160508707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203113740064903832214011609 152335305048677874160508707)
  ·
    refine ⟨228502957573016811240763061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152335305048677874160508707 228502957573016811240763061)
    ·
      refine ⟨21422152272470326053821537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228502957573016811240763061 21422152272470326053821537)
      ·
        refine ⟨16066614204352744540366153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21422152272470326053821537 16066614204352744540366153)
        ·
          refine ⟨12049960653264558405274615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16066614204352744540366153 12049960653264558405274615)
          ·
            refine ⟨18074940979896837607911923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12049960653264558405274615 18074940979896837607911923)
            ·
              refine ⟨27112411469845256411867885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18074940979896837607911923 27112411469845256411867885)
              ·
                refine ⟨10167154301191971154450457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27112411469845256411867885 10167154301191971154450457)
                ·
                  refine ⟨7625365725893978365837843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10167154301191971154450457 7625365725893978365837843)
                  ·
                    refine ⟨11438048588840967548756765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7625365725893978365837843 11438048588840967548756765)
                    ·
                      refine ⟨4289268220815362830783787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11438048588840967548756765 4289268220815362830783787)
                      ·
                        rfl

theorem cell23_8353320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_8353320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353320 prefixEnd_8353320 := by exact prefixLift 8353320
  have htrace : WordTrace (prefixWord ++ tailWord_8353320) baseStart_8353320 baseEnd_8353320 := by
    simpa [prefixWord, tailWord_8353320, baseEnd_8353320] using wordTrace_append hprefix tailTrace_8353320
  have hstable : (prefixWord ++ tailWord_8353320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353320).length < 2 ^ (prefixWord ++ tailWord_8353320).sum := by decide
  have hdescent : baseEnd_8353320 < baseStart_8353320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353359 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 3]
def baseStart_8353359 : Nat := 118140960795 + 8353359 * 2 ^ 59
def prefixEnd_8353359 : Nat := 4983230072969 + 3 ^ 40 * 8353359 * 2
def baseEnd_8353359 : Nat := 4289288246560888178196107

theorem tailTrace_8353359 : CollatzResearch.WordTrace tailWord_8353359 prefixEnd_8353359 4289288246560888178196107 := by
  unfold tailWord_8353359
  simp only [CollatzResearch.WordTrace]
  refine ⟨304672032544214457981687131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203114688362809638654458087 304672032544214457981687131)
  ·
    refine ⟨457008048816321686972530697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304672032544214457981687131 457008048816321686972530697)
    ·
      refine ⟨342756036612241265229398023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457008048816321686972530697 342756036612241265229398023)
      ·
        refine ⟨514134054918361897844097035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342756036612241265229398023 514134054918361897844097035)
        ·
          refine ⟨771201082377542846766145553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514134054918361897844097035 771201082377542846766145553)
          ·
            refine ⟨578400811783157135074609165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 771201082377542846766145553 578400811783157135074609165)
            ·
              refine ⟨216900304418683925652978437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 578400811783157135074609165 216900304418683925652978437)
              ·
                refine ⟨40668807078503236059933457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216900304418683925652978437 40668807078503236059933457)
                ·
                  refine ⟨30501605308877427044950093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40668807078503236059933457 30501605308877427044950093)
                  ·
                    refine ⟨11438101990829035141856285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30501605308877427044950093 11438101990829035141856285)
                    ·
                      refine ⟨4289288246560888178196107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11438101990829035141856285 4289288246560888178196107)
                      ·
                        rfl

theorem cell23_8353359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 3].length) (baseStart_8353359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353359 prefixEnd_8353359 := by exact prefixLift 8353359
  have htrace : WordTrace (prefixWord ++ tailWord_8353359) baseStart_8353359 baseEnd_8353359 := by
    simpa [prefixWord, tailWord_8353359, baseEnd_8353359] using wordTrace_append hprefix tailTrace_8353359
  have hstable : (prefixWord ++ tailWord_8353359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353359).length < 2 ^ (prefixWord ++ tailWord_8353359).sum := by decide
  have hdescent : baseEnd_8353359 < baseStart_8353359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353453 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_8353453 : Nat := 118140960795 + 8353453 * 2 ^ 59
def prefixEnd_8353453 : Nat := 4983230072969 + 3 ^ 40 * 8353453 * 2
def baseEnd_8353453 : Nat := 4289336513742410810420675

theorem tailTrace_8353453 : CollatzResearch.WordTrace tailWord_8353453 prefixEnd_8353453 4289336513742410810420675 := by
  unfold tailWord_8353453
  simp only [CollatzResearch.WordTrace]
  refine ⟨304675461005873912035609013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203116974003915941357072675 304675461005873912035609013)
  ·
    refine ⟨28563324469300679253338345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304675461005873912035609013 28563324469300679253338345)
    ·
      refine ⟨21422493351975509440003759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28563324469300679253338345 21422493351975509440003759)
      ·
        refine ⟨32133740027963264160005639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21422493351975509440003759 32133740027963264160005639)
        ·
          refine ⟨48200610041944896240008459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32133740027963264160005639 48200610041944896240008459)
          ·
            refine ⟨72300915062917344360012689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48200610041944896240008459 72300915062917344360012689)
            ·
              refine ⟨54225686297188008270009517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72300915062917344360012689 54225686297188008270009517)
              ·
                refine ⟨20334632361445503101253569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54225686297188008270009517 20334632361445503101253569)
                ·
                  refine ⟨15250974271084127325940177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20334632361445503101253569 15250974271084127325940177)
                  ·
                    refine ⟨11438230703313095494455133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15250974271084127325940177 11438230703313095494455133)
                    ·
                      refine ⟨4289336513742410810420675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11438230703313095494455133 4289336513742410810420675)
                      ·
                        rfl

theorem cell23_8353453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_8353453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353453 prefixEnd_8353453 := by exact prefixLift 8353453
  have htrace : WordTrace (prefixWord ++ tailWord_8353453) baseStart_8353453 baseEnd_8353453 := by
    simpa [prefixWord, tailWord_8353453, baseEnd_8353453] using wordTrace_append hprefix tailTrace_8353453
  have hstable : (prefixWord ++ tailWord_8353453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353453).length < 2 ^ (prefixWord ++ tailWord_8353453).sum := by decide
  have hdescent : baseEnd_8353453 < baseStart_8353453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353486 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_8353486 : Nat := 118140960795 + 8353486 * 2 ^ 59
def prefixEnd_8353486 : Nat := 4983230072969 + 3 ^ 40 * 8353486 * 2
def baseEnd_8353486 : Nat := 1429784486201336393769341

theorem tailTrace_8353486 : CollatzResearch.WordTrace tailWord_8353486 prefixEnd_8353486 1429784486201336393769341 := by
  unfold tailWord_8353486
  simp only [CollatzResearch.WordTrace]
  refine ⟨38084583076844294833945039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203117776409836239114373541 38084583076844294833945039)
  ·
    refine ⟨57126874615266442250917559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38084583076844294833945039 57126874615266442250917559)
    ·
      refine ⟨85690311922899663376376339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57126874615266442250917559 85690311922899663376376339)
      ·
        refine ⟨128535467884349495064564509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85690311922899663376376339 128535467884349495064564509)
        ·
          refine ⟨48200800456631060649211691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128535467884349495064564509 48200800456631060649211691)
          ·
            refine ⟨72301200684946590973817537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48200800456631060649211691 72301200684946590973817537)
            ·
              refine ⟨54225900513709943230363153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72301200684946590973817537 54225900513709943230363153)
              ·
                refine ⟨40669425385282457422772365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54225900513709943230363153 40669425385282457422772365)
                ·
                  refine ⟨15251034519480921533539637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40669425385282457422772365 15251034519480921533539637)
                  ·
                    refine ⟨1429784486201336393769341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15251034519480921533539637 1429784486201336393769341)
                    ·
                      rfl

theorem cell23_8353486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_8353486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353486 prefixEnd_8353486 := by exact prefixLift 8353486
  have htrace : WordTrace (prefixWord ++ tailWord_8353486) baseStart_8353486 baseEnd_8353486 := by
    simpa [prefixWord, tailWord_8353486, baseEnd_8353486] using wordTrace_append hprefix tailTrace_8353486
  have hstable : (prefixWord ++ tailWord_8353486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353486).length < 2 ^ (prefixWord ++ tailWord_8353486).sum := by decide
  have hdescent : baseEnd_8353486 < baseStart_8353486 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353490 : List Nat := [3, 2, 2, 2, 2, 3, 2, 1, 6]
def baseStart_8353490 : Nat := 118140960795 + 8353490 * 2 ^ 59
def prefixEnd_8353490 : Nat := 4983230072969 + 3 ^ 40 * 8353490 * 2
def baseEnd_8353490 : Nat := 476595056947403018406445

theorem tailTrace_8353490 : CollatzResearch.WordTrace tailWord_8353490 prefixEnd_8353490 476595056947403018406445 := by
  unfold tailWord_8353490
  simp only [CollatzResearch.WordTrace]
  refine ⟨76169202626684966838676481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203117873671159911569803949 76169202626684966838676481)
  ·
    refine ⟨57126901970013725129007361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76169202626684966838676481 57126901970013725129007361)
    ·
      refine ⟨42845176477510293846755521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57126901970013725129007361 42845176477510293846755521)
      ·
        refine ⟨32133882358132720385066641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42845176477510293846755521 32133882358132720385066641)
        ·
          refine ⟨24100411768599540288799981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32133882358132720385066641 24100411768599540288799981)
          ·
            refine ⟨9037654413224827608299993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24100411768599540288799981 9037654413224827608299993)
            ·
              refine ⟨6778240809918620706224995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9037654413224827608299993 6778240809918620706224995)
              ·
                refine ⟨10167361214877931059337493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6778240809918620706224995 10167361214877931059337493)
                ·
                  refine ⟨476595056947403018406445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10167361214877931059337493 476595056947403018406445)
                  ·
                    rfl

theorem cell23_8353490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_8353490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353490 prefixEnd_8353490 := by exact prefixLift 8353490
  have htrace : WordTrace (prefixWord ++ tailWord_8353490) baseStart_8353490 baseEnd_8353490 := by
    simpa [prefixWord, tailWord_8353490, baseEnd_8353490] using wordTrace_append hprefix tailTrace_8353490
  have hstable : (prefixWord ++ tailWord_8353490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353490).length < 2 ^ (prefixWord ++ tailWord_8353490).sum := by decide
  have hdescent : baseEnd_8353490 < baseStart_8353490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353516 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 6, 4]
def baseStart_8353516 : Nat := 118140960795 + 8353516 * 2 ^ 59
def prefixEnd_8353516 : Nat := 4983230072969 + 3 ^ 40 * 8353516 * 2
def baseEnd_8353516 : Nat := 1429789621007881354644295

theorem tailTrace_8353516 : CollatzResearch.WordTrace tailWord_8353516 prefixEnd_8353516 1429789621007881354644295 := by
  unfold tailWord_8353516
  simp only [CollatzResearch.WordTrace]
  refine ⟨152338879402322836897576201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203118505869763782530101601 152338879402322836897576201)
  ·
    refine ⟨114254159551742127673182151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152338879402322836897576201 114254159551742127673182151)
    ·
      refine ⟨171381239327613191509773227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114254159551742127673182151 171381239327613191509773227)
      ·
        refine ⟨257071858991419787264659841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171381239327613191509773227 257071858991419787264659841)
        ·
          refine ⟨192803894243564840448494881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257071858991419787264659841 192803894243564840448494881)
          ·
            refine ⟨144602920682673630336371161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192803894243564840448494881 144602920682673630336371161)
            ·
              refine ⟨108452190512005222752278371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144602920682673630336371161 108452190512005222752278371)
              ·
                refine ⟨162678285768007834128417557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108452190512005222752278371 162678285768007834128417557)
                ·
                  refine ⟨7625544645375367224769573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162678285768007834128417557 7625544645375367224769573)
                  ·
                    refine ⟨1429789621007881354644295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7625544645375367224769573 1429789621007881354644295)
                    ·
                      rfl

theorem cell23_8353516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_8353516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353516 prefixEnd_8353516 := by exact prefixLift 8353516
  have htrace : WordTrace (prefixWord ++ tailWord_8353516) baseStart_8353516 baseEnd_8353516 := by
    simpa [prefixWord, tailWord_8353516, baseEnd_8353516] using wordTrace_append hprefix tailTrace_8353516
  have hstable : (prefixWord ++ tailWord_8353516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353516).length < 2 ^ (prefixWord ++ tailWord_8353516).sum := by decide
  have hdescent : baseEnd_8353516 < baseStart_8353516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353534 : List Nat := [4, 2, 2, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_8353534 : Nat := 118140960795 + 8353534 * 2 ^ 59
def prefixEnd_8353534 : Nat := 4983230072969 + 3 ^ 40 * 8353534 * 2
def baseEnd_8353534 : Nat := 4289378105675424993507803

theorem tailTrace_8353534 : CollatzResearch.WordTrace tailWord_8353534 prefixEnd_8353534 4289378105675424993507803 := by
  unfold tailWord_8353534
  simp only [CollatzResearch.WordTrace]
  refine ⟨38084801914822557858663457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203118943545720308579538437 38084801914822557858663457)
  ·
    refine ⟨28563601436116918393997593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38084801914822557858663457 28563601436116918393997593)
    ·
      refine ⟨21422701077087688795498195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28563601436116918393997593 21422701077087688795498195)
      ·
        refine ⟨32134051615631533193247293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21422701077087688795498195 32134051615631533193247293)
        ·
          refine ⟨12050269355861824947467735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32134051615631533193247293 12050269355861824947467735)
          ·
            refine ⟨18075404033792737421201603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12050269355861824947467735 18075404033792737421201603)
            ·
              refine ⟨27113106050689106131802405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18075404033792737421201603 27113106050689106131802405)
              ·
                refine ⟨5083707384504207399712951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27113106050689106131802405 5083707384504207399712951)
                ·
                  refine ⟨7625561076756311099569427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5083707384504207399712951 7625561076756311099569427)
                  ·
                    refine ⟨11438341615134466649354141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7625561076756311099569427 11438341615134466649354141)
                    ·
                      refine ⟨4289378105675424993507803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11438341615134466649354141 4289378105675424993507803)
                      ·
                        rfl

theorem cell23_8353534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_8353534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353534 prefixEnd_8353534 := by exact prefixLift 8353534
  have htrace : WordTrace (prefixWord ++ tailWord_8353534) baseStart_8353534 baseEnd_8353534 := by
    simpa [prefixWord, tailWord_8353534, baseEnd_8353534] using wordTrace_append hprefix tailTrace_8353534
  have hstable : (prefixWord ++ tailWord_8353534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353534).length < 2 ^ (prefixWord ++ tailWord_8353534).sum := by decide
  have hdescent : baseEnd_8353534 < baseStart_8353534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353546 : List Nat := [3, 1, 2, 2, 1, 3, 3, 8]
def baseStart_8353546 : Nat := 118140960795 + 8353546 * 2 ^ 59
def prefixEnd_8353546 : Nat := 4983230072969 + 3 ^ 40 * 8353546 * 2
def baseEnd_8353546 : Nat := 158866083979380701724361

theorem tailTrace_8353546 : CollatzResearch.WordTrace tailWord_8353546 prefixEnd_8353546 158866083979380701724361 := by
  unfold tailWord_8353546
  simp only [CollatzResearch.WordTrace]
  refine ⟨76169713248634247229686123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203119235329691325945829661 76169713248634247229686123)
  ·
    refine ⟨114254569872951370844529185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76169713248634247229686123 114254569872951370844529185)
    ·
      refine ⟨85690927404713528133396889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114254569872951370844529185 85690927404713528133396889)
      ·
        refine ⟨64268195553535146100047667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85690927404713528133396889 64268195553535146100047667)
        ·
          refine ⟨96402293330302719150071501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64268195553535146100047667 96402293330302719150071501)
          ·
            refine ⟨36150859998863519681276813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96402293330302719150071501 36150859998863519681276813)
            ·
              refine ⟨13556572499573819880478805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36150859998863519681276813 13556572499573819880478805)
              ·
                refine ⟨158866083979380701724361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13556572499573819880478805 158866083979380701724361)
                ·
                  rfl

theorem cell23_8353546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 8].length) (baseStart_8353546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353546 prefixEnd_8353546 := by exact prefixLift 8353546
  have htrace : WordTrace (prefixWord ++ tailWord_8353546) baseStart_8353546 baseEnd_8353546 := by
    simpa [prefixWord, tailWord_8353546, baseEnd_8353546] using wordTrace_append hprefix tailTrace_8353546
  have hstable : (prefixWord ++ tailWord_8353546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353546).length < 2 ^ (prefixWord ++ tailWord_8353546).sum := by decide
  have hdescent : baseEnd_8353546 < baseStart_8353546 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353573 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 1, 3, 3]
def baseStart_8353573 : Nat := 118140960795 + 8353573 * 2 ^ 59
def prefixEnd_8353573 : Nat := 4983230072969 + 3 ^ 40 * 8353573 * 2
def baseEnd_8353573 : Nat := 4289398131420950340920123

theorem tailTrace_8353573 : CollatzResearch.WordTrace tailWord_8353573 prefixEnd_8353573 4289398131420950340920123 := by
  unfold tailWord_8353573
  simp only [CollatzResearch.WordTrace]
  refine ⟨304679837765439172529977373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203119891843626115019984915 304679837765439172529977373)
  ·
    refine ⟨114254939162039689698741515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304679837765439172529977373 114254939162039689698741515)
    ·
      refine ⟨171382408743059534548112273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114254939162039689698741515 171382408743059534548112273)
      ·
        refine ⟨128536806557294650911084205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171382408743059534548112273 128536806557294650911084205)
        ·
          refine ⟨48201302458985494091656577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128536806557294650911084205 48201302458985494091656577)
          ·
            refine ⟨36150976844239120568742433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48201302458985494091656577 36150976844239120568742433)
            ·
              refine ⟨27113232633179340426556825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36150976844239120568742433 27113232633179340426556825)
              ·
                refine ⟨20334924474884505319917619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27113232633179340426556825 20334924474884505319917619)
                ·
                  refine ⟨30502386712326757979876429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20334924474884505319917619 30502386712326757979876429)
                  ·
                    refine ⟨11438395017122534242453661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30502386712326757979876429 11438395017122534242453661)
                    ·
                      refine ⟨4289398131420950340920123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11438395017122534242453661 4289398131420950340920123)
                      ·
                        rfl

theorem cell23_8353573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_8353573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353573 prefixEnd_8353573 := by exact prefixLift 8353573
  have htrace : WordTrace (prefixWord ++ tailWord_8353573) baseStart_8353573 baseEnd_8353573 := by
    simpa [prefixWord, tailWord_8353573, baseEnd_8353573] using wordTrace_append hprefix tailTrace_8353573
  have hstable : (prefixWord ++ tailWord_8353573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353573).length < 2 ^ (prefixWord ++ tailWord_8353573).sum := by decide
  have hdescent : baseEnd_8353573 < baseStart_8353573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353596 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_8353596 : Nat := 118140960795 + 8353596 * 2 ^ 59
def prefixEnd_8353596 : Nat := 4983230072969 + 3 ^ 40 * 8353596 * 2
def baseEnd_8353596 : Nat := 4289409941476003750932517

theorem tailTrace_8353596 : CollatzResearch.WordTrace tailWord_8353596 prefixEnd_8353596 4289409941476003750932517 := by
  unfold tailWord_8353596
  simp only [CollatzResearch.WordTrace]
  refine ⟨152340338322177923729032321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203120451096237231638709761 152340338322177923729032321)
  ·
    refine ⟨114255253741633442796774241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152340338322177923729032321 114255253741633442796774241)
    ·
      refine ⟨85691440306225082097580681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114255253741633442796774241 85691440306225082097580681)
      ·
        refine ⟨64268580229668811573185511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85691440306225082097580681 64268580229668811573185511)
        ·
          refine ⟨96402870344503217359778267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64268580229668811573185511 96402870344503217359778267)
          ·
            refine ⟨144604305516754826039667401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96402870344503217359778267 144604305516754826039667401)
            ·
              refine ⟨108453229137566119529750551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144604305516754826039667401 108453229137566119529750551)
              ·
                refine ⟨162679843706349179294625827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108453229137566119529750551 162679843706349179294625827)
                ·
                  refine ⟨244019765559523768941938741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162679843706349179294625827 244019765559523768941938741)
                  ·
                    refine ⟨22876853021205353338306757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 244019765559523768941938741 22876853021205353338306757)
                    ·
                      refine ⟨4289409941476003750932517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22876853021205353338306757 4289409941476003750932517)
                      ·
                        rfl

theorem cell23_8353596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_8353596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353596 prefixEnd_8353596 := by exact prefixLift 8353596
  have htrace : WordTrace (prefixWord ++ tailWord_8353596) baseStart_8353596 baseEnd_8353596 := by
    simpa [prefixWord, tailWord_8353596, baseEnd_8353596] using wordTrace_append hprefix tailTrace_8353596
  have hstable : (prefixWord ++ tailWord_8353596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353596).length < 2 ^ (prefixWord ++ tailWord_8353596).sum := by decide
  have hdescent : baseEnd_8353596 < baseStart_8353596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353616 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 5]
def baseStart_8353616 : Nat := 118140960795 + 8353616 * 2 ^ 59
def prefixEnd_8353616 : Nat := 4983230072969 + 3 ^ 40 * 8353616 * 2
def baseEnd_8353616 : Nat := 4289420211089093672682425

theorem tailTrace_8353616 : CollatzResearch.WordTrace tailWord_8353616 prefixEnd_8353616 4289420211089093672682425 := by
  unfold tailWord_8353616
  simp only [CollatzResearch.WordTrace]
  refine ⟨152340703052141695436896351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203120937402855593915861801 152340703052141695436896351)
  ·
    refine ⟨228511054578212543155344527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152340703052141695436896351 228511054578212543155344527)
    ·
      refine ⟨342766581867318814733016791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228511054578212543155344527 342766581867318814733016791)
      ·
        refine ⟨514149872800978222099525187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342766581867318814733016791 514149872800978222099525187)
        ·
          refine ⟨771224809201467333149287781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514149872800978222099525187 771224809201467333149287781)
          ·
            refine ⟨144604651725275124965491459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 771224809201467333149287781 144604651725275124965491459)
            ·
              refine ⟨216906977587912687448237189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144604651725275124965491459 216906977587912687448237189)
              ·
                refine ⟨40670058297733628896544473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216906977587912687448237189 40670058297733628896544473)
                ·
                  refine ⟨30502543723300221672408355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40670058297733628896544473 30502543723300221672408355)
                  ·
                    refine ⟨45753815584950332508612533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30502543723300221672408355 45753815584950332508612533)
                    ·
                      refine ⟨4289420211089093672682425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45753815584950332508612533 4289420211089093672682425)
                      ·
                        rfl

theorem cell23_8353616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_8353616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353616 prefixEnd_8353616 := by exact prefixLift 8353616
  have htrace : WordTrace (prefixWord ++ tailWord_8353616) baseStart_8353616 baseEnd_8353616 := by
    simpa [prefixWord, tailWord_8353616, baseEnd_8353616] using wordTrace_append hprefix tailTrace_8353616
  have hstable : (prefixWord ++ tailWord_8353616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353616).length < 2 ^ (prefixWord ++ tailWord_8353616).sum := by decide
  have hdescent : baseEnd_8353616 < baseStart_8353616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353617 : List Nat := [1, 2, 2, 1, 5, 2, 2, 2, 1, 3, 2]
def baseStart_8353617 : Nat := 118140960795 + 8353617 * 2 ^ 59
def prefixEnd_8353617 : Nat := 4983230072969 + 3 ^ 40 * 8353617 * 2
def baseEnd_8353617 : Nat := 4289420724569748168769921

theorem tailTrace_8353617 : CollatzResearch.WordTrace tailWord_8353617 prefixEnd_8353617 4289420724569748168769921 := by
  unfold tailWord_8353617
  simp only [CollatzResearch.WordTrace]
  refine ⟨304681442577279768044579105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203120961718186512029719403 304681442577279768044579105)
  ·
    refine ⟨228511081932959826033434329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304681442577279768044579105 228511081932959826033434329)
    ·
      refine ⟨171383311449719869525075747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228511081932959826033434329 171383311449719869525075747)
      ·
        refine ⟨257074967174579804287613621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171383311449719869525075747 257074967174579804287613621)
        ·
          refine ⟨24100778172616856651963777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257074967174579804287613621 24100778172616856651963777)
          ·
            refine ⟨18075583629462642488972833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24100778172616856651963777 18075583629462642488972833)
            ·
              refine ⟨13556687722096981866729625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18075583629462642488972833 13556687722096981866729625)
              ·
                refine ⟨10167515791572736400047219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13556687722096981866729625 10167515791572736400047219)
                ·
                  refine ⟨15251273687359104600070829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10167515791572736400047219 15251273687359104600070829)
                  ·
                    refine ⟨5719227632759664225026561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15251273687359104600070829 5719227632759664225026561)
                    ·
                      refine ⟨4289420724569748168769921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5719227632759664225026561 4289420724569748168769921)
                      ·
                        rfl

theorem cell23_8353617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 3, 2].length) (baseStart_8353617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353617 prefixEnd_8353617 := by exact prefixLift 8353617
  have htrace : WordTrace (prefixWord ++ tailWord_8353617) baseStart_8353617 baseEnd_8353617 := by
    simpa [prefixWord, tailWord_8353617, baseEnd_8353617] using wordTrace_append hprefix tailTrace_8353617
  have hstable : (prefixWord ++ tailWord_8353617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353617).length < 2 ^ (prefixWord ++ tailWord_8353617).sum := by decide
  have hdescent : baseEnd_8353617 < baseStart_8353617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353676 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_8353676 : Nat := 118140960795 + 8353676 * 2 ^ 59
def prefixEnd_8353676 : Nat := 4983230072969 + 3 ^ 40 * 8353676 * 2
def baseEnd_8353676 : Nat := 4289451019928363437932149

theorem tailTrace_8353676 : CollatzResearch.WordTrace tailWord_8353676 prefixEnd_8353676 4289451019928363437932149 := by
  unfold tailWord_8353676
  simp only [CollatzResearch.WordTrace]
  refine ⟨152341797242033010560488441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203122396322710680747317921 152341797242033010560488441)
  ·
    refine ⟨114256347931524757920366331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152341797242033010560488441 114256347931524757920366331)
    ·
      refine ⟨171384521897287136880549497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114256347931524757920366331 171384521897287136880549497)
      ·
        refine ⟨128538391422965352660412123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171384521897287136880549497 128538391422965352660412123)
        ·
          refine ⟨192807587134448028990618185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128538391422965352660412123 192807587134448028990618185)
          ·
            refine ⟨144605690350836021742963639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192807587134448028990618185 144605690350836021742963639)
            ·
              refine ⟨216908535526254032614445459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144605690350836021742963639 216908535526254032614445459)
              ·
                refine ⟨325362803289381048921668189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216908535526254032614445459 325362803289381048921668189)
                ·
                  refine ⟨122011051233517893345625571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325362803289381048921668189 122011051233517893345625571)
                  ·
                    refine ⟨183016576850276840018438357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122011051233517893345625571 183016576850276840018438357)
                    ·
                      refine ⟨4289451019928363437932149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183016576850276840018438357 4289451019928363437932149)
                      ·
                        rfl

theorem cell23_8353676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_8353676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353676 prefixEnd_8353676 := by exact prefixLift 8353676
  have htrace : WordTrace (prefixWord ++ tailWord_8353676) baseStart_8353676 baseEnd_8353676 := by
    simpa [prefixWord, tailWord_8353676, baseEnd_8353676] using wordTrace_append hprefix tailTrace_8353676
  have hstable : (prefixWord ++ tailWord_8353676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353676).length < 2 ^ (prefixWord ++ tailWord_8353676).sum := by decide
  have hdescent : baseEnd_8353676 < baseStart_8353676 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353693 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_8353693 : Nat := 118140960795 + 8353693 * 2 ^ 59
def prefixEnd_8353693 : Nat := 4983230072969 + 3 ^ 40 * 8353693 * 2
def baseEnd_8353693 : Nat := 4289459749099489871419571

theorem tailTrace_8353693 : CollatzResearch.WordTrace tailWord_8353693 prefixEnd_8353693 4289459749099489871419571 := by
  unfold tailWord_8353693
  simp only [CollatzResearch.WordTrace]
  refine ⟨304684214525004433024345733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203122809683336288682897155 304684214525004433024345733)
  ·
    refine ⟨57128290223438331192064825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304684214525004433024345733 57128290223438331192064825)
    ·
      refine ⟨42846217667578748394048619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57128290223438331192064825 42846217667578748394048619)
      ·
        refine ⟨64269326501368122591072929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42846217667578748394048619 64269326501368122591072929)
        ·
          refine ⟨48201994876026091943304697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64269326501368122591072929 48201994876026091943304697)
          ·
            refine ⟨36151496157019568957478523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48201994876026091943304697 36151496157019568957478523)
            ·
              refine ⟨54227244235529353436217785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36151496157019568957478523 54227244235529353436217785)
              ·
                refine ⟨40670433176647015077163339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54227244235529353436217785 40670433176647015077163339)
                ·
                  refine ⟨61005649764970522615745009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40670433176647015077163339 61005649764970522615745009)
                  ·
                    refine ⟨45754237323727891961808757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61005649764970522615745009 45754237323727891961808757)
                    ·
                      refine ⟨4289459749099489871419571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45754237323727891961808757 4289459749099489871419571)
                      ·
                        rfl

theorem cell23_8353693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_8353693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353693 prefixEnd_8353693 := by exact prefixLift 8353693
  have htrace : WordTrace (prefixWord ++ tailWord_8353693) baseStart_8353693 baseEnd_8353693 := by
    simpa [prefixWord, tailWord_8353693, baseEnd_8353693] using wordTrace_append hprefix tailTrace_8353693
  have hstable : (prefixWord ++ tailWord_8353693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353693).length < 2 ^ (prefixWord ++ tailWord_8353693).sum := by decide
  have hdescent : baseEnd_8353693 < baseStart_8353693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353704 : List Nat := [2, 1, 6, 2, 1, 1, 1, 4, 5]
def baseStart_8353704 : Nat := 118140960795 + 8353704 * 2 ^ 59
def prefixEnd_8353704 : Nat := 4983230072969 + 3 ^ 40 * 8353704 * 2
def baseEnd_8353704 : Nat := 476607266376298814264669

theorem tailTrace_8353704 : CollatzResearch.WordTrace tailWord_8353704 prefixEnd_8353704 476607266376298814264669 := by
  unfold tailWord_8353704
  simp only [CollatzResearch.WordTrace]
  refine ⟨152342307863982290951498083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203123077151976387935330777 152342307863982290951498083)
  ·
    refine ⟨228513461795973436427247125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152342307863982290951498083 228513461795973436427247125)
    ·
      refine ⟨10711568521686254832527209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228513461795973436427247125 10711568521686254832527209)
      ·
        refine ⟨8033676391264691124395407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10711568521686254832527209 8033676391264691124395407)
        ·
          refine ⟨12050514586897036686593111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8033676391264691124395407 12050514586897036686593111)
          ·
            refine ⟨18075771880345555029889667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12050514586897036686593111 18075771880345555029889667)
            ·
              refine ⟨27113657820518332544834501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18075771880345555029889667 27113657820518332544834501)
              ·
                refine ⟨5083810841347187352156469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27113657820518332544834501 5083810841347187352156469)
                ·
                  refine ⟨476607266376298814264669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5083810841347187352156469 476607266376298814264669)
                  ·
                    rfl

theorem cell23_8353704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 5].length) (baseStart_8353704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353704 prefixEnd_8353704 := by exact prefixLift 8353704
  have htrace : WordTrace (prefixWord ++ tailWord_8353704) baseStart_8353704 baseEnd_8353704 := by
    simpa [prefixWord, tailWord_8353704, baseEnd_8353704] using wordTrace_append hprefix tailTrace_8353704
  have hstable : (prefixWord ++ tailWord_8353704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353704).length < 2 ^ (prefixWord ++ tailWord_8353704).sum := by decide
  have hdescent : baseEnd_8353704 < baseStart_8353704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353720 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 2, 4, 2]
def baseStart_8353720 : Nat := 118140960795 + 8353720 * 2 ^ 59
def prefixEnd_8353720 : Nat := 4983230072969 + 3 ^ 40 * 8353720 * 2
def baseEnd_8353720 : Nat := 4289473613077161265781947

theorem tailTrace_8353720 : CollatzResearch.WordTrace tailWord_8353720 prefixEnd_8353720 4289473613077161265781947 := by
  unfold tailWord_8353720
  simp only [CollatzResearch.WordTrace]
  refine ⟨152342599647953308317789307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203123466197271077757052409 152342599647953308317789307)
  ·
    refine ⟨228513899471929962476683961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152342599647953308317789307 228513899471929962476683961)
    ·
      refine ⟨171385424603947471857512971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228513899471929962476683961 171385424603947471857512971)
      ·
        refine ⟨257078136905921207786269457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171385424603947471857512971 257078136905921207786269457)
        ·
          refine ⟨192808602679440905839702093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257078136905921207786269457 192808602679440905839702093)
          ·
            refine ⟨72303226004790339689888285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192808602679440905839702093 72303226004790339689888285)
            ·
              refine ⟨27113709751796377383708107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72303226004790339689888285 27113709751796377383708107)
              ·
                refine ⟨40670564627694566075562161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27113709751796377383708107 40670564627694566075562161)
                ·
                  refine ⟨30502923470770924556671621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40670564627694566075562161 30502923470770924556671621)
                  ·
                    refine ⟨5719298150769548354375929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30502923470770924556671621 5719298150769548354375929)
                    ·
                      refine ⟨4289473613077161265781947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5719298150769548354375929 4289473613077161265781947)
                      ·
                        rfl

theorem cell23_8353720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 4, 2].length) (baseStart_8353720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353720 prefixEnd_8353720 := by exact prefixLift 8353720
  have htrace : WordTrace (prefixWord ++ tailWord_8353720) baseStart_8353720 baseEnd_8353720 := by
    simpa [prefixWord, tailWord_8353720, baseEnd_8353720] using wordTrace_append hprefix tailTrace_8353720
  have hstable : (prefixWord ++ tailWord_8353720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353720).length < 2 ^ (prefixWord ++ tailWord_8353720).sum := by decide
  have hdescent : baseEnd_8353720 < baseStart_8353720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353723 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 3]
def baseStart_8353723 : Nat := 118140960795 + 8353723 * 2 ^ 59
def prefixEnd_8353723 : Nat := 4983230072969 + 3 ^ 40 * 8353723 * 2
def baseEnd_8353723 : Nat := 4289475153519124754044433

theorem tailTrace_8353723 : CollatzResearch.WordTrace tailWord_8353723 prefixEnd_8353723 4289475153519124754044433 := by
  unfold tailWord_8353723
  simp only [CollatzResearch.WordTrace]
  refine ⟨304685308714895748147937823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203123539143263832098625215 304685308714895748147937823)
  ·
    refine ⟨457027963072343622221906735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304685308714895748147937823 457027963072343622221906735)
    ·
      refine ⟨685541944608515433332860103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457027963072343622221906735 685541944608515433332860103)
      ·
        refine ⟨1028312916912773149999290155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685541944608515433332860103 1028312916912773149999290155)
        ·
          refine ⟨1542469375369159724998935233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028312916912773149999290155 1542469375369159724998935233)
          ·
            refine ⟨1156852031526869793749201425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1542469375369159724998935233 1156852031526869793749201425)
            ·
              refine ⟨867639023645152345311901069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156852031526869793749201425 867639023645152345311901069)
              ·
                refine ⟨325364633866932129491962901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 867639023645152345311901069 325364633866932129491962901)
                ·
                  refine ⟨15251467212512443569935761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 325364633866932129491962901 15251467212512443569935761)
                  ·
                    refine ⟨11438600409384332677451821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15251467212512443569935761 11438600409384332677451821)
                    ·
                      refine ⟨4289475153519124754044433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11438600409384332677451821 4289475153519124754044433)
                      ·
                        rfl

theorem cell23_8353723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 3].length) (baseStart_8353723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353723 prefixEnd_8353723 := by exact prefixLift 8353723
  have htrace : WordTrace (prefixWord ++ tailWord_8353723) baseStart_8353723 baseEnd_8353723 := by
    simpa [prefixWord, tailWord_8353723, baseEnd_8353723] using wordTrace_append hprefix tailTrace_8353723
  have hstable : (prefixWord ++ tailWord_8353723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353723).length < 2 ^ (prefixWord ++ tailWord_8353723).sum := by decide
  have hdescent : baseEnd_8353723 < baseStart_8353723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353740 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 1, 4, 3]
def baseStart_8353740 : Nat := 118140960795 + 8353740 * 2 ^ 59
def prefixEnd_8353740 : Nat := 4983230072969 + 3 ^ 40 * 8353740 * 2
def baseEnd_8353740 : Nat := 4289483882690251187531855

theorem tailTrace_8353740 : CollatzResearch.WordTrace tailWord_8353740 prefixEnd_8353740 4289483882690251187531855 := by
  unfold tailWord_8353740
  simp only [CollatzResearch.WordTrace]
  refine ⟨152342964377917080025653337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203123952503889440034204449 152342964377917080025653337)
  ·
    refine ⟨114257223283437810019240003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152342964377917080025653337 114257223283437810019240003)
    ·
      refine ⟨171385834925156715028860005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114257223283437810019240003 171385834925156715028860005)
      ·
        refine ⟨32134844048466884067911251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171385834925156715028860005 32134844048466884067911251)
        ·
          refine ⟨48202266072700326101866877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32134844048466884067911251 48202266072700326101866877)
          ·
            refine ⟨18075849777262622288200079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48202266072700326101866877 18075849777262622288200079)
            ·
              refine ⟨27113774665893933432300119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18075849777262622288200079 27113774665893933432300119)
              ·
                refine ⟨40670661998840900148450179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27113774665893933432300119 40670661998840900148450179)
                ·
                  refine ⟨61005992998261350222675269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40670661998840900148450179 61005992998261350222675269)
                  ·
                    refine ⟨11438623687174003166751613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61005992998261350222675269 11438623687174003166751613)
                    ·
                      refine ⟨4289483882690251187531855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11438623687174003166751613 4289483882690251187531855)
                      ·
                        rfl

theorem cell23_8353740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_8353740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353740 prefixEnd_8353740 := by exact prefixLift 8353740
  have htrace : WordTrace (prefixWord ++ tailWord_8353740) baseStart_8353740 baseEnd_8353740 := by
    simpa [prefixWord, tailWord_8353740, baseEnd_8353740] using wordTrace_append hprefix tailTrace_8353740
  have hstable : (prefixWord ++ tailWord_8353740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353740).length < 2 ^ (prefixWord ++ tailWord_8353740).sum := by decide
  have hdescent : baseEnd_8353740 < baseStart_8353740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353763 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 6]
def baseStart_8353763 : Nat := 118140960795 + 8353763 * 2 ^ 59
def prefixEnd_8353763 : Nat := 4983230072969 + 3 ^ 40 * 8353763 * 2
def baseEnd_8353763 : Nat := 4289495692745304597544249

theorem tailTrace_8353763 : CollatzResearch.WordTrace tailWord_8353763 prefixEnd_8353763 4289495692745304597544249 := by
  unfold tailWord_8353763
  simp only [CollatzResearch.WordTrace]
  refine ⟨304686767634750834979393943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203124511756500556652929295 304686767634750834979393943)
  ·
    refine ⟨457030151452126252469090915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304686767634750834979393943 457030151452126252469090915)
    ·
      refine ⟨685545227178189378703636373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457030151452126252469090915 685545227178189378703636373)
      ·
        refine ⟨32134932523977627126732955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 685545227178189378703636373 32134932523977627126732955)
        ·
          refine ⟨48202398785966440690099433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32134932523977627126732955 48202398785966440690099433)
          ·
            refine ⟨36151799089474830517574575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48202398785966440690099433 36151799089474830517574575)
            ·
              refine ⟨54227698634212245776361863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36151799089474830517574575 54227698634212245776361863)
              ·
                refine ⟨81341547951318368664542795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54227698634212245776361863 81341547951318368664542795)
                ·
                  refine ⟨122012321926977552996814193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81341547951318368664542795 122012321926977552996814193)
                  ·
                    refine ⟨91509241445233164747610645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122012321926977552996814193 91509241445233164747610645)
                    ·
                      refine ⟨4289495692745304597544249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91509241445233164747610645 4289495692745304597544249)
                      ·
                        rfl

theorem cell23_8353763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_8353763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353763 prefixEnd_8353763 := by exact prefixLift 8353763
  have htrace : WordTrace (prefixWord ++ tailWord_8353763) baseStart_8353763 baseEnd_8353763 := by
    simpa [prefixWord, tailWord_8353763, baseEnd_8353763] using wordTrace_append hprefix tailTrace_8353763
  have hstable : (prefixWord ++ tailWord_8353763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353763).length < 2 ^ (prefixWord ++ tailWord_8353763).sum := by decide
  have hdescent : baseEnd_8353763 < baseStart_8353763 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353777 : List Nat := [1, 2, 2, 2, 5, 1, 3, 1, 6]
def baseStart_8353777 : Nat := 118140960795 + 8353777 * 2 ^ 59
def prefixEnd_8353777 : Nat := 4983230072969 + 3 ^ 40 * 8353777 * 2
def baseEnd_8353777 : Nat := 476611431274940838085465

theorem tailTrace_8353777 : CollatzResearch.WordTrace tailWord_8353777 prefixEnd_8353777 476611431274940838085465 := by
  unfold tailWord_8353777
  simp only [CollatzResearch.WordTrace]
  refine ⟨304687278256700115370403585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203124852171133410246935723 304687278256700115370403585)
  ·
    refine ⟨228515458692525086527802689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304687278256700115370403585 228515458692525086527802689)
    ·
      refine ⟨171386594019393814895852017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228515458692525086527802689 171386594019393814895852017)
      ·
        refine ⟨128539945514545361171889013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171386594019393814895852017 128539945514545361171889013)
        ·
          refine ⟨12050619891988627609864595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128539945514545361171889013 12050619891988627609864595)
          ·
            refine ⟨18075929837982941414796893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12050619891988627609864595 18075929837982941414796893)
            ·
              refine ⟨6778473689243603030548835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18075929837982941414796893 6778473689243603030548835)
              ·
                refine ⟨10167710533865404545823253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6778473689243603030548835 10167710533865404545823253)
                ·
                  refine ⟨476611431274940838085465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10167710533865404545823253 476611431274940838085465)
                  ·
                    rfl

theorem cell23_8353777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 6].length) (baseStart_8353777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353777 prefixEnd_8353777 := by exact prefixLift 8353777
  have htrace : WordTrace (prefixWord ++ tailWord_8353777) baseStart_8353777 baseEnd_8353777 := by
    simpa [prefixWord, tailWord_8353777, baseEnd_8353777] using wordTrace_append hprefix tailTrace_8353777
  have hstable : (prefixWord ++ tailWord_8353777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353777).length < 2 ^ (prefixWord ++ tailWord_8353777).sum := by decide
  have hdescent : baseEnd_8353777 < baseStart_8353777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353803 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 3, 6]
def baseStart_8353803 : Nat := 118140960795 + 8353803 * 2 ^ 59
def prefixEnd_8353803 : Nat := 4983230072969 + 3 ^ 40 * 8353803 * 2
def baseEnd_8353803 : Nat := 1429838743990494813681355

theorem tailTrace_8353803 : CollatzResearch.WordTrace tailWord_8353803 prefixEnd_8353803 1429838743990494813681355 := by
  unfold tailWord_8353803
  simp only [CollatzResearch.WordTrace]
  refine ⟨304688226554605921810850063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203125484369737281207233375 304688226554605921810850063)
  ·
    refine ⟨457032339831908882716275095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304688226554605921810850063 457032339831908882716275095)
    ·
      refine ⟨685548509747863324074412643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457032339831908882716275095 685548509747863324074412643)
      ·
        refine ⟨1028322764621794986111618965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685548509747863324074412643 1028322764621794986111618965)
        ·
          refine ⟨48202629591646639973982139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1028322764621794986111618965 48202629591646639973982139)
          ·
            refine ⟨72303944387469959960973209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48202629591646639973982139 72303944387469959960973209)
            ·
              refine ⟨54227958290602469970729907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72303944387469959960973209 54227958290602469970729907)
              ·
                refine ⟨81341937435903704956094861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54227958290602469970729907 81341937435903704956094861)
                ·
                  refine ⟨30503226538463889358535573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81341937435903704956094861 30503226538463889358535573)
                  ·
                    refine ⟨1429838743990494813681355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30503226538463889358535573 1429838743990494813681355)
                    ·
                      rfl

theorem cell23_8353803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 6].length) (baseStart_8353803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353803 prefixEnd_8353803 := by exact prefixLift 8353803
  have htrace : WordTrace (prefixWord ++ tailWord_8353803) baseStart_8353803 baseEnd_8353803 := by
    simpa [prefixWord, tailWord_8353803, baseEnd_8353803] using wordTrace_append hprefix tailTrace_8353803
  have hstable : (prefixWord ++ tailWord_8353803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353803).length < 2 ^ (prefixWord ++ tailWord_8353803).sum := by decide
  have hdescent : baseEnd_8353803 < baseStart_8353803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353823 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 6]
def baseStart_8353823 : Nat := 118140960795 + 8353823 * 2 ^ 59
def prefixEnd_8353823 : Nat := 4983230072969 + 3 ^ 40 * 8353823 * 2
def baseEnd_8353823 : Nat := 4289526501584574362793973

theorem tailTrace_8353823 : CollatzResearch.WordTrace tailWord_8353823 prefixEnd_8353823 4289526501584574362793973 := by
  unfold tailWord_8353823
  simp only [CollatzResearch.WordTrace]
  refine ⟨304688956014533465226578123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203125970676355643484385415 304688956014533465226578123)
  ·
    refine ⟨457033434021800197839867185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304688956014533465226578123 457033434021800197839867185)
    ·
      refine ⟨342775075516350148379900389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457033434021800197839867185 342775075516350148379900389)
      ·
        refine ⟨64270326659315652821231323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342775075516350148379900389 64270326659315652821231323)
        ·
          refine ⟨96405489988973479231846985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64270326659315652821231323 96405489988973479231846985)
          ·
            refine ⟨72304117491730109423885239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96405489988973479231846985 72304117491730109423885239)
            ·
              refine ⟨108456176237595164135827859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72304117491730109423885239 108456176237595164135827859)
              ·
                refine ⟨162684264356392746203741789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108456176237595164135827859 162684264356392746203741789)
                ·
                  refine ⟨61006599133647279826403171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162684264356392746203741789 61006599133647279826403171)
                  ·
                    refine ⟨91509898700470919739604757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61006599133647279826403171 91509898700470919739604757)
                    ·
                      refine ⟨4289526501584574362793973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91509898700470919739604757 4289526501584574362793973)
                      ·
                        rfl

theorem cell23_8353823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_8353823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353823 prefixEnd_8353823 := by exact prefixLift 8353823
  have htrace : WordTrace (prefixWord ++ tailWord_8353823) baseStart_8353823 baseEnd_8353823 := by
    simpa [prefixWord, tailWord_8353823, baseEnd_8353823] using wordTrace_append hprefix tailTrace_8353823
  have hstable : (prefixWord ++ tailWord_8353823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353823).length < 2 ^ (prefixWord ++ tailWord_8353823).sum := by decide
  have hdescent : baseEnd_8353823 < baseStart_8353823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353844 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_8353844 : Nat := 118140960795 + 8353844 * 2 ^ 59
def prefixEnd_8353844 : Nat := 4983230072969 + 3 ^ 40 * 8353844 * 2
def baseEnd_8353844 : Nat := 4289537284678318780631377

theorem tailTrace_8353844 : CollatzResearch.WordTrace tailWord_8353844 prefixEnd_8353844 4289537284678318780631377 := by
  unfold tailWord_8353844
  simp only [CollatzResearch.WordTrace]
  refine ⟨152344860973728692906546293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203126481298304923875395057 152344860973728692906546293)
  ·
    refine ⟨14282330716287064959988715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152344860973728692906546293 14282330716287064959988715)
    ·
      refine ⟨21423496074430597439983073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14282330716287064959988715 21423496074430597439983073)
      ·
        refine ⟨16067622055822948079987305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21423496074430597439983073 16067622055822948079987305)
        ·
          refine ⟨12050716541867211059990479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16067622055822948079987305 12050716541867211059990479)
          ·
            refine ⟨18076074812800816589985719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12050716541867211059990479 18076074812800816589985719)
            ·
              refine ⟨27114112219201224884978579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18076074812800816589985719 27114112219201224884978579)
              ·
                refine ⟨40671168328801837327467869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27114112219201224884978579 40671168328801837327467869)
                ·
                  refine ⟨15251688123300688997800451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40671168328801837327467869 15251688123300688997800451)
                  ·
                    refine ⟨22877532184951033496700677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15251688123300688997800451 22877532184951033496700677)
                    ·
                      refine ⟨4289537284678318780631377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22877532184951033496700677 4289537284678318780631377)
                      ·
                        rfl

theorem cell23_8353844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_8353844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353844 prefixEnd_8353844 := by exact prefixLift 8353844
  have htrace : WordTrace (prefixWord ++ tailWord_8353844) baseStart_8353844 baseEnd_8353844 := by
    simpa [prefixWord, tailWord_8353844, baseEnd_8353844] using wordTrace_append hprefix tailTrace_8353844
  have hstable : (prefixWord ++ tailWord_8353844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353844).length < 2 ^ (prefixWord ++ tailWord_8353844).sum := by decide
  have hdescent : baseEnd_8353844 < baseStart_8353844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353847 : List Nat := [1, 1, 3, 1, 2, 2, 5, 2, 1, 2, 3]
def baseStart_8353847 : Nat := 118140960795 + 8353847 * 2 ^ 59
def prefixEnd_8353847 : Nat := 4983230072969 + 3 ^ 40 * 8353847 * 2
def baseEnd_8353847 : Nat := 4289538825120282268893863

theorem tailTrace_8353847 : CollatzResearch.WordTrace tailWord_8353847 prefixEnd_8353847 4289538825120282268893863 := by
  unfold tailWord_8353847
  simp only [CollatzResearch.WordTrace]
  refine ⟨304689831366446517325451795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203126554244297678216967863 304689831366446517325451795)
  ·
    refine ⟨457034747049669775988177693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304689831366446517325451795 457034747049669775988177693)
    ·
      refine ⟨171388030143626165995566635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457034747049669775988177693 171388030143626165995566635)
      ·
        refine ⟨257082045215439248993349953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171388030143626165995566635 257082045215439248993349953)
        ·
          refine ⟨192811533911579436745012465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257082045215439248993349953 192811533911579436745012465)
          ·
            refine ⟨144608650433684577558759349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192811533911579436745012465 144608650433684577558759349)
            ·
              refine ⟨13557060978157929146133689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144608650433684577558759349 13557060978157929146133689)
              ·
                refine ⟨10167795733618446859600267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13557060978157929146133689 10167795733618446859600267)
                ·
                  refine ⟨15251693600427670289400401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10167795733618446859600267 15251693600427670289400401)
                  ·
                    refine ⟨11438770200320752717050301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15251693600427670289400401 11438770200320752717050301)
                    ·
                      refine ⟨4289538825120282268893863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11438770200320752717050301 4289538825120282268893863)
                      ·
                        rfl

theorem cell23_8353847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_8353847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353847 prefixEnd_8353847 := by exact prefixLift 8353847
  have htrace : WordTrace (prefixWord ++ tailWord_8353847) baseStart_8353847 baseEnd_8353847 := by
    simpa [prefixWord, tailWord_8353847, baseEnd_8353847] using wordTrace_append hprefix tailTrace_8353847
  have hstable : (prefixWord ++ tailWord_8353847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353847).length < 2 ^ (prefixWord ++ tailWord_8353847).sum := by decide
  have hdescent : baseEnd_8353847 < baseStart_8353847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353857 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_8353857 : Nat := 118140960795 + 8353857 * 2 ^ 59
def prefixEnd_8353857 : Nat := 4983230072969 + 3 ^ 40 * 8353857 * 2
def baseEnd_8353857 : Nat := 4289543959926827229768817

theorem tailTrace_8353857 : CollatzResearch.WordTrace tailWord_8353857 prefixEnd_8353857 4289543959926827229768817 := by
  unfold tailWord_8353857
  simp only [CollatzResearch.WordTrace]
  refine ⟨304690196096410289033315825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203126797397606859355543883 304690196096410289033315825)
  ·
    refine ⟨228517647072307716774986869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304690196096410289033315825 228517647072307716774986869)
    ·
      refine ⟨21423529413028848447655019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228517647072307716774986869 21423529413028848447655019)
      ·
        refine ⟨32135294119543272671482529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21423529413028848447655019 32135294119543272671482529)
        ·
          refine ⟨24101470589657454503611897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32135294119543272671482529 24101470589657454503611897)
          ·
            refine ⟨18076102942243090877708923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24101470589657454503611897 18076102942243090877708923)
            ·
              refine ⟨27114154413364636316563385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18076102942243090877708923 27114154413364636316563385)
              ·
                refine ⟨20335615810023477237422539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27114154413364636316563385 20335615810023477237422539)
                ·
                  refine ⟨30503423715035215856133809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20335615810023477237422539 30503423715035215856133809)
                  ·
                    refine ⟨22877567786276411892100357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30503423715035215856133809 22877567786276411892100357)
                    ·
                      refine ⟨4289543959926827229768817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22877567786276411892100357 4289543959926827229768817)
                      ·
                        rfl

theorem cell23_8353857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_8353857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353857 prefixEnd_8353857 := by exact prefixLift 8353857
  have htrace : WordTrace (prefixWord ++ tailWord_8353857) baseStart_8353857 baseEnd_8353857 := by
    simpa [prefixWord, tailWord_8353857, baseEnd_8353857] using wordTrace_append hprefix tailTrace_8353857
  have hstable : (prefixWord ++ tailWord_8353857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353857).length < 2 ^ (prefixWord ++ tailWord_8353857).sum := by decide
  have hdescent : baseEnd_8353857 < baseStart_8353857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353921 : List Nat := [1, 2, 4, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_8353921 : Nat := 118140960795 + 8353921 * 2 ^ 59
def prefixEnd_8353921 : Nat := 4983230072969 + 3 ^ 40 * 8353921 * 2
def baseEnd_8353921 : Nat := 4289576822688714979368523

theorem tailTrace_8353921 : CollatzResearch.WordTrace tailWord_8353921 prefixEnd_8353921 4289576822688714979368523 := by
  unfold tailWord_8353921
  simp only [CollatzResearch.WordTrace]
  refine ⟨304692530368178427963645617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203128353578785618642430411 304692530368178427963645617)
  ·
    refine ⟨228519397776133820972734213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304692530368178427963645617 228519397776133820972734213)
    ·
      refine ⟨42847387083025091432387665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228519397776133820972734213 42847387083025091432387665)
      ·
        refine ⟨32135540312268818574290749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42847387083025091432387665 32135540312268818574290749)
        ·
          refine ⟨12050827617100806965359031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32135540312268818574290749 12050827617100806965359031)
          ·
            refine ⟨18076241425651210448038547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12050827617100806965359031 18076241425651210448038547)
            ·
              refine ⟨27114362138476815672057821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18076241425651210448038547 27114362138476815672057821)
              ·
                refine ⟨10167885801928805877021683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27114362138476815672057821 10167885801928805877021683)
                ·
                  refine ⟨15251828702893208815532525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10167885801928805877021683 15251828702893208815532525)
                  ·
                    refine ⟨5719435763584953305824697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15251828702893208815532525 5719435763584953305824697)
                    ·
                      refine ⟨4289576822688714979368523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5719435763584953305824697 4289576822688714979368523)
                      ·
                        rfl

theorem cell23_8353921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_8353921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353921 prefixEnd_8353921 := by exact prefixLift 8353921
  have htrace : WordTrace (prefixWord ++ tailWord_8353921) baseStart_8353921 baseEnd_8353921 := by
    simpa [prefixWord, tailWord_8353921, baseEnd_8353921] using wordTrace_append hprefix tailTrace_8353921
  have hstable : (prefixWord ++ tailWord_8353921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353921).length < 2 ^ (prefixWord ++ tailWord_8353921).sum := by decide
  have hdescent : baseEnd_8353921 < baseStart_8353921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353942 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_8353942 : Nat := 118140960795 + 8353942 * 2 ^ 59
def prefixEnd_8353942 : Nat := 4983230072969 + 3 ^ 40 * 8353942 * 2
def baseEnd_8353942 : Nat := 4289587605782459397205927

theorem tailTrace_8353942 : CollatzResearch.WordTrace tailWord_8353942 prefixEnd_8353942 4289587605782459397205927 := by
  unfold tailWord_8353942
  simp only [CollatzResearch.WordTrace]
  refine ⟨19043331018818896784385005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203128864200734899033440053 19043331018818896784385005)
  ·
    refine ⟨7141249132057086294144377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19043331018818896784385005 7141249132057086294144377)
    ·
      refine ⟨5355936849042814720608283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7141249132057086294144377 5355936849042814720608283)
      ·
        refine ⟨8033905273564222080912425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5355936849042814720608283 8033905273564222080912425)
        ·
          refine ⟨6025428955173166560684319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8033905273564222080912425 6025428955173166560684319)
          ·
            refine ⟨9038143432759749841026479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6025428955173166560684319 9038143432759749841026479)
            ·
              refine ⟨13557215149139624761539719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9038143432759749841026479 13557215149139624761539719)
              ·
                refine ⟨20335822723709437142309579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13557215149139624761539719 20335822723709437142309579)
                ·
                  refine ⟨30503734085564155713464369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20335822723709437142309579 30503734085564155713464369)
                  ·
                    refine ⟨22877800564173116785098277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30503734085564155713464369 22877800564173116785098277)
                    ·
                      refine ⟨4289587605782459397205927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22877800564173116785098277 4289587605782459397205927)
                      ·
                        rfl

theorem cell23_8353942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_8353942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353942 prefixEnd_8353942 := by exact prefixLift 8353942
  have htrace : WordTrace (prefixWord ++ tailWord_8353942) baseStart_8353942 baseEnd_8353942 := by
    simpa [prefixWord, tailWord_8353942, baseEnd_8353942] using wordTrace_append hprefix tailTrace_8353942
  have hstable : (prefixWord ++ tailWord_8353942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353942).length < 2 ^ (prefixWord ++ tailWord_8353942).sum := by decide
  have hdescent : baseEnd_8353942 < baseStart_8353942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353951 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 1, 4, 2]
def baseStart_8353951 : Nat := 118140960795 + 8353951 * 2 ^ 59
def prefixEnd_8353951 : Nat := 4983230072969 + 3 ^ 40 * 8353951 * 2
def baseEnd_8353951 : Nat := 4289592227108349861993385

theorem tailTrace_8353951 : CollatzResearch.WordTrace tailWord_8353951 prefixEnd_8353951 4289592227108349861993385 := by
  unfold tailWord_8353951
  simp only [CollatzResearch.WordTrace]
  refine ⟨304693624558069743087237707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203129083038713162058158471 304693624558069743087237707)
  ·
    refine ⟨457040436837104614630856561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304693624558069743087237707 457040436837104614630856561)
    ·
      refine ⟨342780327627828460973142421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457040436837104614630856561 342780327627828460973142421)
      ·
        refine ⟨16067827857554459108116051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 342780327627828460973142421 16067827857554459108116051)
        ·
          refine ⟨24101741786331688662174077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16067827857554459108116051 24101741786331688662174077)
          ·
            refine ⟨9038153169874383248315279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24101741786331688662174077 9038153169874383248315279)
            ·
              refine ⟨13557229754811574872472919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9038153169874383248315279 13557229754811574872472919)
              ·
                refine ⟨20335844632217362308709379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13557229754811574872472919 20335844632217362308709379)
                ·
                  refine ⟨30503766948326043463064069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20335844632217362308709379 30503766948326043463064069)
                  ·
                    refine ⟨5719456302811133149324513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30503766948326043463064069 5719456302811133149324513)
                    ·
                      refine ⟨4289592227108349861993385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5719456302811133149324513 4289592227108349861993385)
                      ·
                        rfl

theorem cell23_8353951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_8353951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353951 prefixEnd_8353951 := by exact prefixLift 8353951
  have htrace : WordTrace (prefixWord ++ tailWord_8353951) baseStart_8353951 baseEnd_8353951 := by
    simpa [prefixWord, tailWord_8353951, baseEnd_8353951] using wordTrace_append hprefix tailTrace_8353951
  have hstable : (prefixWord ++ tailWord_8353951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353951).length < 2 ^ (prefixWord ++ tailWord_8353951).sum := by decide
  have hdescent : baseEnd_8353951 < baseStart_8353951 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8353970 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_8353970 : Nat := 118140960795 + 8353970 * 2 ^ 59
def prefixEnd_8353970 : Nat := 4983230072969 + 3 ^ 40 * 8353970 * 2
def baseEnd_8353970 : Nat := 1429867327746928429218599

theorem tailTrace_8353970 : CollatzResearch.WordTrace tailWord_8353970 prefixEnd_8353970 1429867327746928429218599 := by
  unfold tailWord_8353970
  simp only [CollatzResearch.WordTrace]
  refine ⟨76173579386250227333044841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203129545030000606221452909 76173579386250227333044841)
  ·
    refine ⟨57130184539687670499783631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76173579386250227333044841 57130184539687670499783631)
    ·
      refine ⟨85695276809531505749675447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57130184539687670499783631 85695276809531505749675447)
      ·
        refine ⟨128542915214297258624513171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85695276809531505749675447 128542915214297258624513171)
        ·
          refine ⟨192814372821445887936769757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128542915214297258624513171 192814372821445887936769757)
          ·
            refine ⟨72305389808042207976288659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192814372821445887936769757 72305389808042207976288659)
            ·
              refine ⟨108458084712063311964432989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72305389808042207976288659 108458084712063311964432989)
              ·
                refine ⟨40671781767023741986662371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108458084712063311964432989 40671781767023741986662371)
                ·
                  refine ⟨61007672650535612979993557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40671781767023741986662371 61007672650535612979993557)
                  ·
                    refine ⟨1429867327746928429218599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61007672650535612979993557 1429867327746928429218599)
                    ·
                      rfl

theorem cell23_8353970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_8353970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8353970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8353970 prefixEnd_8353970 := by exact prefixLift 8353970
  have htrace : WordTrace (prefixWord ++ tailWord_8353970) baseStart_8353970 baseEnd_8353970 := by
    simpa [prefixWord, tailWord_8353970, baseEnd_8353970] using wordTrace_append hprefix tailTrace_8353970
  have hstable : (prefixWord ++ tailWord_8353970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8353970).length < 2 ^ (prefixWord ++ tailWord_8353970).sum := by decide
  have hdescent : baseEnd_8353970 < baseStart_8353970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8353970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354007 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 1, 6, 2]
def baseStart_8354007 : Nat := 118140960795 + 8354007 * 2 ^ 59
def prefixEnd_8354007 : Nat := 4983230072969 + 3 ^ 40 * 8354007 * 2
def baseEnd_8354007 : Nat := 4289620982025001642893127

theorem tailTrace_8354007 : CollatzResearch.WordTrace tailWord_8354007 prefixEnd_8354007 4289620982025001642893127 := by
  unfold tailWord_8354007
  simp only [CollatzResearch.WordTrace]
  refine ⟨304695667045866864651276275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203130444697244576434184183 304695667045866864651276275)
  ·
    refine ⟨457043500568800296976914413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304695667045866864651276275 457043500568800296976914413)
    ·
      refine ⟨171391312713300111366342905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457043500568800296976914413 171391312713300111366342905)
      ·
        refine ⟨128543484534975083524757179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171391312713300111366342905 128543484534975083524757179)
        ·
          refine ⟨192815226802462625287135769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128543484534975083524757179 192815226802462625287135769)
          ·
            refine ⟨144611420101846968965351827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192815226802462625287135769 144611420101846968965351827)
            ·
              refine ⟨216917130152770453448027741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144611420101846968965351827 216917130152770453448027741)
              ·
                refine ⟨81343923807288920043010403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216917130152770453448027741 81343923807288920043010403)
                ·
                  refine ⟨122015885710933380064515605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81343923807288920043010403 122015885710933380064515605)
                  ·
                    refine ⟨5719494642700002190524169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122015885710933380064515605 5719494642700002190524169)
                    ·
                      refine ⟨4289620982025001642893127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5719494642700002190524169 4289620982025001642893127)
                      ·
                        rfl

theorem cell23_8354007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_8354007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354007 prefixEnd_8354007 := by exact prefixLift 8354007
  have htrace : WordTrace (prefixWord ++ tailWord_8354007) baseStart_8354007 baseEnd_8354007 := by
    simpa [prefixWord, tailWord_8354007, baseEnd_8354007] using wordTrace_append hprefix tailTrace_8354007
  have hstable : (prefixWord ++ tailWord_8354007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354007).length < 2 ^ (prefixWord ++ tailWord_8354007).sum := by decide
  have hdescent : baseEnd_8354007 < baseStart_8354007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354017 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 5, 4]
def baseStart_8354017 : Nat := 118140960795 + 8354017 * 2 ^ 59
def prefixEnd_8354017 : Nat := 4983230072969 + 3 ^ 40 * 8354017 * 2
def baseEnd_8354017 : Nat := 1429875372277182201256027

theorem tailTrace_8354017 : CollatzResearch.WordTrace tailWord_8354017 prefixEnd_8354017 1429875372277182201256027 := by
  unfold tailWord_8354017
  simp only [CollatzResearch.WordTrace]
  refine ⟨304696031775830636359140305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203130687850553757572760203 304696031775830636359140305)
  ·
    refine ⟨228522023831872977269355229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304696031775830636359140305 228522023831872977269355229)
    ·
      refine ⟨85695758936952366476008211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228522023831872977269355229 85695758936952366476008211)
      ·
        refine ⟨128543638405428549714012317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85695758936952366476008211 128543638405428549714012317)
        ·
          refine ⟨48203864402035706142754619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128543638405428549714012317 48203864402035706142754619)
          ·
            refine ⟨72305796603053559214131929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48203864402035706142754619 72305796603053559214131929)
            ·
              refine ⟨54229347452290169410598947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72305796603053559214131929 54229347452290169410598947)
              ·
                refine ⟨81344021178435254115898421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54229347452290169410598947 81344021178435254115898421)
                ·
                  refine ⟨7626001985478305073365477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81344021178435254115898421 7626001985478305073365477)
                  ·
                    refine ⟨1429875372277182201256027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7626001985478305073365477 1429875372277182201256027)
                    ·
                      rfl

theorem cell23_8354017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_8354017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354017 prefixEnd_8354017 := by exact prefixLift 8354017
  have htrace : WordTrace (prefixWord ++ tailWord_8354017) baseStart_8354017 baseEnd_8354017 := by
    simpa [prefixWord, tailWord_8354017, baseEnd_8354017] using wordTrace_append hprefix tailTrace_8354017
  have hstable : (prefixWord ++ tailWord_8354017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354017).length < 2 ^ (prefixWord ++ tailWord_8354017).sum := by decide
  have hdescent : baseEnd_8354017 < baseStart_8354017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354020 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_8354020 : Nat := 118140960795 + 8354020 * 2 ^ 59
def prefixEnd_8354020 : Nat := 4983230072969 + 3 ^ 40 * 8354020 * 2
def baseEnd_8354020 : Nat := 4289627657273510092030567

theorem tailTrace_8354020 : CollatzResearch.WordTrace tailWord_8354020 prefixEnd_8354020 4289627657273510092030567 := by
  unfold tailWord_8354020
  simp only [CollatzResearch.WordTrace]
  refine ⟨152348070597409883935749757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203130760796546511914333009 152348070597409883935749757)
  ·
    refine ⟨57130526474028706475906159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152348070597409883935749757 57130526474028706475906159)
    ·
      refine ⟨85695789711043059713859239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57130526474028706475906159 85695789711043059713859239)
      ·
        refine ⟨128543684566564589570788859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85695789711043059713859239 128543684566564589570788859)
        ·
          refine ⟨192815526849846884356183289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128543684566564589570788859 192815526849846884356183289)
          ·
            refine ⟨144611645137385163267137467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192815526849846884356183289 144611645137385163267137467)
            ·
              refine ⟨216917467706077744900706201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144611645137385163267137467 216917467706077744900706201)
              ·
                refine ⟨162688100779558308675529651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216917467706077744900706201 162688100779558308675529651)
                ·
                  refine ⟨244032151169337463013294477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162688100779558308675529651 244032151169337463013294477)
                  ·
                    refine ⟨91512056688501548629985429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244032151169337463013294477 91512056688501548629985429)
                    ·
                      refine ⟨4289627657273510092030567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91512056688501548629985429 4289627657273510092030567)
                      ·
                        rfl

theorem cell23_8354020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_8354020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354020 prefixEnd_8354020 := by exact prefixLift 8354020
  have htrace : WordTrace (prefixWord ++ tailWord_8354020) baseStart_8354020 baseEnd_8354020 := by
    simpa [prefixWord, tailWord_8354020, baseEnd_8354020] using wordTrace_append hprefix tailTrace_8354020
  have hstable : (prefixWord ++ tailWord_8354020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354020).length < 2 ^ (prefixWord ++ tailWord_8354020).sum := by decide
  have hdescent : baseEnd_8354020 < baseStart_8354020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354024 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_8354024 : Nat := 118140960795 + 8354024 * 2 ^ 59
def prefixEnd_8354024 : Nat := 4983230072969 + 3 ^ 40 * 8354024 * 2
def baseEnd_8354024 : Nat := 4289629711196128076380549

theorem tailTrace_8354024 : CollatzResearch.WordTrace tailWord_8354024 prefixEnd_8354024 4289629711196128076380549 := by
  unfold tailWord_8354024
  simp only [CollatzResearch.WordTrace]
  refine ⟨152348143543402638277322563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203130858057870184369763417 152348143543402638277322563)
  ·
    refine ⟨228522215315103957415983845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152348143543402638277322563 228522215315103957415983845)
    ·
      refine ⟨42847915371581992015496971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228522215315103957415983845 42847915371581992015496971)
      ·
        refine ⟨64271873057372988023245457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42847915371581992015496971 64271873057372988023245457)
        ·
          refine ⟨48203904793029741017434093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64271873057372988023245457 48203904793029741017434093)
          ·
            refine ⟨18076464297386152881537785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48203904793029741017434093 18076464297386152881537785)
            ·
              refine ⟨13557348223039614661153339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18076464297386152881537785 13557348223039614661153339)
              ·
                refine ⟨20336022334559421991730009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13557348223039614661153339 20336022334559421991730009)
                ·
                  refine ⟨15252016750919566493797507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20336022334559421991730009 15252016750919566493797507)
                  ·
                    refine ⟨22878025126379349740696261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15252016750919566493797507 22878025126379349740696261)
                    ·
                      refine ⟨4289629711196128076380549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22878025126379349740696261 4289629711196128076380549)
                      ·
                        rfl

theorem cell23_8354024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_8354024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354024 prefixEnd_8354024 := by exact prefixLift 8354024
  have htrace : WordTrace (prefixWord ++ tailWord_8354024) baseStart_8354024 baseEnd_8354024 := by
    simpa [prefixWord, tailWord_8354024, baseEnd_8354024] using wordTrace_append hprefix tailTrace_8354024
  have hstable : (prefixWord ++ tailWord_8354024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354024).length < 2 ^ (prefixWord ++ tailWord_8354024).sum := by decide
  have hdescent : baseEnd_8354024 < baseStart_8354024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354044 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_8354044 : Nat := 118140960795 + 8354044 * 2 ^ 59
def prefixEnd_8354044 : Nat := 4983230072969 + 3 ^ 40 * 8354044 * 2
def baseEnd_8354044 : Nat := 4289639980809217998130457

theorem tailTrace_8354044 : CollatzResearch.WordTrace tailWord_8354044 prefixEnd_8354044 4289639980809217998130457 := by
  unfold tailWord_8354044
  simp only [CollatzResearch.WordTrace]
  refine ⟨152348508273366409985186593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203131344364488546646915457 152348508273366409985186593)
  ·
    refine ⟨114261381205024807488889945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152348508273366409985186593 114261381205024807488889945)
    ·
      refine ⟨85696035903768605616667459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114261381205024807488889945 85696035903768605616667459)
      ·
        refine ⟨128544053855652908425001189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85696035903768605616667459 128544053855652908425001189)
        ·
          refine ⟨24102010097934920329687723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128544053855652908425001189 24102010097934920329687723)
          ·
            refine ⟨36153015146902380494531585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24102010097934920329687723 36153015146902380494531585)
            ·
              refine ⟨27114761360176785370898689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36153015146902380494531585 27114761360176785370898689)
              ·
                refine ⟨20336071020132589028174017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27114761360176785370898689 20336071020132589028174017)
                ·
                  refine ⟨15252053265099441771130513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20336071020132589028174017 15252053265099441771130513)
                  ·
                    refine ⟨11439039948824581328347885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15252053265099441771130513 11439039948824581328347885)
                    ·
                      refine ⟨4289639980809217998130457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11439039948824581328347885 4289639980809217998130457)
                      ·
                        rfl

theorem cell23_8354044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_8354044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354044 prefixEnd_8354044 := by exact prefixLift 8354044
  have htrace : WordTrace (prefixWord ++ tailWord_8354044) baseStart_8354044 baseEnd_8354044 := by
    simpa [prefixWord, tailWord_8354044, baseEnd_8354044] using wordTrace_append hprefix tailTrace_8354044
  have hstable : (prefixWord ++ tailWord_8354044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354044).length < 2 ^ (prefixWord ++ tailWord_8354044).sum := by decide
  have hdescent : baseEnd_8354044 < baseStart_8354044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354047 : List Nat := [1, 1, 2, 2, 1, 4, 4, 2, 6]
def baseStart_8354047 : Nat := 118140960795 + 8354047 * 2 ^ 59
def prefixEnd_8354047 : Nat := 4983230072969 + 3 ^ 40 * 8354047 * 2
def baseEnd_8354047 : Nat := 476626835694575720710327

theorem tailTrace_8354047 : CollatzResearch.WordTrace tailWord_8354047 prefixEnd_8354047 476626835694575720710327 := by
  unfold tailWord_8354047
  simp only [CollatzResearch.WordTrace]
  refine ⟨304697125965721951482732395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203131417310481300988488263 304697125965721951482732395)
  ·
    refine ⟨457045688948582927224098593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304697125965721951482732395 457045688948582927224098593)
    ·
      refine ⟨342784266711437195418073945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457045688948582927224098593 342784266711437195418073945)
      ·
        refine ⟨257088200033577896563555459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342784266711437195418073945 257088200033577896563555459)
        ·
          refine ⟨385632300050366844845333189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257088200033577896563555459 385632300050366844845333189)
          ·
            refine ⟨72306056259443783408499973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 385632300050366844845333189 72306056259443783408499973)
            ·
              refine ⟨13557385548645709389093745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72306056259443783408499973 13557385548645709389093745)
              ·
                refine ⟨10168039161484282041820309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13557385548645709389093745 10168039161484282041820309)
                ·
                  refine ⟨476626835694575720710327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10168039161484282041820309 476626835694575720710327)
                  ·
                    rfl

theorem cell23_8354047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 6].length) (baseStart_8354047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354047 prefixEnd_8354047 := by exact prefixLift 8354047
  have htrace : WordTrace (prefixWord ++ tailWord_8354047) baseStart_8354047 baseEnd_8354047 := by
    simpa [prefixWord, tailWord_8354047, baseEnd_8354047] using wordTrace_append hprefix tailTrace_8354047
  have hstable : (prefixWord ++ tailWord_8354047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354047).length < 2 ^ (prefixWord ++ tailWord_8354047).sum := by decide
  have hdescent : baseEnd_8354047 < baseStart_8354047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354078 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_8354078 : Nat := 118140960795 + 8354078 * 2 ^ 59
def prefixEnd_8354078 : Nat := 4983230072969 + 3 ^ 40 * 8354078 * 2
def baseEnd_8354078 : Nat := 4289657439151470865105301

theorem tailTrace_8354078 : CollatzResearch.WordTrace tailWord_8354078 prefixEnd_8354078 4289657439151470865105301 := by
  unfold tailWord_8354078
  simp only [CollatzResearch.WordTrace]
  refine ⟨38087282078576205472138861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203132171085739762518073925 38087282078576205472138861)
  ·
    refine ⟨14282730779466077052052073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38087282078576205472138861 14282730779466077052052073)
    ·
      refine ⟨10712048084599557789039055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14282730779466077052052073 10712048084599557789039055)
      ·
        refine ⟨16068072126899336683558583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10712048084599557789039055 16068072126899336683558583)
        ·
          refine ⟨24102108190349005025337875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16068072126899336683558583 24102108190349005025337875)
          ·
            refine ⟨36153162285523507538006813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24102108190349005025337875 36153162285523507538006813)
            ·
              refine ⟨13557435857071315326752555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36153162285523507538006813 13557435857071315326752555)
              ·
                refine ⟨20336153785606972990128833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13557435857071315326752555 20336153785606972990128833)
                ·
                  refine ⟨15252115339205229742596625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20336153785606972990128833 15252115339205229742596625)
                  ·
                    refine ⟨11439086504403922306947469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15252115339205229742596625 11439086504403922306947469)
                    ·
                      refine ⟨4289657439151470865105301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11439086504403922306947469 4289657439151470865105301)
                      ·
                        rfl

theorem cell23_8354078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_8354078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354078 prefixEnd_8354078 := by exact prefixLift 8354078
  have htrace : WordTrace (prefixWord ++ tailWord_8354078) baseStart_8354078 baseEnd_8354078 := by
    simpa [prefixWord, tailWord_8354078, baseEnd_8354078] using wordTrace_append hprefix tailTrace_8354078
  have hstable : (prefixWord ++ tailWord_8354078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354078).length < 2 ^ (prefixWord ++ tailWord_8354078).sum := by decide
  have hdescent : baseEnd_8354078 < baseStart_8354078 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354127 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 4]
def baseStart_8354127 : Nat := 118140960795 + 8354127 * 2 ^ 59
def prefixEnd_8354127 : Nat := 4983230072969 + 3 ^ 40 * 8354127 * 2
def baseEnd_8354127 : Nat := 4289682599703541173392575

theorem tailTrace_8354127 : CollatzResearch.WordTrace tailWord_8354127 prefixEnd_8354127 4289682599703541173392575 := by
  unfold tailWord_8354127
  simp only [CollatzResearch.WordTrace]
  refine ⟨304700043805432125145644635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203133362536954750097096423 304700043805432125145644635)
  ·
    refine ⟨457050065708148187718466953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304700043805432125145644635 457050065708148187718466953)
    ·
      refine ⟨342787549281111140788850215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457050065708148187718466953 342787549281111140788850215)
      ·
        refine ⟨514181323921666711183275323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342787549281111140788850215 514181323921666711183275323)
        ·
          refine ⟨771271985882500066774912985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514181323921666711183275323 771271985882500066774912985)
          ·
            refine ⟨578453989411875050081184739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 771271985882500066774912985 578453989411875050081184739)
            ·
              refine ⟨867680984117812575121777109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578453989411875050081184739 867680984117812575121777109)
              ·
                refine ⟨20336273065261232229416651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 867680984117812575121777109 20336273065261232229416651)
                ·
                  refine ⟨30504409597891848344124977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20336273065261232229416651 30504409597891848344124977)
                  ·
                    refine ⟨22878307198418886258093733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30504409597891848344124977 22878307198418886258093733)
                    ·
                      refine ⟨4289682599703541173392575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22878307198418886258093733 4289682599703541173392575)
                      ·
                        rfl

theorem cell23_8354127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_8354127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354127 prefixEnd_8354127 := by exact prefixLift 8354127
  have htrace : WordTrace (prefixWord ++ tailWord_8354127) baseStart_8354127 baseEnd_8354127 := by
    simpa [prefixWord, tailWord_8354127, baseEnd_8354127] using wordTrace_append hprefix tailTrace_8354127
  have hstable : (prefixWord ++ tailWord_8354127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354127).length < 2 ^ (prefixWord ++ tailWord_8354127).sum := by decide
  have hdescent : baseEnd_8354127 < baseStart_8354127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354151 : List Nat := [1, 1, 5, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_8354151 : Nat := 118140960795 + 8354151 * 2 ^ 59
def prefixEnd_8354151 : Nat := 4983230072969 + 3 ^ 40 * 8354151 * 2
def baseEnd_8354151 : Nat := 4289694923239249079492465

theorem tailTrace_8354151 : CollatzResearch.WordTrace tailWord_8354151 prefixEnd_8354151 4289694923239249079492465 := by
  unfold tailWord_8354151
  simp only [CollatzResearch.WordTrace]
  refine ⟨304700919157345177244518307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203133946104896784829678871 304700919157345177244518307)
  ·
    refine ⟨457051378736017765866777461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304700919157345177244518307 457051378736017765866777461)
    ·
      refine ⟨42848566756501665550010387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 457051378736017765866777461 42848566756501665550010387)
      ·
        refine ⟨64272850134752498325015581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42848566756501665550010387 64272850134752498325015581)
        ·
          refine ⟨24102318800532186871880843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64272850134752498325015581 24102318800532186871880843)
          ·
            refine ⟨36153478200798280307821265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24102318800532186871880843 36153478200798280307821265)
            ·
              refine ⟨27115108650598710230865949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36153478200798280307821265 27115108650598710230865949)
              ·
                refine ⟨10168165743974516336574731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27115108650598710230865949 10168165743974516336574731)
                ·
                  refine ⟨15252248615961774504862097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10168165743974516336574731 15252248615961774504862097)
                  ·
                    refine ⟨11439186461971330878646573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15252248615961774504862097 11439186461971330878646573)
                    ·
                      refine ⟨4289694923239249079492465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11439186461971330878646573 4289694923239249079492465)
                      ·
                        rfl

theorem cell23_8354151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_8354151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354151 prefixEnd_8354151 := by exact prefixLift 8354151
  have htrace : WordTrace (prefixWord ++ tailWord_8354151) baseStart_8354151 baseEnd_8354151 := by
    simpa [prefixWord, tailWord_8354151, baseEnd_8354151] using wordTrace_append hprefix tailTrace_8354151
  have hstable : (prefixWord ++ tailWord_8354151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354151).length < 2 ^ (prefixWord ++ tailWord_8354151).sum := by decide
  have hdescent : baseEnd_8354151 < baseStart_8354151 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354154 : List Nat := [3, 1, 3, 3, 1, 3, 9]
def baseStart_8354154 : Nat := 118140960795 + 8354154 * 2 ^ 59
def prefixEnd_8354154 : Nat := 4983230072969 + 3 ^ 40 * 8354154 * 2
def baseEnd_8354154 : Nat := 52959215601002624293271

theorem tailTrace_8354154 : CollatzResearch.WordTrace tailWord_8354154 prefixEnd_8354154 52959215601002624293271 := by
  unfold tailWord_8354154
  simp only [CollatzResearch.WordTrace]
  refine ⟨76175257144083577189219379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203134019050889539171251677 76175257144083577189219379)
  ·
    refine ⟨114262885716125365783829069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76175257144083577189219379 114262885716125365783829069)
    ·
      refine ⟨42848582143547012168935901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114262885716125365783829069 42848582143547012168935901)
      ·
        refine ⟨16068218303830129563350963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42848582143547012168935901 16068218303830129563350963)
        ·
          refine ⟨24102327455745194345026445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16068218303830129563350963 24102327455745194345026445)
          ·
            refine ⟨9038372795904447879384917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24102327455745194345026445 9038372795904447879384917)
            ·
              refine ⟨52959215601002624293271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9038372795904447879384917 52959215601002624293271)
              ·
                rfl

theorem cell23_8354154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 9].length) (baseStart_8354154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354154 prefixEnd_8354154 := by exact prefixLift 8354154
  have htrace : WordTrace (prefixWord ++ tailWord_8354154) baseStart_8354154 baseEnd_8354154 := by
    simpa [prefixWord, tailWord_8354154, baseEnd_8354154] using wordTrace_append hprefix tailTrace_8354154
  have hstable : (prefixWord ++ tailWord_8354154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354154).length < 2 ^ (prefixWord ++ tailWord_8354154).sum := by decide
  have hdescent : baseEnd_8354154 < baseStart_8354154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354165 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_8354165 : Nat := 118140960795 + 8354165 * 2 ^ 59
def prefixEnd_8354165 : Nat := 4983230072969 + 3 ^ 40 * 8354165 * 2
def baseEnd_8354165 : Nat := 4289702111968412024717401

theorem tailTrace_8354165 : CollatzResearch.WordTrace tailWord_8354165 prefixEnd_8354165 4289702111968412024717401 := by
  unfold tailWord_8354165
  simp only [CollatzResearch.WordTrace]
  refine ⟨304701429779294457635527949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203134286519529638423685299 304701429779294457635527949)
  ·
    refine ⟨114263036167235421613322981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304701429779294457635527949 114263036167235421613322981)
    ·
      refine ⟨21424319281356641552498059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114263036167235421613322981 21424319281356641552498059)
      ·
        refine ⟨32136478922034962328747089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21424319281356641552498059 32136478922034962328747089)
        ·
          refine ⟨24102359191526221746560317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32136478922034962328747089 24102359191526221746560317)
          ·
            refine ⟨9038384696822333154960119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24102359191526221746560317 9038384696822333154960119)
            ·
              refine ⟨13557577045233499732440179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9038384696822333154960119 13557577045233499732440179)
              ·
                refine ⟨20336365567850249598660269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13557577045233499732440179 20336365567850249598660269)
                ·
                  refine ⟨7626137087943843599497601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20336365567850249598660269 7626137087943843599497601)
                  ·
                    refine ⟨5719602815957882699623201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7626137087943843599497601 5719602815957882699623201)
                    ·
                      refine ⟨4289702111968412024717401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5719602815957882699623201 4289702111968412024717401)
                      ·
                        rfl

theorem cell23_8354165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_8354165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354165 prefixEnd_8354165 := by exact prefixLift 8354165
  have htrace : WordTrace (prefixWord ++ tailWord_8354165) baseStart_8354165 baseEnd_8354165 := by
    simpa [prefixWord, tailWord_8354165, baseEnd_8354165] using wordTrace_append hprefix tailTrace_8354165
  have hstable : (prefixWord ++ tailWord_8354165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354165).length < 2 ^ (prefixWord ++ tailWord_8354165).sum := by decide
  have hdescent : baseEnd_8354165 < baseStart_8354165 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354197 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 4, 6]
def baseStart_8354197 : Nat := 118140960795 + 8354197 * 2 ^ 59
def prefixEnd_8354197 : Nat := 4983230072969 + 3 ^ 40 * 8354197 * 2
def baseEnd_8354197 : Nat := 1429906181116451966505751

theorem tailTrace_8354197 : CollatzResearch.WordTrace tailWord_8354197 prefixEnd_8354197 1429906181116451966505751 := by
  unfold tailWord_8354197
  simp only [CollatzResearch.WordTrace]
  refine ⟨304702596915178527100692845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203135064610119018067128563 304702596915178527100692845)
  ·
    refine ⟨114263473843191947662759817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304702596915178527100692845 114263473843191947662759817)
    ·
      refine ⟨85697605382393960747069863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114263473843191947662759817 85697605382393960747069863)
      ·
        refine ⟨128546408073590941120604795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85697605382393960747069863 128546408073590941120604795)
        ·
          refine ⟨192819612110386411680907193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128546408073590941120604795 192819612110386411680907193)
          ·
            refine ⟨144614709082789808760680395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192819612110386411680907193 144614709082789808760680395)
            ·
              refine ⟨216922063624184713141020593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144614709082789808760680395 216922063624184713141020593)
              ·
                refine ⟨162691547718138534855765445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216922063624184713141020593 162691547718138534855765445)
                ·
                  refine ⟨30504665197150975285456021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162691547718138534855765445 30504665197150975285456021)
                  ·
                    refine ⟨1429906181116451966505751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30504665197150975285456021 1429906181116451966505751)
                    ·
                      rfl

theorem cell23_8354197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_8354197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354197 prefixEnd_8354197 := by exact prefixLift 8354197
  have htrace : WordTrace (prefixWord ++ tailWord_8354197) baseStart_8354197 baseEnd_8354197 := by
    simpa [prefixWord, tailWord_8354197, baseEnd_8354197] using wordTrace_append hprefix tailTrace_8354197
  have hstable : (prefixWord ++ tailWord_8354197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354197).length < 2 ^ (prefixWord ++ tailWord_8354197).sum := by decide
  have hdescent : baseEnd_8354197 < baseStart_8354197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354217 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 3, 4, 4]
def baseStart_8354217 : Nat := 118140960795 + 8354217 * 2 ^ 59
def prefixEnd_8354217 : Nat := 4983230072969 + 3 ^ 40 * 8354217 * 2
def baseEnd_8354217 : Nat := 4289728812962445821267161

theorem tailTrace_8354217 : CollatzResearch.WordTrace tailWord_8354217 prefixEnd_8354217 4289728812962445821267161 := by
  unfold tailWord_8354217
  simp only [CollatzResearch.WordTrace]
  refine ⟨304703326375106070516420905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203135550916737380344280603 304703326375106070516420905)
  ·
    refine ⟨228527494781329552887315679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304703326375106070516420905 228527494781329552887315679)
    ·
      refine ⟨342791242171994329330973519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228527494781329552887315679 342791242171994329330973519)
      ·
        refine ⟨514186863257991493996460279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342791242171994329330973519 514186863257991493996460279)
        ·
          refine ⟨771280294886987240994690419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514186863257991493996460279 771280294886987240994690419)
          ·
            refine ⟨1156920442330480861492035629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771280294886987240994690419 1156920442330480861492035629)
            ·
              refine ⟨433845165873930323059513361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1156920442330480861492035629 433845165873930323059513361)
              ·
                refine ⟨325383874405447742294635021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433845165873930323059513361 325383874405447742294635021)
                ·
                  refine ⟨122018952902042903360488133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325383874405447742294635021 122018952902042903360488133)
                  ·
                    refine ⟨22878553669133044380091525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122018952902042903360488133 22878553669133044380091525)
                    ·
                      refine ⟨4289728812962445821267161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22878553669133044380091525 4289728812962445821267161)
                      ·
                        rfl

theorem cell23_8354217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_8354217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354217 prefixEnd_8354217 := by exact prefixLift 8354217
  have htrace : WordTrace (prefixWord ++ tailWord_8354217) baseStart_8354217 baseEnd_8354217 := by
    simpa [prefixWord, tailWord_8354217, baseEnd_8354217] using wordTrace_append hprefix tailTrace_8354217
  have hstable : (prefixWord ++ tailWord_8354217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354217).length < 2 ^ (prefixWord ++ tailWord_8354217).sum := by decide
  have hdescent : baseEnd_8354217 < baseStart_8354217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354254 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_8354254 : Nat := 118140960795 + 8354254 * 2 ^ 59
def prefixEnd_8354254 : Nat := 4983230072969 + 3 ^ 40 * 8354254 * 2
def baseEnd_8354254 : Nat := 4289747811746662176504491

theorem tailTrace_8354254 : CollatzResearch.WordTrace tailWord_8354254 prefixEnd_8354254 4289747811746662176504491 := by
  unfold tailWord_8354254
  simp only [CollatzResearch.WordTrace]
  refine ⟨38088084484496503229439727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203136450583981350557011877 38088084484496503229439727)
  ·
    refine ⟨57132126726744754844159591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38088084484496503229439727 57132126726744754844159591)
    ·
      refine ⟨85698190090117132266239387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57132126726744754844159591 85698190090117132266239387)
      ·
        refine ⟨128547285135175698399359081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85698190090117132266239387 128547285135175698399359081)
        ·
          refine ⟨96410463851381773799519311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128547285135175698399359081 96410463851381773799519311)
          ·
            refine ⟨144615695777072660699278967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96410463851381773799519311 144615695777072660699278967)
            ·
              refine ⟨216923543665608991048918451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144615695777072660699278967 216923543665608991048918451)
              ·
                refine ⟨325385315498413486573377677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216923543665608991048918451 325385315498413486573377677)
                ·
                  refine ⟨122019493311905057465016629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325385315498413486573377677 122019493311905057465016629)
                  ·
                    refine ⟨11439327497991099137345309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122019493311905057465016629 11439327497991099137345309)
                    ·
                      refine ⟨4289747811746662176504491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11439327497991099137345309 4289747811746662176504491)
                      ·
                        rfl

theorem cell23_8354254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_8354254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354254 prefixEnd_8354254 := by exact prefixLift 8354254
  have htrace : WordTrace (prefixWord ++ tailWord_8354254) baseStart_8354254 baseEnd_8354254 := by
    simpa [prefixWord, tailWord_8354254, baseEnd_8354254] using wordTrace_append hprefix tailTrace_8354254
  have hstable : (prefixWord ++ tailWord_8354254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354254).length < 2 ^ (prefixWord ++ tailWord_8354254).sum := by decide
  have hdescent : baseEnd_8354254 < baseStart_8354254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354261 : List Nat := [1, 3, 2, 3, 1, 2, 1, 5, 5]
def baseStart_8354261 : Nat := 118140960795 + 8354261 * 2 ^ 59
def prefixEnd_8354261 : Nat := 4983230072969 + 3 ^ 40 * 8354261 * 2
def baseEnd_8354261 : Nat := 476639045123471516568551

theorem tailTrace_8354261 : CollatzResearch.WordTrace tailWord_8354261 prefixEnd_8354261 476639045123471516568551 := by
  unfold tailWord_8354261
  simp only [CollatzResearch.WordTrace]
  refine ⟨304704931186946666031022637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203136620791297777354015091 304704931186946666031022637)
  ·
    refine ⟨114264349195104999761633489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304704931186946666031022637 114264349195104999761633489)
    ·
      refine ⟨85698261896328749821225117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114264349195104999761633489 85698261896328749821225117)
      ·
        refine ⟨32136848211123281182959419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85698261896328749821225117 32136848211123281182959419)
        ·
          refine ⟨48205272316684921774439129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32136848211123281182959419 48205272316684921774439129)
          ·
            refine ⟨36153954237513691330829347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48205272316684921774439129 36153954237513691330829347)
            ·
              refine ⟨54230931356270536996244021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36153954237513691330829347 54230931356270536996244021)
              ·
                refine ⟨5084149814650362843397877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54230931356270536996244021 5084149814650362843397877)
                ·
                  refine ⟨476639045123471516568551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5084149814650362843397877 476639045123471516568551)
                  ·
                    rfl

theorem cell23_8354261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 5].length) (baseStart_8354261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354261 prefixEnd_8354261 := by exact prefixLift 8354261
  have htrace : WordTrace (prefixWord ++ tailWord_8354261) baseStart_8354261 baseEnd_8354261 := by
    simpa [prefixWord, tailWord_8354261, baseEnd_8354261] using wordTrace_append hprefix tailTrace_8354261
  have hstable : (prefixWord ++ tailWord_8354261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354261).length < 2 ^ (prefixWord ++ tailWord_8354261).sum := by decide
  have hdescent : baseEnd_8354261 < baseStart_8354261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354354 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_8354354 : Nat := 118140960795 + 8354354 * 2 ^ 59
def prefixEnd_8354354 : Nat := 4983230072969 + 3 ^ 40 * 8354354 * 2
def baseEnd_8354354 : Nat := 4289799159812111785254031

theorem tailTrace_8354354 : CollatzResearch.WordTrace tailWord_8354354 prefixEnd_8354354 4289799159812111785254031 := by
  unfold tailWord_8354354
  simp only [CollatzResearch.WordTrace]
  refine ⟨76177080793902435728539529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203138882117073161942772077 76177080793902435728539529)
  ·
    refine ⟨57132810595426826796404647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76177080793902435728539529 57132810595426826796404647)
    ·
      refine ⟨85699215893140240194606971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57132810595426826796404647 85699215893140240194606971)
      ·
        refine ⟨128548823839710360291910457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85699215893140240194606971 128548823839710360291910457)
        ·
          refine ⟨96411617879782770218932843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128548823839710360291910457 96411617879782770218932843)
          ·
            refine ⟨144617426819674155328399265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96411617879782770218932843 144617426819674155328399265)
            ·
              refine ⟨108463070114755616496299449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144617426819674155328399265 108463070114755616496299449)
              ·
                refine ⟨81347302586066712372224587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108463070114755616496299449 81347302586066712372224587)
                ·
                  refine ⟨122020953879100068558336881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81347302586066712372224587 122020953879100068558336881)
                  ·
                    refine ⟨91515715409325051418752661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122020953879100068558336881 91515715409325051418752661)
                    ·
                      refine ⟨4289799159812111785254031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91515715409325051418752661 4289799159812111785254031)
                      ·
                        rfl

theorem cell23_8354354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_8354354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354354 prefixEnd_8354354 := by exact prefixLift 8354354
  have htrace : WordTrace (prefixWord ++ tailWord_8354354) baseStart_8354354 baseEnd_8354354 := by
    simpa [prefixWord, tailWord_8354354, baseEnd_8354354] using wordTrace_append hprefix tailTrace_8354354
  have hstable : (prefixWord ++ tailWord_8354354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354354).length < 2 ^ (prefixWord ++ tailWord_8354354).sum := by decide
  have hdescent : baseEnd_8354354 < baseStart_8354354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354371 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 1, 5, 2]
def baseStart_8354371 : Nat := 118140960795 + 8354371 * 2 ^ 59
def prefixEnd_8354371 : Nat := 4983230072969 + 3 ^ 40 * 8354371 * 2
def baseEnd_8354371 : Nat := 4289807888983238218741453

theorem tailTrace_8354371 : CollatzResearch.WordTrace tailWord_8354371 prefixEnd_8354371 4289807888983238218741453 := by
  unfold tailWord_8354371
  simp only [CollatzResearch.WordTrace]
  refine ⟨304708943216548154817526967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203139295477698769878351311 304708943216548154817526967)
  ·
    refine ⟨457063414824822232226290451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304708943216548154817526967 457063414824822232226290451)
    ·
      refine ⟨685595122237233348339435677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457063414824822232226290451 685595122237233348339435677)
      ·
        refine ⟨257098170838962505627288379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 685595122237233348339435677 257098170838962505627288379)
        ·
          refine ⟨385647256258443758440932569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257098170838962505627288379 385647256258443758440932569)
          ·
            refine ⟨289235442193832818830699427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385647256258443758440932569 289235442193832818830699427)
            ·
              refine ⟨433853163290749228246049141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289235442193832818830699427 433853163290749228246049141)
              ·
                refine ⟨40673734058507740148067107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 433853163290749228246049141 40673734058507740148067107)
                ·
                  refine ⟨61010601087761610222100661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40673734058507740148067107 61010601087761610222100661)
                  ·
                    refine ⟨5719743851977650958321937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61010601087761610222100661 5719743851977650958321937)
                    ·
                      refine ⟨4289807888983238218741453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5719743851977650958321937 4289807888983238218741453)
                      ·
                        rfl

theorem cell23_8354371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 5, 2].length) (baseStart_8354371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354371 prefixEnd_8354371 := by exact prefixLift 8354371
  have htrace : WordTrace (prefixWord ++ tailWord_8354371) baseStart_8354371 baseEnd_8354371 := by
    simpa [prefixWord, tailWord_8354371, baseEnd_8354371] using wordTrace_append hprefix tailTrace_8354371
  have hstable : (prefixWord ++ tailWord_8354371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354371).length < 2 ^ (prefixWord ++ tailWord_8354371).sum := by decide
  have hdescent : baseEnd_8354371 < baseStart_8354371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354401 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_8354401 : Nat := 118140960795 + 8354401 * 2 ^ 59
def prefixEnd_8354401 : Nat := 4983230072969 + 3 ^ 40 * 8354401 * 2
def baseEnd_8354401 : Nat := 4289823293402873101366315

theorem tailTrace_8354401 : CollatzResearch.WordTrace tailWord_8354401 prefixEnd_8354401 4289823293402873101366315 := by
  unfold tailWord_8354401
  simp only [CollatzResearch.WordTrace]
  refine ⟨304710037406439469941119057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203140024937626313294079371 304710037406439469941119057)
  ·
    refine ⟨228532528054829602455839293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304710037406439469941119057 228532528054829602455839293)
    ·
      refine ⟨85699698020561100920939735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228532528054829602455839293 85699698020561100920939735)
      ·
        refine ⟨128549547030841651381409603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85699698020561100920939735 128549547030841651381409603)
        ·
          refine ⟨192824320546262477072114405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128549547030841651381409603 192824320546262477072114405)
          ·
            refine ⟨36154560102424214451021451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192824320546262477072114405 36154560102424214451021451)
            ·
              refine ⟨54231840153636321676532177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36154560102424214451021451 54231840153636321676532177)
              ·
                refine ⟨40673880115227241257399133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54231840153636321676532177 40673880115227241257399133)
                ·
                  refine ⟨15252705043210215471524675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40673880115227241257399133 15252705043210215471524675)
                  ·
                    refine ⟨22879057564815323207287013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15252705043210215471524675 22879057564815323207287013)
                    ·
                      refine ⟨4289823293402873101366315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22879057564815323207287013 4289823293402873101366315)
                      ·
                        rfl

theorem cell23_8354401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_8354401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354401 prefixEnd_8354401 := by exact prefixLift 8354401
  have htrace : WordTrace (prefixWord ++ tailWord_8354401) baseStart_8354401 baseEnd_8354401 := by
    simpa [prefixWord, tailWord_8354401, baseEnd_8354401] using wordTrace_append hprefix tailTrace_8354401
  have hstable : (prefixWord ++ tailWord_8354401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354401).length < 2 ^ (prefixWord ++ tailWord_8354401).sum := by decide
  have hdescent : baseEnd_8354401 < baseStart_8354401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354452 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_8354452 : Nat := 118140960795 + 8354452 * 2 ^ 59
def prefixEnd_8354452 : Nat := 4983230072969 + 3 ^ 40 * 8354452 * 2
def baseEnd_8354452 : Nat := 4289849480916252401828581

theorem tailTrace_8354452 : CollatzResearch.WordTrace tailWord_8354452 prefixEnd_8354452 4289849480916252401828581 := by
  unfold tailWord_8354452
  simp only [CollatzResearch.WordTrace]
  refine ⟨152355948764627352825612805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203141265019503137100817073 152355948764627352825612805)
  ·
    refine ⟨28566740393367628654802401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152355948764627352825612805 28566740393367628654802401)
    ·
      refine ⟨21425055295025721491101801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28566740393367628654802401 21425055295025721491101801)
      ·
        refine ⟨16068791471269291118326351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21425055295025721491101801 16068791471269291118326351)
        ·
          refine ⟨24103187206903936677489527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16068791471269291118326351 24103187206903936677489527)
          ·
            refine ⟨36154780810355905016234291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24103187206903936677489527 36154780810355905016234291)
            ·
              refine ⟨54232171215533857524351437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36154780810355905016234291 54232171215533857524351437)
              ·
                refine ⟨20337064205825196571631789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54232171215533857524351437 20337064205825196571631789)
                ·
                  refine ⟨7626399077184448714361921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20337064205825196571631789 7626399077184448714361921)
                  ·
                    refine ⟨5719799307888336535771441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7626399077184448714361921 5719799307888336535771441)
                    ·
                      refine ⟨4289849480916252401828581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5719799307888336535771441 4289849480916252401828581)
                      ·
                        rfl

theorem cell23_8354452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_8354452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354452 prefixEnd_8354452 := by exact prefixLift 8354452
  have htrace : WordTrace (prefixWord ++ tailWord_8354452) baseStart_8354452 baseEnd_8354452 := by
    simpa [prefixWord, tailWord_8354452, baseEnd_8354452] using wordTrace_append hprefix tailTrace_8354452
  have hstable : (prefixWord ++ tailWord_8354452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354452).length < 2 ^ (prefixWord ++ tailWord_8354452).sum := by decide
  have hdescent : baseEnd_8354452 < baseStart_8354452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354462 : List Nat := [4, 3, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_8354462 : Nat := 118140960795 + 8354462 * 2 ^ 59
def prefixEnd_8354462 : Nat := 4983230072969 + 3 ^ 40 * 8354462 * 2
def baseEnd_8354462 : Nat := 1429951538574265787567845

theorem tailTrace_8354462 : CollatzResearch.WordTrace tailWord_8354462 prefixEnd_8354462 1429951538574265787567845 := by
  unfold tailWord_8354462
  simp only [CollatzResearch.WordTrace]
  refine ⟨38089032782402309669886205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203141508172812318239393093 38089032782402309669886205)
  ·
    refine ⟨14283387293400866126207327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38089032782402309669886205 14283387293400866126207327)
    ·
      refine ⟨21425080940101299189310991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14283387293400866126207327 21425080940101299189310991)
      ·
        refine ⟨32137621410151948783966487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21425080940101299189310991 32137621410151948783966487)
        ·
          refine ⟨48206432115227923175949731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32137621410151948783966487 48206432115227923175949731)
          ·
            refine ⟨72309648172841884763924597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48206432115227923175949731 72309648172841884763924597)
            ·
              refine ⟨6779029516203926696617931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72309648172841884763924597 6779029516203926696617931)
              ·
                refine ⟨10168544274305890044926897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6779029516203926696617931 10168544274305890044926897)
                ·
                  refine ⟨7626408205729417533695173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10168544274305890044926897 7626408205729417533695173)
                  ·
                    refine ⟨1429951538574265787567845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7626408205729417533695173 1429951538574265787567845)
                    ·
                      rfl

theorem cell23_8354462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_8354462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354462 prefixEnd_8354462 := by exact prefixLift 8354462
  have htrace : WordTrace (prefixWord ++ tailWord_8354462) baseStart_8354462 baseEnd_8354462 := by
    simpa [prefixWord, tailWord_8354462, baseEnd_8354462] using wordTrace_append hprefix tailTrace_8354462
  have hstable : (prefixWord ++ tailWord_8354462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354462).length < 2 ^ (prefixWord ++ tailWord_8354462).sum := by decide
  have hdescent : baseEnd_8354462 < baseStart_8354462 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354465 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_8354465 : Nat := 118140960795 + 8354465 * 2 ^ 59
def prefixEnd_8354465 : Nat := 4983230072969 + 3 ^ 40 * 8354465 * 2
def baseEnd_8354465 : Nat := 4289856156164760850966021

theorem tailTrace_8354465 : CollatzResearch.WordTrace tailWord_8354465 prefixEnd_8354465 4289856156164760850966021 := by
  unfold tailWord_8354465
  simp only [CollatzResearch.WordTrace]
  refine ⟨304712371678207608871448849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203141581118805072580965899 304712371678207608871448849)
  ·
    refine ⟨228534278758655706653586637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304712371678207608871448849 228534278758655706653586637)
    ·
      refine ⟨85700354534495889995094989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228534278758655706653586637 85700354534495889995094989)
      ·
        refine ⟨32137632950435958748160621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85700354534495889995094989 32137632950435958748160621)
        ·
          refine ⟨12051612356413484530560233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32137632950435958748160621 12051612356413484530560233)
          ·
            refine ⟨9038709267310113397920175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12051612356413484530560233 9038709267310113397920175)
            ·
              refine ⟨13558063900965170096880263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9038709267310113397920175 13558063900965170096880263)
              ·
                refine ⟨20337095851447755145320395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13558063900965170096880263 20337095851447755145320395)
                ·
                  refine ⟨30505643777171632717980593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20337095851447755145320395 30505643777171632717980593)
                  ·
                    refine ⟨22879232832878724538485445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30505643777171632717980593 22879232832878724538485445)
                    ·
                      refine ⟨4289856156164760850966021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22879232832878724538485445 4289856156164760850966021)
                      ·
                        rfl

theorem cell23_8354465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_8354465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354465 prefixEnd_8354465 := by exact prefixLift 8354465
  have htrace : WordTrace (prefixWord ++ tailWord_8354465) baseStart_8354465 baseEnd_8354465 := by
    simpa [prefixWord, tailWord_8354465, baseEnd_8354465] using wordTrace_append hprefix tailTrace_8354465
  have hstable : (prefixWord ++ tailWord_8354465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354465).length < 2 ^ (prefixWord ++ tailWord_8354465).sum := by decide
  have hdescent : baseEnd_8354465 < baseStart_8354465 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354485 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_8354485 : Nat := 118140960795 + 8354485 * 2 ^ 59
def prefixEnd_8354485 : Nat := 4983230072969 + 3 ^ 40 * 8354485 * 2
def baseEnd_8354485 : Nat := 4289866425777850772715929

theorem tailTrace_8354485 : CollatzResearch.WordTrace tailWord_8354485 prefixEnd_8354485 4289866425777850772715929 := by
  unfold tailWord_8354485
  simp only [CollatzResearch.WordTrace]
  refine ⟨304713101138135152287176909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203142067425423434858117939 304713101138135152287176909)
  ·
    refine ⟨114267412926800682107691341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304713101138135152287176909 114267412926800682107691341)
    ·
      refine ⟨42850279847550255790384253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114267412926800682107691341 42850279847550255790384253)
      ·
        refine ⟨16068854942831345921394095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42850279847550255790384253 16068854942831345921394095)
        ·
          refine ⟨24103282414247018882091143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16068854942831345921394095 24103282414247018882091143)
          ·
            refine ⟨36154923621370528323136715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24103282414247018882091143 36154923621370528323136715)
            ·
              refine ⟨54232385432055792484705073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36154923621370528323136715 54232385432055792484705073)
              ·
                refine ⟨40674289074041844363528805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54232385432055792484705073 40674289074041844363528805)
                ·
                  refine ⟨7626429201382845818161651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40674289074041844363528805 7626429201382845818161651)
                  ·
                    refine ⟨11439643802074268727242477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7626429201382845818161651 11439643802074268727242477)
                    ·
                      refine ⟨4289866425777850772715929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11439643802074268727242477 4289866425777850772715929)
                      ·
                        rfl

theorem cell23_8354485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_8354485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354485 prefixEnd_8354485 := by exact prefixLift 8354485
  have htrace : WordTrace (prefixWord ++ tailWord_8354485) baseStart_8354485 baseEnd_8354485 := by
    simpa [prefixWord, tailWord_8354485, baseEnd_8354485] using wordTrace_append hprefix tailTrace_8354485
  have hstable : (prefixWord ++ tailWord_8354485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354485).length < 2 ^ (prefixWord ++ tailWord_8354485).sum := by decide
  have hdescent : baseEnd_8354485 < baseStart_8354485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354495 : List Nat := [1, 1, 2, 2, 2, 4, 2, 3, 1, 3, 2]
def baseStart_8354495 : Nat := 118140960795 + 8354495 * 2 ^ 59
def prefixEnd_8354495 : Nat := 4983230072969 + 3 ^ 40 * 8354495 * 2
def baseEnd_8354495 : Nat := 4289871560584395733590883

theorem tailTrace_8354495 : CollatzResearch.WordTrace tailWord_8354495 prefixEnd_8354495 4289871560584395733590883 := by
  unfold tailWord_8354495
  simp only [CollatzResearch.WordTrace]
  refine ⟨304713465868098923995040939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203142310578732615996693959 304713465868098923995040939)
  ·
    refine ⟨457070198802148385992561409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304713465868098923995040939 457070198802148385992561409)
    ·
      refine ⟨342802649101611289494421057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457070198802148385992561409 342802649101611289494421057)
      ·
        refine ⟨257101986826208467120815793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342802649101611289494421057 257101986826208467120815793)
        ·
          refine ⟨192826490119656350340611845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257101986826208467120815793 192826490119656350340611845)
          ·
            refine ⟨36154966897435565688864721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192826490119656350340611845 36154966897435565688864721)
            ·
              refine ⟨27116225173076674266648541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36154966897435565688864721 27116225173076674266648541)
              ·
                refine ⟨10168584439903752849993203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27116225173076674266648541 10168584439903752849993203)
                ·
                  refine ⟨15252876659855629274989805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10168584439903752849993203 15252876659855629274989805)
                  ·
                    refine ⟨5719828747445860978121177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15252876659855629274989805 5719828747445860978121177)
                    ·
                      refine ⟨4289871560584395733590883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5719828747445860978121177 4289871560584395733590883)
                      ·
                        rfl

theorem cell23_8354495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 3, 2].length) (baseStart_8354495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354495 prefixEnd_8354495 := by exact prefixLift 8354495
  have htrace : WordTrace (prefixWord ++ tailWord_8354495) baseStart_8354495 baseEnd_8354495 := by
    simpa [prefixWord, tailWord_8354495, baseEnd_8354495] using wordTrace_append hprefix tailTrace_8354495
  have hstable : (prefixWord ++ tailWord_8354495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354495).length < 2 ^ (prefixWord ++ tailWord_8354495).sum := by decide
  have hdescent : baseEnd_8354495 < baseStart_8354495 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354521 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 1, 4, 4]
def baseStart_8354521 : Nat := 118140960795 + 8354521 * 2 ^ 59
def prefixEnd_8354521 : Nat := 4983230072969 + 3 ^ 40 * 8354521 * 2
def baseEnd_8354521 : Nat := 4289884911081412631865763

theorem tailTrace_8354521 : CollatzResearch.WordTrace tailWord_8354521 prefixEnd_8354521 4289884911081412631865763 := by
  unfold tailWord_8354521
  simp only [CollatzResearch.WordTrace]
  refine ⟨304714414166004730435487417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203142942777336486956991611 304714414166004730435487417)
  ·
    refine ⟨228535810624503547826615563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304714414166004730435487417 228535810624503547826615563)
    ·
      refine ⟨342803715936755321739923345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228535810624503547826615563 342803715936755321739923345)
      ·
        refine ⟨257102786952566491304942509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342803715936755321739923345 257102786952566491304942509)
        ·
          refine ⟨96413545107212434239353441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257102786952566491304942509 96413545107212434239353441)
          ·
            refine ⟨72310158830409325679515081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96413545107212434239353441 72310158830409325679515081)
            ·
              refine ⟨54232619122806994259636311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72310158830409325679515081 54232619122806994259636311)
              ·
                refine ⟨81348928684210491389454467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54232619122806994259636311 81348928684210491389454467)
                ·
                  refine ⟨122023393026315737084181701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81348928684210491389454467 122023393026315737084181701)
                  ·
                    refine ⟨22879386192434200703284069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122023393026315737084181701 22879386192434200703284069)
                    ·
                      refine ⟨4289884911081412631865763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22879386192434200703284069 4289884911081412631865763)
                      ·
                        rfl

theorem cell23_8354521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_8354521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354521 prefixEnd_8354521 := by exact prefixLift 8354521
  have htrace : WordTrace (prefixWord ++ tailWord_8354521) baseStart_8354521 baseEnd_8354521 := by
    simpa [prefixWord, tailWord_8354521, baseEnd_8354521] using wordTrace_append hprefix tailTrace_8354521
  have hstable : (prefixWord ++ tailWord_8354521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354521).length < 2 ^ (prefixWord ++ tailWord_8354521).sum := by decide
  have hdescent : baseEnd_8354521 < baseStart_8354521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354561 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 3, 7]
def baseStart_8354561 : Nat := 118140960795 + 8354561 * 2 ^ 59
def prefixEnd_8354561 : Nat := 4983230072969 + 3 ^ 40 * 8354561 * 2
def baseEnd_8354561 : Nat := 1429968483435864158455193

theorem tailTrace_8354561 : CollatzResearch.WordTrace tailWord_8354561 prefixEnd_8354561 1429968483435864158455193 := by
  unfold tailWord_8354561
  simp only [CollatzResearch.WordTrace]
  refine ⟨304715873085859817266943537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203143915390573211511295691 304715873085859817266943537)
  ·
    refine ⟨228536904814394862950207653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304715873085859817266943537 228536904814394862950207653)
    ·
      refine ⟨42850669652699036803163935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228536904814394862950207653 42850669652699036803163935)
      ·
        refine ⟨64276004479048555204745903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42850669652699036803163935 64276004479048555204745903)
        ·
          refine ⟨96414006718572832807118855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64276004479048555204745903 96414006718572832807118855)
          ·
            refine ⟨144621010077859249210678283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96414006718572832807118855 144621010077859249210678283)
            ·
              refine ⟨216931515116788873816017425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144621010077859249210678283 216931515116788873816017425)
              ·
                refine ⟨162698636337591655362013069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216931515116788873816017425 162698636337591655362013069)
                ·
                  refine ⟨61011988626596870760754901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162698636337591655362013069 61011988626596870760754901)
                  ·
                    refine ⟨1429968483435864158455193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61011988626596870760754901 1429968483435864158455193)
                    ·
                      rfl

theorem cell23_8354561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_8354561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354561 prefixEnd_8354561 := by exact prefixLift 8354561
  have htrace : WordTrace (prefixWord ++ tailWord_8354561) baseStart_8354561 baseEnd_8354561 := by
    simpa [prefixWord, tailWord_8354561, baseEnd_8354561] using wordTrace_append hprefix tailTrace_8354561
  have hstable : (prefixWord ++ tailWord_8354561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354561).length < 2 ^ (prefixWord ++ tailWord_8354561).sum := by decide
  have hdescent : baseEnd_8354561 < baseStart_8354561 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354638 : List Nat := [4, 1, 1, 1, 1, 1, 1, 7, 6]
def baseStart_8354638 : Nat := 118140960795 + 8354638 * 2 ^ 59
def prefixEnd_8354638 : Nat := 4983230072969 + 3 ^ 40 * 8354638 * 2
def baseEnd_8354638 : Nat := 476660554257554297122525

theorem tailTrace_8354638 : CollatzResearch.WordTrace tailWord_8354638 prefixEnd_8354638 476660554257554297122525 := by
  unfold tailWord_8354638
  simp only [CollatzResearch.WordTrace]
  refine ⟨38089835188322607427187071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203145787671053906278331045 38089835188322607427187071)
  ·
    refine ⟨57134752782483911140780607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38089835188322607427187071 57134752782483911140780607)
    ·
      refine ⟨85702129173725866711170911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57134752782483911140780607 85702129173725866711170911)
      ·
        refine ⟨128553193760588800066756367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85702129173725866711170911 128553193760588800066756367)
        ·
          refine ⟨192829790640883200100134551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128553193760588800066756367 192829790640883200100134551)
          ·
            refine ⟨289244685961324800150201827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192829790640883200100134551 289244685961324800150201827)
            ·
              refine ⟨433867028941987200225302741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289244685961324800150201827 433867028941987200225302741)
              ·
                refine ⟨10168758490827825005280533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 433867028941987200225302741 10168758490827825005280533)
                ·
                  refine ⟨476660554257554297122525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10168758490827825005280533 476660554257554297122525)
                  ·
                    rfl

theorem cell23_8354638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_8354638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354638 prefixEnd_8354638 := by exact prefixLift 8354638
  have htrace : WordTrace (prefixWord ++ tailWord_8354638) baseStart_8354638 baseEnd_8354638 := by
    simpa [prefixWord, tailWord_8354638, baseEnd_8354638] using wordTrace_append hprefix tailTrace_8354638
  have hstable : (prefixWord ++ tailWord_8354638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354638).length < 2 ^ (prefixWord ++ tailWord_8354638).sum := by decide
  have hdescent : baseEnd_8354638 < baseStart_8354638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354659 : List Nat := [1, 1, 1, 5, 3, 3, 1, 3, 1, 4]
def baseStart_8354659 : Nat := 118140960795 + 8354659 * 2 ^ 59
def prefixEnd_8354659 : Nat := 4983230072969 + 3 ^ 40 * 8354659 * 2
def baseEnd_8354659 : Nat := 1429985257137244363980043

theorem tailTrace_8354659 : CollatzResearch.WordTrace tailWord_8354659 prefixEnd_8354659 1429985257137244363980043 := by
  unfold tailWord_8354659
  simp only [CollatzResearch.WordTrace]
  refine ⟨304719447439504780004011031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203146298293003186669340687 304719447439504780004011031)
  ·
    refine ⟨457079171159257170006016547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304719447439504780004011031 457079171159257170006016547)
    ·
      refine ⟨685618756738885755009024821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457079171159257170006016547 685618756738885755009024821)
      ·
        refine ⟨64276758444270539532096077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 685618756738885755009024821 64276758444270539532096077)
        ·
          refine ⟨24103784416601452324536029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64276758444270539532096077 24103784416601452324536029)
          ·
            refine ⟨9038919156225544621701011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24103784416601452324536029 9038919156225544621701011)
            ·
              refine ⟨13558378734338316932551517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9038919156225544621701011 13558378734338316932551517)
              ·
                refine ⟨5084392025376868849706819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13558378734338316932551517 5084392025376868849706819)
                ·
                  refine ⟨7626588038065303274560229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5084392025376868849706819 7626588038065303274560229)
                  ·
                    refine ⟨1429985257137244363980043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7626588038065303274560229 1429985257137244363980043)
                    ·
                      rfl

theorem cell23_8354659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 1, 4].length) (baseStart_8354659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354659 prefixEnd_8354659 := by exact prefixLift 8354659
  have htrace : WordTrace (prefixWord ++ tailWord_8354659) baseStart_8354659 baseEnd_8354659 := by
    simpa [prefixWord, tailWord_8354659, baseEnd_8354659] using wordTrace_append hprefix tailTrace_8354659
  have hstable : (prefixWord ++ tailWord_8354659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354659).length < 2 ^ (prefixWord ++ tailWord_8354659).sum := by decide
  have hdescent : baseEnd_8354659 < baseStart_8354659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354675 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 4, 3, 2]
def baseStart_8354675 : Nat := 118140960795 + 8354675 * 2 ^ 59
def prefixEnd_8354675 : Nat := 4983230072969 + 3 ^ 40 * 8354675 * 2
def baseEnd_8354675 : Nat := 4289963987102205029340055

theorem tailTrace_8354675 : CollatzResearch.WordTrace tailWord_8354675 prefixEnd_8354675 4289963987102205029340055 := by
  unfold tailWord_8354675
  simp only [CollatzResearch.WordTrace]
  refine ⟨304720031007446814736593479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203146687338297876491062319 304720031007446814736593479)
  ·
    refine ⟨457080046511170222104890219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304720031007446814736593479 457080046511170222104890219)
    ·
      refine ⟨685620069766755333157335329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457080046511170222104890219 685620069766755333157335329)
      ·
        refine ⟨514215052325066499868001497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685620069766755333157335329 514215052325066499868001497)
        ·
          refine ⟨385661289243799874901001123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514215052325066499868001497 385661289243799874901001123)
          ·
            refine ⟨578491933865699812351501685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385661289243799874901001123 578491933865699812351501685)
            ·
              refine ⟨54233618799909357407953283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 578491933865699812351501685 54233618799909357407953283)
              ·
                refine ⟨81350428199864036111929925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54233618799909357407953283 81350428199864036111929925)
                ·
                  refine ⟨15253205287474506770986861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81350428199864036111929925 15253205287474506770986861)
                  ·
                    refine ⟨5719951982802940039120073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15253205287474506770986861 5719951982802940039120073)
                    ·
                      refine ⟨4289963987102205029340055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5719951982802940039120073 4289963987102205029340055)
                      ·
                        rfl

theorem cell23_8354675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 3, 2].length) (baseStart_8354675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354675 prefixEnd_8354675 := by exact prefixLift 8354675
  have htrace : WordTrace (prefixWord ++ tailWord_8354675) baseStart_8354675 baseEnd_8354675 := by
    simpa [prefixWord, tailWord_8354675, baseEnd_8354675] using wordTrace_append hprefix tailTrace_8354675
  have hstable : (prefixWord ++ tailWord_8354675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354675).length < 2 ^ (prefixWord ++ tailWord_8354675).sum := by decide
  have hdescent : baseEnd_8354675 < baseStart_8354675 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354728 : List Nat := [2, 1, 6, 14]
def baseStart_8354728 : Nat := 118140960795 + 8354728 * 2 ^ 59
def prefixEnd_8354728 : Nat := 4983230072969 + 3 ^ 40 * 8354728 * 2
def baseEnd_8354728 : Nat := 1961587197794647152253

theorem tailTrace_8354728 : CollatzResearch.WordTrace tailWord_8354728 prefixEnd_8354728 1961587197794647152253 := by
  unfold tailWord_8354728
  simp only [CollatzResearch.WordTrace]
  refine ⟨152360982038127402394136419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203147976050836536525515225 152360982038127402394136419)
  ·
    refine ⟨228541473057191103591204629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152360982038127402394136419 228541473057191103591204629)
    ·
      refine ⟨10712881549555832980837717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228541473057191103591204629 10712881549555832980837717)
      ·
        refine ⟨1961587197794647152253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 10712881549555832980837717 1961587197794647152253)
        ·
          rfl

theorem cell23_8354728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 14].length) (baseStart_8354728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354728 prefixEnd_8354728 := by exact prefixLift 8354728
  have htrace : WordTrace (prefixWord ++ tailWord_8354728) baseStart_8354728 baseEnd_8354728 := by
    simpa [prefixWord, tailWord_8354728, baseEnd_8354728] using wordTrace_append hprefix tailTrace_8354728
  have hstable : (prefixWord ++ tailWord_8354728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354728).length < 2 ^ (prefixWord ++ tailWord_8354728).sum := by decide
  have hdescent : baseEnd_8354728 < baseStart_8354728 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354733 : List Nat := [1, 5, 2, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_8354733 : Nat := 118140960795 + 8354733 * 2 ^ 59
def prefixEnd_8354733 : Nat := 4983230072969 + 3 ^ 40 * 8354733 * 2
def baseEnd_8354733 : Nat := 4289993768980165802414789

theorem tailTrace_8354733 : CollatzResearch.WordTrace tailWord_8354733 prefixEnd_8354733 4289993768980165802414789 := by
  unfold tailWord_8354733
  simp only [CollatzResearch.WordTrace]
  refine ⟨304722146441236690642204853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203148097627491127094803235 304722146441236690642204853)
  ·
    refine ⟨28567701228865939747706705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304722146441236690642204853 28567701228865939747706705)
    ·
      refine ⟨21425775921649454810780029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28567701228865939747706705 21425775921649454810780029)
      ·
        refine ⟨8034665970618545554042511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21425775921649454810780029 8034665970618545554042511)
        ·
          refine ⟨12051998955927818331063767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8034665970618545554042511 12051998955927818331063767)
          ·
            refine ⟨18077998433891727496595651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12051998955927818331063767 18077998433891727496595651)
            ·
              refine ⟨27116997650837591244893477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18077998433891727496595651 27116997650837591244893477)
              ·
                refine ⟨5084437059532048358417527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27116997650837591244893477 5084437059532048358417527)
                ·
                  refine ⟨7626655589298072537626291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5084437059532048358417527 7626655589298072537626291)
                  ·
                    refine ⟨11439983383947108806439437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7626655589298072537626291 11439983383947108806439437)
                    ·
                      refine ⟨4289993768980165802414789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11439983383947108806439437 4289993768980165802414789)
                      ·
                        rfl

theorem cell23_8354733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_8354733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354733 prefixEnd_8354733 := by exact prefixLift 8354733
  have htrace : WordTrace (prefixWord ++ tailWord_8354733) baseStart_8354733 baseEnd_8354733 := by
    simpa [prefixWord, tailWord_8354733, baseEnd_8354733] using wordTrace_append hprefix tailTrace_8354733
  have hstable : (prefixWord ++ tailWord_8354733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354733).length < 2 ^ (prefixWord ++ tailWord_8354733).sum := by decide
  have hdescent : baseEnd_8354733 < baseStart_8354733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354745 : List Nat := [1, 2, 1, 4, 2, 4, 1, 8]
def baseStart_8354745 : Nat := 118140960795 + 8354745 * 2 ^ 59
def prefixEnd_8354745 : Nat := 4983230072969 + 3 ^ 40 * 8354745 * 2
def baseEnd_8354745 : Nat := 158888886324000731683879

theorem tailTrace_8354745 : CollatzResearch.WordTrace tailWord_8354745 prefixEnd_8354745 158888886324000731683879 := by
  unfold tailWord_8354745
  simp only [CollatzResearch.WordTrace]
  refine ⟨304722584117193216691641689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203148389411462144461094459 304722584117193216691641689)
  ·
    refine ⟨228541938087894912518731267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304722584117193216691641689 228541938087894912518731267)
    ·
      refine ⟨342812907131842368778096901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228541938087894912518731267 342812907131842368778096901)
      ·
        refine ⟨64277420087220444145893169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342812907131842368778096901 64277420087220444145893169)
        ·
          refine ⟨48208065065415333109419877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64277420087220444145893169 48208065065415333109419877)
          ·
            refine ⟨9039012199765374958016227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48208065065415333109419877 9039012199765374958016227)
            ·
              refine ⟨13558518299648062437024341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9039012199765374958016227 13558518299648062437024341)
              ·
                refine ⟨158888886324000731683879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13558518299648062437024341 158888886324000731683879)
                ·
                  rfl

theorem cell23_8354745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 8].length) (baseStart_8354745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354745 prefixEnd_8354745 := by exact prefixLift 8354745
  have htrace : WordTrace (prefixWord ++ tailWord_8354745) baseStart_8354745 baseEnd_8354745 := by
    simpa [prefixWord, tailWord_8354745, baseEnd_8354745] using wordTrace_append hprefix tailTrace_8354745
  have hstable : (prefixWord ++ tailWord_8354745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354745).length < 2 ^ (prefixWord ++ tailWord_8354745).sum := by decide
  have hdescent : baseEnd_8354745 < baseStart_8354745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354768 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 5]
def baseStart_8354768 : Nat := 118140960795 + 8354768 * 2 ^ 59
def prefixEnd_8354768 : Nat := 4983230072969 + 3 ^ 40 * 8354768 * 2
def baseEnd_8354768 : Nat := 4290011740803073165477127

theorem tailTrace_8354768 : CollatzResearch.WordTrace tailWord_8354768 prefixEnd_8354768 4290011740803073165477127 := by
  unfold tailWord_8354768
  simp only [CollatzResearch.WordTrace]
  refine ⟨152361711498054945809864479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203148948664073261079819305 152361711498054945809864479)
  ·
    refine ⟨228542567247082418714796719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152361711498054945809864479 228542567247082418714796719)
    ·
      refine ⟨342813850870623628072195079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228542567247082418714796719 342813850870623628072195079)
      ·
        refine ⟨514220776305935442108292619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342813850870623628072195079 514220776305935442108292619)
        ·
          refine ⟨771331164458903163162438929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514220776305935442108292619 771331164458903163162438929)
          ·
            refine ⟨578498373344177372371829197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 771331164458903163162438929 578498373344177372371829197)
            ·
              refine ⟨216936890004066514639435949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 578498373344177372371829197 216936890004066514639435949)
              ·
                refine ⟨81351333751524942989788481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216936890004066514639435949 81351333751524942989788481)
                ·
                  refine ⟨61013500313643707242341361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81351333751524942989788481 61013500313643707242341361)
                  ·
                    refine ⟨45760125235232780431756021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61013500313643707242341361 45760125235232780431756021)
                    ·
                      refine ⟨4290011740803073165477127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45760125235232780431756021 4290011740803073165477127)
                      ·
                        rfl

theorem cell23_8354768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_8354768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354768 prefixEnd_8354768 := by exact prefixLift 8354768
  have htrace : WordTrace (prefixWord ++ tailWord_8354768) baseStart_8354768 baseEnd_8354768 := by
    simpa [prefixWord, tailWord_8354768, baseEnd_8354768] using wordTrace_append hprefix tailTrace_8354768
  have hstable : (prefixWord ++ tailWord_8354768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354768).length < 2 ^ (prefixWord ++ tailWord_8354768).sum := by decide
  have hdescent : baseEnd_8354768 < baseStart_8354768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354772 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_8354772 : Nat := 118140960795 + 8354772 * 2 ^ 59
def prefixEnd_8354772 : Nat := 4983230072969 + 3 ^ 40 * 8354772 * 2
def baseEnd_8354772 : Nat := 4290013794725691149827109

theorem tailTrace_8354772 : CollatzResearch.WordTrace tailWord_8354772 prefixEnd_8354772 4290013794725691149827109 := by
  unfold tailWord_8354772
  simp only [CollatzResearch.WordTrace]
  refine ⟨152361784444047700151437285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203149045925396933535249713 152361784444047700151437285)
  ·
    refine ⟨28567834583258943778394491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152361784444047700151437285 28567834583258943778394491)
    ·
      refine ⟨42851751874888415667591737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28567834583258943778394491 42851751874888415667591737)
      ·
        refine ⟨32138813906166311750693803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42851751874888415667591737 32138813906166311750693803)
        ·
          refine ⟨48208220859249467626040705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32138813906166311750693803 48208220859249467626040705)
          ·
            refine ⟨36156165644437100719530529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48208220859249467626040705 36156165644437100719530529)
            ·
              refine ⟨27117124233327825539647897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36156165644437100719530529 27117124233327825539647897)
              ·
                refine ⟨20337843174995869154735923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27117124233327825539647897 20337843174995869154735923)
                ·
                  refine ⟨30506764762493803732103885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20337843174995869154735923 30506764762493803732103885)
                  ·
                    refine ⟨11440036785935176399538957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30506764762493803732103885 11440036785935176399538957)
                    ·
                      refine ⟨4290013794725691149827109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11440036785935176399538957 4290013794725691149827109)
                      ·
                        rfl

theorem cell23_8354772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_8354772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354772 prefixEnd_8354772 := by exact prefixLift 8354772
  have htrace : WordTrace (prefixWord ++ tailWord_8354772) baseStart_8354772 baseEnd_8354772 := by
    simpa [prefixWord, tailWord_8354772, baseEnd_8354772] using wordTrace_append hprefix tailTrace_8354772
  have hstable : (prefixWord ++ tailWord_8354772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354772).length < 2 ^ (prefixWord ++ tailWord_8354772).sum := by decide
  have hdescent : baseEnd_8354772 < baseStart_8354772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354773 : List Nat := [1, 3, 2, 3, 3, 1, 2, 3, 1, 2, 2]
def baseStart_8354773 : Nat := 118140960795 + 8354773 * 2 ^ 59
def prefixEnd_8354773 : Nat := 4983230072969 + 3 ^ 40 * 8354773 * 2
def baseEnd_8354773 : Nat := 4290014308206345645914605

theorem tailTrace_8354773 : CollatzResearch.WordTrace tailWord_8354773 prefixEnd_8354773 4290014308206345645914605 := by
  unfold tailWord_8354773
  simp only [CollatzResearch.WordTrace]
  refine ⟨304723605361091777473660973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203149070240727851649107315 304723605361091777473660973)
  ·
    refine ⟨114271352010409416552622865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304723605361091777473660973 114271352010409416552622865)
    ·
      refine ⟨85703514007807062414467149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114271352010409416552622865 85703514007807062414467149)
      ·
        refine ⟨32138817752927648405425181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85703514007807062414467149 32138817752927648405425181)
        ·
          refine ⟨12052056657347868152034443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32138817752927648405425181 12052056657347868152034443)
          ·
            refine ⟨18078084986021802228051665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12052056657347868152034443 18078084986021802228051665)
            ·
              refine ⟨13558563739516351671038749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18078084986021802228051665 13558563739516351671038749)
              ·
                refine ⟨5084461402318631876639531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13558563739516351671038749 5084461402318631876639531)
                ·
                  refine ⟨7626692103477947814959297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5084461402318631876639531 7626692103477947814959297)
                  ·
                    refine ⟨5720019077608460861219473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7626692103477947814959297 5720019077608460861219473)
                    ·
                      refine ⟨4290014308206345645914605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5720019077608460861219473 4290014308206345645914605)
                      ·
                        rfl

theorem cell23_8354773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_8354773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354773 prefixEnd_8354773 := by exact prefixLift 8354773
  have htrace : WordTrace (prefixWord ++ tailWord_8354773) baseStart_8354773 baseEnd_8354773 := by
    simpa [prefixWord, tailWord_8354773, baseEnd_8354773] using wordTrace_append hprefix tailTrace_8354773
  have hstable : (prefixWord ++ tailWord_8354773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354773).length < 2 ^ (prefixWord ++ tailWord_8354773).sum := by decide
  have hdescent : baseEnd_8354773 < baseStart_8354773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354795 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 2, 8, 2]
def baseStart_8354795 : Nat := 118140960795 + 8354795 * 2 ^ 59
def prefixEnd_8354795 : Nat := 4983230072969 + 3 ^ 40 * 8354795 * 2
def baseEnd_8354795 : Nat := 4290025604780744559839503

theorem tailTrace_8354795 : CollatzResearch.WordTrace tailWord_8354795 prefixEnd_8354795 4290025604780744559839503 := by
  unfold tailWord_8354795
  simp only [CollatzResearch.WordTrace]
  refine ⟨304724407767012075230961839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203149605178008050153974559 304724407767012075230961839)
  ·
    refine ⟨457086611650518112846442759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304724407767012075230961839 457086611650518112846442759)
    ·
      refine ⟨685629917475777169269664139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457086611650518112846442759 685629917475777169269664139)
      ·
        refine ⟨1028444876213665753904496209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685629917475777169269664139 1028444876213665753904496209)
        ·
          refine ⟨771333657160249315428372157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1028444876213665753904496209 771333657160249315428372157)
          ·
            refine ⟨289250121435093493285639559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 771333657160249315428372157 289250121435093493285639559)
            ·
              refine ⟨433875182152640239928459339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289250121435093493285639559 433875182152640239928459339)
              ·
                refine ⟨650812773228960359892689009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433875182152640239928459339 650812773228960359892689009)
                ·
                  refine ⟨488109579921720269919516757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 650812773228960359892689009 488109579921720269919516757)
                  ·
                    refine ⟨5720034139707659413119337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 488109579921720269919516757 5720034139707659413119337)
                    ·
                      refine ⟨4290025604780744559839503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5720034139707659413119337 4290025604780744559839503)
                      ·
                        rfl

theorem cell23_8354795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 8, 2].length) (baseStart_8354795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354795 prefixEnd_8354795 := by exact prefixLift 8354795
  have htrace : WordTrace (prefixWord ++ tailWord_8354795) baseStart_8354795 baseEnd_8354795 := by
    simpa [prefixWord, tailWord_8354795, baseEnd_8354795] using wordTrace_append hprefix tailTrace_8354795
  have hstable : (prefixWord ++ tailWord_8354795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354795).length < 2 ^ (prefixWord ++ tailWord_8354795).sum := by decide
  have hdescent : baseEnd_8354795 < baseStart_8354795 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354852 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 7]
def baseStart_8354852 : Nat := 118140960795 + 8354852 * 2 ^ 59
def prefixEnd_8354852 : Nat := 4983230072969 + 3 ^ 40 * 8354852 * 2
def baseEnd_8354852 : Nat := 476672763686450092980749

theorem tailTrace_8354852 : CollatzResearch.WordTrace tailWord_8354852 prefixEnd_8354852 476672763686450092980749 := by
  unfold tailWord_8354852
  simp only [CollatzResearch.WordTrace]
  refine ⟨152363243363902786982893405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203150991151870382643857873 152363243363902786982893405)
  ·
    refine ⟨57136216261463545118585027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152363243363902786982893405 57136216261463545118585027)
    ·
      refine ⟨85704324392195317677877541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57136216261463545118585027 85704324392195317677877541)
      ·
        refine ⟨16069560823536622064602039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85704324392195317677877541 16069560823536622064602039)
        ·
          refine ⟨24104341235304933096903059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16069560823536622064602039 24104341235304933096903059)
          ·
            refine ⟨36156511852957399645354589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24104341235304933096903059 36156511852957399645354589)
            ·
              refine ⟨13558691944859024867007971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36156511852957399645354589 13558691944859024867007971)
              ·
                refine ⟨20338037917288537300511957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13558691944859024867007971 20338037917288537300511957)
                ·
                  refine ⟨476672763686450092980749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20338037917288537300511957 476672763686450092980749)
                  ·
                    rfl

theorem cell23_8354852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_8354852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354852 prefixEnd_8354852 := by exact prefixLift 8354852
  have htrace : WordTrace (prefixWord ++ tailWord_8354852) baseStart_8354852 baseEnd_8354852 := by
    simpa [prefixWord, tailWord_8354852, baseEnd_8354852] using wordTrace_append hprefix tailTrace_8354852
  have hstable : (prefixWord ++ tailWord_8354852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354852).length < 2 ^ (prefixWord ++ tailWord_8354852).sum := by decide
  have hdescent : baseEnd_8354852 < baseStart_8354852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354862 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_8354862 : Nat := 118140960795 + 8354862 * 2 ^ 59
def prefixEnd_8354862 : Nat := 4983230072969 + 3 ^ 40 * 8354862 * 2
def baseEnd_8354862 : Nat := 4290060007984595797701695

theorem tailTrace_8354862 : CollatzResearch.WordTrace tailWord_8354862 prefixEnd_8354862 4290060007984595797701695 := by
  unfold tailWord_8354862
  simp only [CollatzResearch.WordTrace]
  refine ⟨38090856432221168209206355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203151234305179563782433893 38090856432221168209206355)
  ·
    refine ⟨57136284648331752313809533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38090856432221168209206355 57136284648331752313809533)
    ·
      refine ⟨21426106743124407117678575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57136284648331752313809533 21426106743124407117678575)
      ·
        refine ⟨32139160114686610676517863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21426106743124407117678575 32139160114686610676517863)
        ·
          refine ⟨48208740172029916014776795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32139160114686610676517863 48208740172029916014776795)
          ·
            refine ⟨72313110258044874022165193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48208740172029916014776795 72313110258044874022165193)
            ·
              refine ⟨54234832693533655516623895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72313110258044874022165193 54234832693533655516623895)
              ·
                refine ⟨81352249040300483274935843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54234832693533655516623895 81352249040300483274935843)
                ·
                  refine ⟨122028373560450724912403765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81352249040300483274935843 122028373560450724912403765)
                  ·
                    refine ⟨11440160021292255460537853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122028373560450724912403765 11440160021292255460537853)
                    ·
                      refine ⟨4290060007984595797701695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11440160021292255460537853 4290060007984595797701695)
                      ·
                        rfl

theorem cell23_8354862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_8354862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354862 prefixEnd_8354862 := by exact prefixLift 8354862
  have htrace : WordTrace (prefixWord ++ tailWord_8354862) baseStart_8354862 baseEnd_8354862 := by
    simpa [prefixWord, tailWord_8354862, baseEnd_8354862] using wordTrace_append hprefix tailTrace_8354862
  have hstable : (prefixWord ++ tailWord_8354862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354862).length < 2 ^ (prefixWord ++ tailWord_8354862).sum := by decide
  have hdescent : baseEnd_8354862 < baseStart_8354862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354865 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 4, 5]
def baseStart_8354865 : Nat := 118140960795 + 8354865 * 2 ^ 59
def prefixEnd_8354865 : Nat := 4983230072969 + 3 ^ 40 * 8354865 * 2
def baseEnd_8354865 : Nat := 1430020516142186428654727

theorem tailTrace_8354865 : CollatzResearch.WordTrace tailWord_8354865 prefixEnd_8354865 1430020516142186428654727 := by
  unfold tailWord_8354865
  simp only [CollatzResearch.WordTrace]
  refine ⟨304726960876758477186010049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203151307251172318124006699 304726960876758477186010049)
  ·
    refine ⟨228545220657568857889507537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304726960876758477186010049 228545220657568857889507537)
    ·
      refine ⟨171408915493176643417130653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228545220657568857889507537 171408915493176643417130653)
      ·
        refine ⟨64278343309941241281423995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171408915493176643417130653 64278343309941241281423995)
        ·
          refine ⟨96417514964911861922135993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64278343309941241281423995 96417514964911861922135993)
          ·
            refine ⟨72313136223683896441601995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96417514964911861922135993 72313136223683896441601995)
            ·
              refine ⟨108469704335525844662402993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72313136223683896441601995 108469704335525844662402993)
              ·
                refine ⟨81352278251644383496802245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108469704335525844662402993 81352278251644383496802245)
                ·
                  refine ⟨15253552172183321905650421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81352278251644383496802245 15253552172183321905650421)
                  ·
                    refine ⟨1430020516142186428654727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15253552172183321905650421 1430020516142186428654727)
                    ·
                      rfl

theorem cell23_8354865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_8354865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354865 prefixEnd_8354865 := by exact prefixLift 8354865
  have htrace : WordTrace (prefixWord ++ tailWord_8354865) baseStart_8354865 baseEnd_8354865 := by
    simpa [prefixWord, tailWord_8354865, baseEnd_8354865] using wordTrace_append hprefix tailTrace_8354865
  have hstable : (prefixWord ++ tailWord_8354865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354865).length < 2 ^ (prefixWord ++ tailWord_8354865).sum := by decide
  have hdescent : baseEnd_8354865 < baseStart_8354865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354885 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_8354885 : Nat := 118140960795 + 8354885 * 2 ^ 59
def prefixEnd_8354885 : Nat := 4983230072969 + 3 ^ 40 * 8354885 * 2
def baseEnd_8354885 : Nat := 4290071818039649207714089

theorem tailTrace_8354885 : CollatzResearch.WordTrace tailWord_8354885 prefixEnd_8354885 4290071818039649207714089 := by
  unfold tailWord_8354885
  simp only [CollatzResearch.WordTrace]
  refine ⟨304727690336686020601738109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203151793557790680401158739 304727690336686020601738109)
  ·
    refine ⟨114272883876257257725651791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304727690336686020601738109 114272883876257257725651791)
    ·
      refine ⟨171409325814385886588477687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114272883876257257725651791 171409325814385886588477687)
      ·
        refine ⟨257113988721578829882716531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171409325814385886588477687 257113988721578829882716531)
        ·
          refine ⟨385670983082368244824074797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257113988721578829882716531 385670983082368244824074797)
          ·
            refine ⟨144626618655888091809028049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385670983082368244824074797 144626618655888091809028049)
            ·
              refine ⟨108469963991916068856771037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144626618655888091809028049 108469963991916068856771037)
              ·
                refine ⟨40676236496968525821289139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108469963991916068856771037 40676236496968525821289139)
                ·
                  refine ⟨61014354745452788731933709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40676236496968525821289139 61014354745452788731933709)
                  ·
                    refine ⟨22880383029544795774475141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61014354745452788731933709 22880383029544795774475141)
                    ·
                      refine ⟨4290071818039649207714089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22880383029544795774475141 4290071818039649207714089)
                      ·
                        rfl

theorem cell23_8354885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_8354885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354885 prefixEnd_8354885 := by exact prefixLift 8354885
  have htrace : WordTrace (prefixWord ++ tailWord_8354885) baseStart_8354885 baseEnd_8354885 := by
    simpa [prefixWord, tailWord_8354885, baseEnd_8354885] using wordTrace_append hprefix tailTrace_8354885
  have hstable : (prefixWord ++ tailWord_8354885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354885).length < 2 ^ (prefixWord ++ tailWord_8354885).sum := by decide
  have hdescent : baseEnd_8354885 < baseStart_8354885 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354912 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 3, 4]
def baseStart_8354912 : Nat := 118140960795 + 8354912 * 2 ^ 59
def prefixEnd_8354912 : Nat := 4983230072969 + 3 ^ 40 * 8354912 * 2
def baseEnd_8354912 : Nat := 1430028560672440200692155

theorem tailTrace_8354912 : CollatzResearch.WordTrace tailWord_8354912 prefixEnd_8354912 1430028560672440200692155 := by
  unfold tailWord_8354912
  simp only [CollatzResearch.WordTrace]
  refine ⟨152364337553794102106485495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203152450071725469475313993 152364337553794102106485495)
  ·
    refine ⟨228546506330691153159728243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152364337553794102106485495 228546506330691153159728243)
    ·
      refine ⟨342819759496036729739592365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228546506330691153159728243 342819759496036729739592365)
      ·
        refine ⟨128557409811013773652347137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342819759496036729739592365 128557409811013773652347137)
        ·
          refine ⟨96418057358260330239260353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128557409811013773652347137 96418057358260330239260353)
          ·
            refine ⟨72313543018695247679445265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96418057358260330239260353 72313543018695247679445265)
            ·
              refine ⟨54235157264021435759583949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72313543018695247679445265 54235157264021435759583949)
              ·
                refine ⟨20338183974008038409843981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54235157264021435759583949 20338183974008038409843981)
                ·
                  refine ⟨7626818990253014403691493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20338183974008038409843981 7626818990253014403691493)
                  ·
                    refine ⟨1430028560672440200692155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7626818990253014403691493 1430028560672440200692155)
                    ·
                      rfl

theorem cell23_8354912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 3, 4].length) (baseStart_8354912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354912 prefixEnd_8354912 := by exact prefixLift 8354912
  have htrace : WordTrace (prefixWord ++ tailWord_8354912) baseStart_8354912 baseEnd_8354912 := by
    simpa [prefixWord, tailWord_8354912, baseEnd_8354912] using wordTrace_append hprefix tailTrace_8354912
  have hstable : (prefixWord ++ tailWord_8354912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354912).length < 2 ^ (prefixWord ++ tailWord_8354912).sum := by decide
  have hdescent : baseEnd_8354912 < baseStart_8354912 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354915 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 4]
def baseStart_8354915 : Nat := 118140960795 + 8354915 * 2 ^ 59
def prefixEnd_8354915 : Nat := 4983230072969 + 3 ^ 40 * 8354915 * 2
def baseEnd_8354915 : Nat := 4290087222459284090338951

theorem tailTrace_8354915 : CollatzResearch.WordTrace tailWord_8354915 prefixEnd_8354915 4290087222459284090338951 := by
  unfold tailWord_8354915
  simp only [CollatzResearch.WordTrace]
  refine ⟨304728784526577335725330199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203152523017718223816886799 304728784526577335725330199)
  ·
    refine ⟨457093176789866003587995299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304728784526577335725330199 457093176789866003587995299)
    ·
      refine ⟨685639765184799005381992949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457093176789866003587995299 685639765184799005381992949)
      ·
        refine ⟨64278727986074906754561839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 685639765184799005381992949 64278727986074906754561839)
        ·
          refine ⟨96418091979112360131842759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64278727986074906754561839 96418091979112360131842759)
          ·
            refine ⟨144627137968668540197764139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96418091979112360131842759 144627137968668540197764139)
            ·
              refine ⟨216940706953002810296646209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144627137968668540197764139 216940706953002810296646209)
              ·
                refine ⟨162705530214752107722484657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216940706953002810296646209 162705530214752107722484657)
                ·
                  refine ⟨122029147661064080791863493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162705530214752107722484657 122029147661064080791863493)
                  ·
                    refine ⟨22880465186449515148474405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122029147661064080791863493 22880465186449515148474405)
                    ·
                      refine ⟨4290087222459284090338951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22880465186449515148474405 4290087222459284090338951)
                      ·
                        rfl

theorem cell23_8354915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_8354915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354915 prefixEnd_8354915 := by exact prefixLift 8354915
  have htrace : WordTrace (prefixWord ++ tailWord_8354915) baseStart_8354915 baseEnd_8354915 := by
    simpa [prefixWord, tailWord_8354915, baseEnd_8354915] using wordTrace_append hprefix tailTrace_8354915
  have hstable : (prefixWord ++ tailWord_8354915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354915).length < 2 ^ (prefixWord ++ tailWord_8354915).sum := by decide
  have hdescent : baseEnd_8354915 < baseStart_8354915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354919 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_8354919 : Nat := 118140960795 + 8354919 * 2 ^ 59
def prefixEnd_8354919 : Nat := 4983230072969 + 3 ^ 40 * 8354919 * 2
def baseEnd_8354919 : Nat := 4290089276381902074688933

theorem tailTrace_8354919 : CollatzResearch.WordTrace tailWord_8354919 prefixEnd_8354919 4290089276381902074688933 := by
  unfold tailWord_8354919
  simp only [CollatzResearch.WordTrace]
  refine ⟨304728930418562844408475811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203152620279041896272317207 304728930418562844408475811)
  ·
    refine ⟨457093395627844266612713717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304728930418562844408475811 457093395627844266612713717)
    ·
      refine ⟨42852505840110399994941911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 457093395627844266612713717 42852505840110399994941911)
      ·
        refine ⟨64278758760165599992412867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42852505840110399994941911 64278758760165599992412867)
        ·
          refine ⟨96418138140248399988619301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64278758760165599992412867 96418138140248399988619301)
          ·
            refine ⟨18078400901296574997866119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96418138140248399988619301 18078400901296574997866119)
            ·
              refine ⟨27117601351944862496799179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18078400901296574997866119 27117601351944862496799179)
              ·
                refine ⟨40676402027917293745198769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27117601351944862496799179 40676402027917293745198769)
                ·
                  refine ⟨30507301520937970308899077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40676402027917293745198769 30507301520937970308899077)
                  ·
                    refine ⟨5720119035175869432918577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30507301520937970308899077 5720119035175869432918577)
                    ·
                      refine ⟨4290089276381902074688933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5720119035175869432918577 4290089276381902074688933)
                      ·
                        rfl

theorem cell23_8354919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_8354919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354919 prefixEnd_8354919 := by exact prefixLift 8354919
  have htrace : WordTrace (prefixWord ++ tailWord_8354919) baseStart_8354919 baseEnd_8354919 := by
    simpa [prefixWord, tailWord_8354919, baseEnd_8354919] using wordTrace_append hprefix tailTrace_8354919
  have hstable : (prefixWord ++ tailWord_8354919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354919).length < 2 ^ (prefixWord ++ tailWord_8354919).sum := by decide
  have hdescent : baseEnd_8354919 < baseStart_8354919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354933 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 2, 5]
def baseStart_8354933 : Nat := 118140960795 + 8354933 * 2 ^ 59
def prefixEnd_8354933 : Nat := 4983230072969 + 3 ^ 40 * 8354933 * 2
def baseEnd_8354933 : Nat := 1430032155037021673304623

theorem tailTrace_8354933 : CollatzResearch.WordTrace tailWord_8354933 prefixEnd_8354933 1430032155037021673304623 := by
  unfold tailWord_8354933
  simp only [CollatzResearch.WordTrace]
  refine ⟨304729441040512124799485453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203152960693674749866323635 304729441040512124799485453)
  ·
    refine ⟨114273540390192046799807045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304729441040512124799485453 114273540390192046799807045)
    ·
      refine ⟨21426288823161008774963821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114273540390192046799807045 21426288823161008774963821)
      ·
        refine ⟨8034858308685378290611433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21426288823161008774963821 8034858308685378290611433)
        ·
          refine ⟨6026143731514033717958575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8034858308685378290611433 6026143731514033717958575)
          ·
            refine ⟨9039215597271050576937863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6026143731514033717958575 9039215597271050576937863)
            ·
              refine ⟨13558823395906575865406795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9039215597271050576937863 13558823395906575865406795)
              ·
                refine ⟨20338235093859863798110193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13558823395906575865406795 20338235093859863798110193)
                ·
                  refine ⟨15253676320394897848582645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20338235093859863798110193 15253676320394897848582645)
                  ·
                    refine ⟨1430032155037021673304623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15253676320394897848582645 1430032155037021673304623)
                    ·
                      rfl

theorem cell23_8354933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_8354933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354933 prefixEnd_8354933 := by exact prefixLift 8354933
  have htrace : WordTrace (prefixWord ++ tailWord_8354933) baseStart_8354933 baseEnd_8354933 := by
    simpa [prefixWord, tailWord_8354933, baseEnd_8354933] using wordTrace_append hprefix tailTrace_8354933
  have hstable : (prefixWord ++ tailWord_8354933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354933).length < 2 ^ (prefixWord ++ tailWord_8354933).sum := by decide
  have hdescent : baseEnd_8354933 < baseStart_8354933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354962 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_8354962 : Nat := 118140960795 + 8354962 * 2 ^ 59
def prefixEnd_8354962 : Nat := 4983230072969 + 3 ^ 40 * 8354962 * 2
def baseEnd_8354962 : Nat := 4290111356050045406451235

theorem tailTrace_8354962 : CollatzResearch.WordTrace tailWord_8354962 prefixEnd_8354962 4290111356050045406451235 := by
  unfold tailWord_8354962
  simp only [CollatzResearch.WordTrace]
  refine ⟨76182624689351765688072785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203153665838271375168194093 76182624689351765688072785)
  ·
    refine ⟨57136968517013824266054589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76182624689351765688072785 57136968517013824266054589)
    ·
      refine ⟨21426363193880184099770471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57136968517013824266054589 21426363193880184099770471)
      ·
        refine ⟨32139544790820276149655707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21426363193880184099770471 32139544790820276149655707)
        ·
          refine ⟨48209317186230414224483561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32139544790820276149655707 48209317186230414224483561)
          ·
            refine ⟨36156987889672810668362671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48209317186230414224483561 36156987889672810668362671)
            ·
              refine ⟨54235481834509216002544007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36156987889672810668362671 54235481834509216002544007)
              ·
                refine ⟨81353222751763824003816011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54235481834509216002544007 81353222751763824003816011)
                ·
                  refine ⟨122029834127645736005724017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81353222751763824003816011 122029834127645736005724017)
                  ·
                    refine ⟨91522375595734302004293013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122029834127645736005724017 91522375595734302004293013)
                    ·
                      refine ⟨4290111356050045406451235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91522375595734302004293013 4290111356050045406451235)
                      ·
                        rfl

theorem cell23_8354962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_8354962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354962 prefixEnd_8354962 := by exact prefixLift 8354962
  have htrace : WordTrace (prefixWord ++ tailWord_8354962) baseStart_8354962 baseEnd_8354962 := by
    simpa [prefixWord, tailWord_8354962, baseEnd_8354962] using wordTrace_append hprefix tailTrace_8354962
  have hstable : (prefixWord ++ tailWord_8354962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354962).length < 2 ^ (prefixWord ++ tailWord_8354962).sum := by decide
  have hdescent : baseEnd_8354962 < baseStart_8354962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354965 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_8354965 : Nat := 118140960795 + 8354965 * 2 ^ 59
def prefixEnd_8354965 : Nat := 4983230072969 + 3 ^ 40 * 8354965 * 2
def baseEnd_8354965 : Nat := 4290112896492008894713721

theorem tailTrace_8354965 : CollatzResearch.WordTrace tailWord_8354965 prefixEnd_8354965 4290112896492008894713721 := by
  unfold tailWord_8354965
  simp only [CollatzResearch.WordTrace]
  refine ⟨304730608176396194264650349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203153738784264129509766899 304730608176396194264650349)
  ·
    refine ⟨114273978066148572849243881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304730608176396194264650349 114273978066148572849243881)
    ·
      refine ⟨85705483549611429636932911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114273978066148572849243881 85705483549611429636932911)
      ·
        refine ⟨128558225324417144455399367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85705483549611429636932911 128558225324417144455399367)
        ·
          refine ⟨192837337986625716683099051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128558225324417144455399367 192837337986625716683099051)
          ·
            refine ⟨289256006979938575024648577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192837337986625716683099051 289256006979938575024648577)
            ·
              refine ⟨216942005234953931268486433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289256006979938575024648577 216942005234953931268486433)
              ·
                refine ⟨162706503926215448451364825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216942005234953931268486433 162706503926215448451364825)
                ·
                  refine ⟨122029877944661586338523619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162706503926215448451364825 122029877944661586338523619)
                  ·
                    refine ⟨183044816916992379507785429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122029877944661586338523619 183044816916992379507785429)
                    ·
                      refine ⟨4290112896492008894713721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183044816916992379507785429 4290112896492008894713721)
                      ·
                        rfl

theorem cell23_8354965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_8354965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354965 prefixEnd_8354965 := by exact prefixLift 8354965
  have htrace : WordTrace (prefixWord ++ tailWord_8354965) baseStart_8354965 baseEnd_8354965 := by
    simpa [prefixWord, tailWord_8354965, baseEnd_8354965] using wordTrace_append hprefix tailTrace_8354965
  have hstable : (prefixWord ++ tailWord_8354965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354965).length < 2 ^ (prefixWord ++ tailWord_8354965).sum := by decide
  have hdescent : baseEnd_8354965 < baseStart_8354965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354985 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 7, 6]
def baseStart_8354985 : Nat := 118140960795 + 8354985 * 2 ^ 59
def prefixEnd_8354985 : Nat := 4983230072969 + 3 ^ 40 * 8354985 * 2
def baseEnd_8354985 : Nat := 1430041055368366272154543

theorem tailTrace_8354985 : CollatzResearch.WordTrace tailWord_8354985 prefixEnd_8354985 1430041055368366272154543 := by
  unfold tailWord_8354985
  simp only [CollatzResearch.WordTrace]
  refine ⟨304731337636323737680378409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203154225090882491786918939 304731337636323737680378409)
  ·
    refine ⟨228548503227242803260283807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304731337636323737680378409 228548503227242803260283807)
    ·
      refine ⟨342822754840864204890425711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228548503227242803260283807 342822754840864204890425711)
      ·
        refine ⟨514234132261296307335638567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342822754840864204890425711 514234132261296307335638567)
        ·
          refine ⟨771351198391944461003457851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514234132261296307335638567 771351198391944461003457851)
          ·
            refine ⟨1157026797587916691505186777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771351198391944461003457851 1157026797587916691505186777)
            ·
              refine ⟨867770098190937518628890083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157026797587916691505186777 867770098190937518628890083)
              ·
                refine ⟨1301655147286406277943335125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867770098190937518628890083 1301655147286406277943335125)
                ·
                  refine ⟨30507542514525147139296917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1301655147286406277943335125 30507542514525147139296917)
                  ·
                    refine ⟨1430041055368366272154543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30507542514525147139296917 1430041055368366272154543)
                    ·
                      rfl

theorem cell23_8354985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_8354985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8354985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8354985 prefixEnd_8354985 := by exact prefixLift 8354985
  have htrace : WordTrace (prefixWord ++ tailWord_8354985) baseStart_8354985 baseEnd_8354985 := by
    simpa [prefixWord, tailWord_8354985, baseEnd_8354985] using wordTrace_append hprefix tailTrace_8354985
  have hstable : (prefixWord ++ tailWord_8354985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354985).length < 2 ^ (prefixWord ++ tailWord_8354985).sum := by decide
  have hdescent : baseEnd_8354985 < baseStart_8354985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355014 : List Nat := [6, 1, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_8355014 : Nat := 118140960795 + 8355014 * 2 ^ 59
def prefixEnd_8355014 : Nat := 4983230072969 + 3 ^ 40 * 8355014 * 2
def baseEnd_8355014 : Nat := 1430046019014693067666999

theorem tailTrace_8355014 : CollatzResearch.WordTrace tailWord_8355014 prefixEnd_8355014 1430046019014693067666999 := by
  unfold tailWord_8355014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9522887354788083613537003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203154930235479117088789397 9522887354788083613537003)
  ·
    refine ⟨14284331032182125420305505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9522887354788083613537003 14284331032182125420305505)
    ·
      refine ⟨10713248274136594065229129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14284331032182125420305505 10713248274136594065229129)
      ·
        refine ⟨8034936205602445548921847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10713248274136594065229129 8034936205602445548921847)
        ·
          refine ⟨12052404308403668323382771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8034936205602445548921847 12052404308403668323382771)
          ·
            refine ⟨18078606462605502485074157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12052404308403668323382771 18078606462605502485074157)
            ·
              refine ⟨6779477423477063431902809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18078606462605502485074157 6779477423477063431902809)
              ·
                refine ⟨5084608067607797573927107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6779477423477063431902809 5084608067607797573927107)
                ·
                  refine ⟨7626912101411696360890661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5084608067607797573927107 7626912101411696360890661)
                  ·
                    refine ⟨1430046019014693067666999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7626912101411696360890661 1430046019014693067666999)
                    ·
                      rfl

theorem cell23_8355014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_8355014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355014 prefixEnd_8355014 := by exact prefixLift 8355014
  have htrace : WordTrace (prefixWord ++ tailWord_8355014) baseStart_8355014 baseEnd_8355014 := by
    simpa [prefixWord, tailWord_8355014, baseEnd_8355014] using wordTrace_append hprefix tailTrace_8355014
  have hstable : (prefixWord ++ tailWord_8355014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355014).length < 2 ^ (prefixWord ++ tailWord_8355014).sum := by decide
  have hdescent : baseEnd_8355014 < baseStart_8355014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355029 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_8355029 : Nat := 118140960795 + 8355029 * 2 ^ 59
def prefixEnd_8355029 : Nat := 4983230072969 + 3 ^ 40 * 8355029 * 2
def baseEnd_8355029 : Nat := 4290145759253896644313427

theorem tailTrace_8355029 : CollatzResearch.WordTrace tailWord_8355029 prefixEnd_8355029 4290145759253896644313427 := by
  unfold tailWord_8355029
  simp only [CollatzResearch.WordTrace]
  refine ⟨304732942448164333194980141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203155294965442888796653427 304732942448164333194980141)
  ·
    refine ⟨114274853418061624948117553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304732942448164333194980141 114274853418061624948117553)
    ·
      refine ⟨85706140063546218711088165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114274853418061624948117553 85706140063546218711088165)
      ·
        refine ⟨16069901261914916008329031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85706140063546218711088165 16069901261914916008329031)
        ·
          refine ⟨24104851892872374012493547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16069901261914916008329031 24104851892872374012493547)
          ·
            refine ⟨36157277839308561018740321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24104851892872374012493547 36157277839308561018740321)
            ·
              refine ⟨27117958379481420764055241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36157277839308561018740321 27117958379481420764055241)
              ·
                refine ⟨20338468784611065573041431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27117958379481420764055241 20338468784611065573041431)
                ·
                  refine ⟨30507703176916598359562147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20338468784611065573041431 30507703176916598359562147)
                  ·
                    refine ⟨45761554765374897539343221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30507703176916598359562147 45761554765374897539343221)
                    ·
                      refine ⟨4290145759253896644313427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45761554765374897539343221 4290145759253896644313427)
                      ·
                        rfl

theorem cell23_8355029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_8355029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355029 prefixEnd_8355029 := by exact prefixLift 8355029
  have htrace : WordTrace (prefixWord ++ tailWord_8355029) baseStart_8355029 baseEnd_8355029 := by
    simpa [prefixWord, tailWord_8355029, baseEnd_8355029] using wordTrace_append hprefix tailTrace_8355029
  have hstable : (prefixWord ++ tailWord_8355029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355029).length < 2 ^ (prefixWord ++ tailWord_8355029).sum := by decide
  have hdescent : baseEnd_8355029 < baseStart_8355029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355059 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 3]
def baseStart_8355059 : Nat := 118140960795 + 8355059 * 2 ^ 59
def prefixEnd_8355059 : Nat := 4983230072969 + 3 ^ 40 * 8355059 * 2
def baseEnd_8355059 : Nat := 4290161163673531526938289

theorem tailTrace_8355059 : CollatzResearch.WordTrace tailWord_8355059 prefixEnd_8355059 4290161163673531526938289 := by
  unfold tailWord_8355059
  simp only [CollatzResearch.WordTrace]
  refine ⟨304734036638055648318572231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203156024425370432212381487 304734036638055648318572231)
  ·
    refine ⟨457101054957083472477858347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304734036638055648318572231 457101054957083472477858347)
    ·
      refine ⟨685651582435625208716787521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457101054957083472477858347 685651582435625208716787521)
      ·
        refine ⟨514238686826718906537590641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685651582435625208716787521 514238686826718906537590641)
        ·
          refine ⟨385679015120039179903192981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514238686826718906537590641 385679015120039179903192981)
          ·
            refine ⟨18078703833751836557962171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 385679015120039179903192981 18078703833751836557962171)
            ·
              refine ⟨27118055750627754836943257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18078703833751836557962171 27118055750627754836943257)
              ·
                refine ⟨20338541812970816127707443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27118055750627754836943257 20338541812970816127707443)
                ·
                  refine ⟨30507812719456224191561165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20338541812970816127707443 30507812719456224191561165)
                  ·
                    refine ⟨11440429769796084071835437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30507812719456224191561165 11440429769796084071835437)
                    ·
                      refine ⟨4290161163673531526938289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11440429769796084071835437 4290161163673531526938289)
                      ·
                        rfl

theorem cell23_8355059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 3].length) (baseStart_8355059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355059 prefixEnd_8355059 := by exact prefixLift 8355059
  have htrace : WordTrace (prefixWord ++ tailWord_8355059) baseStart_8355059 baseEnd_8355059 := by
    simpa [prefixWord, tailWord_8355059, baseEnd_8355059] using wordTrace_append hprefix tailTrace_8355059
  have hstable : (prefixWord ++ tailWord_8355059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355059).length < 2 ^ (prefixWord ++ tailWord_8355059).sum := by decide
  have hdescent : baseEnd_8355059 < baseStart_8355059 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355086 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2]
def baseStart_8355086 : Nat := 118140960795 + 8355086 * 2 ^ 59
def prefixEnd_8355086 : Nat := 4983230072969 + 3 ^ 40 * 8355086 * 2
def baseEnd_8355086 : Nat := 4290175027651202921300665

theorem tailTrace_8355086 : CollatzResearch.WordTrace tailWord_8355086 prefixEnd_8355086 4290175027651202921300665 := by
  unfold tailWord_8355086
  simp only [CollatzResearch.WordTrace]
  refine ⟨38091877676119728991225639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203156680939305221286536741 38091877676119728991225639)
  ·
    refine ⟨57137816514179593486838459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38091877676119728991225639 57137816514179593486838459)
    ·
      refine ⟨85706724771269390230257689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57137816514179593486838459 85706724771269390230257689)
      ·
        refine ⟨64280043578452042672693267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85706724771269390230257689 64280043578452042672693267)
        ·
          refine ⟨96420065367678064009039901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64280043578452042672693267 96420065367678064009039901)
          ·
            refine ⟨36157524512879274003389963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96420065367678064009039901 36157524512879274003389963)
            ·
              refine ⟨54236286769318911005084945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36157524512879274003389963 54236286769318911005084945)
              ·
                refine ⟨40677215076989183253813709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54236286769318911005084945 40677215076989183253813709)
                ·
                  refine ⟨15253955653870943720180141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40677215076989183253813709 15253955653870943720180141)
                  ·
                    refine ⟨5720233370201603895067553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15253955653870943720180141 5720233370201603895067553)
                    ·
                      refine ⟨4290175027651202921300665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5720233370201603895067553 4290175027651202921300665)
                      ·
                        rfl

theorem cell23_8355086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_8355086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355086 prefixEnd_8355086 := by exact prefixLift 8355086
  have htrace : WordTrace (prefixWord ++ tailWord_8355086) baseStart_8355086 baseEnd_8355086 := by
    simpa [prefixWord, tailWord_8355086, baseEnd_8355086] using wordTrace_append hprefix tailTrace_8355086
  have hstable : (prefixWord ++ tailWord_8355086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355086).length < 2 ^ (prefixWord ++ tailWord_8355086).sum := by decide
  have hdescent : baseEnd_8355086 < baseStart_8355086 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355116 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 4, 2, 2]
def baseStart_8355116 : Nat := 118140960795 + 8355116 * 2 ^ 59
def prefixEnd_8355116 : Nat := 4983230072969 + 3 ^ 40 * 8355116 * 2
def baseEnd_8355116 : Nat := 4290190432070837803925527

theorem tailTrace_8355116 : CollatzResearch.WordTrace tailWord_8355116 prefixEnd_8355116 4290190432070837803925527 := by
  unfold tailWord_8355116
  simp only [CollatzResearch.WordTrace]
  refine ⟨152368057799424573526698601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203157410399232764702264801 152368057799424573526698601)
  ·
    refine ⟨114276043349568430145023951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152368057799424573526698601 114276043349568430145023951)
    ·
      refine ⟨171414065024352645217535927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114276043349568430145023951 171414065024352645217535927)
      ·
        refine ⟨257121097536528967826303891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171414065024352645217535927 257121097536528967826303891)
        ·
          refine ⟨385681646304793451739455837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257121097536528967826303891 385681646304793451739455837)
          ·
            refine ⟨144630617364297544402295939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385681646304793451739455837 144630617364297544402295939)
            ·
              refine ⟨216945926046446316603443909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144630617364297544402295939 216945926046446316603443909)
              ·
                refine ⟨40677361133708684363145733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216945926046446316603443909 40677361133708684363145733)
                ·
                  refine ⟨7627005212570378318089825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40677361133708684363145733 7627005212570378318089825)
                  ·
                    refine ⟨5720253909427783738567369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7627005212570378318089825 5720253909427783738567369)
                    ·
                      refine ⟨4290190432070837803925527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5720253909427783738567369 4290190432070837803925527)
                      ·
                        rfl

theorem cell23_8355116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 2, 2].length) (baseStart_8355116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355116 prefixEnd_8355116 := by exact prefixLift 8355116
  have htrace : WordTrace (prefixWord ++ tailWord_8355116) baseStart_8355116 baseEnd_8355116 := by
    simpa [prefixWord, tailWord_8355116, baseEnd_8355116] using wordTrace_append hprefix tailTrace_8355116
  have hstable : (prefixWord ++ tailWord_8355116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355116).length < 2 ^ (prefixWord ++ tailWord_8355116).sum := by decide
  have hdescent : baseEnd_8355116 < baseStart_8355116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355150 : List Nat := [4, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2]
def baseStart_8355150 : Nat := 118140960795 + 8355150 * 2 ^ 59
def prefixEnd_8355150 : Nat := 4983230072969 + 3 ^ 40 * 8355150 * 2
def baseEnd_8355150 : Nat := 4290207890413090670900371

theorem tailTrace_8355150 : CollatzResearch.WordTrace tailWord_8355150 prefixEnd_8355150 4290207890413090670900371 := by
  unfold tailWord_8355150
  simp only [CollatzResearch.WordTrace]
  refine ⟨38092169460090746357516863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203158237120483980573423269 38092169460090746357516863)
  ·
    refine ⟨57138254190136119536275295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38092169460090746357516863 57138254190136119536275295)
    ·
      refine ⟨85707381285204179304412943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57138254190136119536275295 85707381285204179304412943)
      ·
        refine ⟨128561071927806268956619415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85707381285204179304412943 128561071927806268956619415)
        ·
          refine ⟨192841607891709403434929123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128561071927806268956619415 192841607891709403434929123)
          ·
            refine ⟨289262411837564105152393685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192841607891709403434929123 289262411837564105152393685)
            ·
              refine ⟨6779587777442908714509227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 289262411837564105152393685 6779587777442908714509227)
              ·
                refine ⟨10169381666164363071763841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6779587777442908714509227 10169381666164363071763841)
                ·
                  refine ⟨7627036249623272303822881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10169381666164363071763841 7627036249623272303822881)
                  ·
                    refine ⟨5720277187217454227867161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7627036249623272303822881 5720277187217454227867161)
                    ·
                      refine ⟨4290207890413090670900371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5720277187217454227867161 4290207890413090670900371)
                      ·
                        rfl

theorem cell23_8355150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_8355150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355150 prefixEnd_8355150 := by exact prefixLift 8355150
  have htrace : WordTrace (prefixWord ++ tailWord_8355150) baseStart_8355150 baseEnd_8355150 := by
    simpa [prefixWord, tailWord_8355150, baseEnd_8355150] using wordTrace_append hprefix tailTrace_8355150
  have hstable : (prefixWord ++ tailWord_8355150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355150).length < 2 ^ (prefixWord ++ tailWord_8355150).sum := by decide
  have hdescent : baseEnd_8355150 < baseStart_8355150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355152 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 3, 7]
def baseStart_8355152 : Nat := 118140960795 + 8355152 * 2 ^ 59
def prefixEnd_8355152 : Nat := 4983230072969 + 3 ^ 40 * 8355152 * 2
def baseEnd_8355152 : Nat := 1430069639124799887691787

theorem tailTrace_8355152 : CollatzResearch.WordTrace tailWord_8355152 prefixEnd_8355152 1430069639124799887691787 := by
  unfold tailWord_8355152
  simp only [CollatzResearch.WordTrace]
  refine ⟨152368714313359362600853855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203158285751145816801138473 152368714313359362600853855)
  ·
    refine ⟨228553071470039043901280783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152368714313359362600853855 228553071470039043901280783)
    ·
      refine ⟨342829607205058565851921175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228553071470039043901280783 342829607205058565851921175)
      ·
        refine ⟨514244410807587848777881763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342829607205058565851921175 514244410807587848777881763)
        ·
          refine ⟨771366616211381773166822645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514244410807587848777881763 771366616211381773166822645)
          ·
            refine ⟨72315620269817041234389623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 771366616211381773166822645 72315620269817041234389623)
            ·
              refine ⟨108473430404725561851584435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72315620269817041234389623 108473430404725561851584435)
              ·
                refine ⟨162710145607088342777376653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108473430404725561851584435 162710145607088342777376653)
                ·
                  refine ⟨61016304602658128541516245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162710145607088342777376653 61016304602658128541516245)
                  ·
                    refine ⟨1430069639124799887691787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61016304602658128541516245 1430069639124799887691787)
                    ·
                      rfl

theorem cell23_8355152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_8355152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355152 prefixEnd_8355152 := by exact prefixLift 8355152
  have htrace : WordTrace (prefixWord ++ tailWord_8355152) baseStart_8355152 baseEnd_8355152 := by
    simpa [prefixWord, tailWord_8355152, baseEnd_8355152] using wordTrace_append hprefix tailTrace_8355152
  have hstable : (prefixWord ++ tailWord_8355152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355152).length < 2 ^ (prefixWord ++ tailWord_8355152).sum := by decide
  have hdescent : baseEnd_8355152 < baseStart_8355152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355249 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_8355249 : Nat := 118140960795 + 8355249 * 2 ^ 59
def prefixEnd_8355249 : Nat := 4983230072969 + 3 ^ 40 * 8355249 * 2
def baseEnd_8355249 : Nat := 4290258724997885783562415

theorem tailTrace_8355249 : CollatzResearch.WordTrace tailWord_8355249 prefixEnd_8355249 4290258724997885783562415 := by
  unfold tailWord_8355249
  simp only [CollatzResearch.WordTrace]
  refine ⟨304740966507367310767988801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203160644338244873845325867 304740966507367310767988801)
  ·
    refine ⟨228555724880525483075991601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304740966507367310767988801 228555724880525483075991601)
    ·
      refine ⟨171416793660394112306993701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228555724880525483075991601 171416793660394112306993701)
      ·
        refine ⟨32140648811323896057561319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171416793660394112306993701 32140648811323896057561319)
        ·
          refine ⟨48210973216985844086341979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32140648811323896057561319 48210973216985844086341979)
          ·
            refine ⟨72316459825478766129512969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48210973216985844086341979 72316459825478766129512969)
            ·
              refine ⟨54237344869109074597134727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72316459825478766129512969 54237344869109074597134727)
              ·
                refine ⟨81356017303663611895702091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54237344869109074597134727 81356017303663611895702091)
                ·
                  refine ⟨122034025955495417843553137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81356017303663611895702091 122034025955495417843553137)
                  ·
                    refine ⟨91525519466621563382664853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122034025955495417843553137 91525519466621563382664853)
                    ·
                      refine ⟨4290258724997885783562415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91525519466621563382664853 4290258724997885783562415)
                      ·
                        rfl

theorem cell23_8355249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_8355249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355249 prefixEnd_8355249 := by exact prefixLift 8355249
  have htrace : WordTrace (prefixWord ++ tailWord_8355249) baseStart_8355249 baseEnd_8355249 := by
    simpa [prefixWord, tailWord_8355249, baseEnd_8355249] using wordTrace_append hprefix tailTrace_8355249
  have hstable : (prefixWord ++ tailWord_8355249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355249).length < 2 ^ (prefixWord ++ tailWord_8355249).sum := by decide
  have hdescent : baseEnd_8355249 < baseStart_8355249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355276 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 3, 5]
def baseStart_8355276 : Nat := 118140960795 + 8355276 * 2 ^ 59
def prefixEnd_8355276 : Nat := 4983230072969 + 3 ^ 40 * 8355276 * 2
def baseEnd_8355276 : Nat := 1430090862991852392641597

theorem tailTrace_8355276 : CollatzResearch.WordTrace tailWord_8355276 prefixEnd_8355276 1430090862991852392641597 := by
  unfold tailWord_8355276
  simp only [CollatzResearch.WordTrace]
  refine ⟨152370975639134747189610841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203161300852179662919481121 152370975639134747189610841)
  ·
    refine ⟨114278231729351060392208131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152370975639134747189610841 114278231729351060392208131)
    ·
      refine ⟨171417347594026590588312197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114278231729351060392208131 171417347594026590588312197)
      ·
        refine ⟨32140752673879985735308537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171417347594026590588312197 32140752673879985735308537)
        ·
          refine ⟨24105564505409989301481403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32140752673879985735308537 24105564505409989301481403)
          ·
            refine ⟨36158346758114983952222105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24105564505409989301481403 36158346758114983952222105)
            ·
              refine ⟨27118760068586237964166579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36158346758114983952222105 27118760068586237964166579)
              ·
                refine ⟨40678140102879356946249869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27118760068586237964166579 40678140102879356946249869)
                ·
                  refine ⟨15254302538579758854843701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40678140102879356946249869 15254302538579758854843701)
                  ·
                    refine ⟨1430090862991852392641597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15254302538579758854843701 1430090862991852392641597)
                    ·
                      rfl

theorem cell23_8355276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_8355276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355276 prefixEnd_8355276 := by exact prefixLift 8355276
  have htrace : WordTrace (prefixWord ++ tailWord_8355276) baseStart_8355276 baseEnd_8355276 := by
    simpa [prefixWord, tailWord_8355276, baseEnd_8355276] using wordTrace_append hprefix tailTrace_8355276
  have hstable : (prefixWord ++ tailWord_8355276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355276).length < 2 ^ (prefixWord ++ tailWord_8355276).sum := by decide
  have hdescent : baseEnd_8355276 < baseStart_8355276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355290 : List Nat := [3, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3]
def baseStart_8355290 : Nat := 118140960795 + 8355290 * 2 ^ 59
def prefixEnd_8355290 : Nat := 4983230072969 + 3 ^ 40 * 8355290 * 2
def baseEnd_8355290 : Nat := 4290279777704720123149727

theorem tailTrace_8355290 : CollatzResearch.WordTrace tailWord_8355290 prefixEnd_8355290 4290279777704720123149727 := by
  unfold tailWord_8355290
  simp only [CollatzResearch.WordTrace]
  refine ⟨76185615475054693692557831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203161641266812516513487549 76185615475054693692557831)
  ·
    refine ⟨114278423212582040538836747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76185615475054693692557831 114278423212582040538836747)
    ·
      refine ⟨171417634818873060808255121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114278423212582040538836747 171417634818873060808255121)
      ·
        refine ⟨128563226114154795606191341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171417634818873060808255121 128563226114154795606191341)
        ·
          refine ⟨48211209792808048352321753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128563226114154795606191341 48211209792808048352321753)
          ·
            refine ⟨36158407344606036264241315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48211209792808048352321753 36158407344606036264241315)
            ·
              refine ⟨54237611016909054396361973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36158407344606036264241315 54237611016909054396361973)
              ·
                refine ⟨5084776032835223849658935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54237611016909054396361973 5084776032835223849658935)
                ·
                  refine ⟨7627164049252835774488403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5084776032835223849658935 7627164049252835774488403)
                  ·
                    refine ⟨11440746073879253661732605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7627164049252835774488403 11440746073879253661732605)
                    ·
                      refine ⟨4290279777704720123149727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11440746073879253661732605 4290279777704720123149727)
                      ·
                        rfl

theorem cell23_8355290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_8355290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355290 prefixEnd_8355290 := by exact prefixLift 8355290
  have htrace : WordTrace (prefixWord ++ tailWord_8355290) baseStart_8355290 baseEnd_8355290 := by
    simpa [prefixWord, tailWord_8355290, baseEnd_8355290] using wordTrace_append hprefix tailTrace_8355290
  have hstable : (prefixWord ++ tailWord_8355290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355290).length < 2 ^ (prefixWord ++ tailWord_8355290).sum := by decide
  have hdescent : baseEnd_8355290 < baseStart_8355290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355293 : List Nat := [1, 4, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_8355293 : Nat := 118140960795 + 8355293 * 2 ^ 59
def prefixEnd_8355293 : Nat := 4983230072969 + 3 ^ 40 * 8355293 * 2
def baseEnd_8355293 : Nat := 1430093772715561203804071

theorem tailTrace_8355293 : CollatzResearch.WordTrace tailWord_8355293 prefixEnd_8355293 1430093772715561203804071 := by
  unfold tailWord_8355293
  simp only [CollatzResearch.WordTrace]
  refine ⟨304742571319207906282590533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203161714212805270855060355 304742571319207906282590533)
  ·
    refine ⟨57139232122351482427985725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304742571319207906282590533 57139232122351482427985725)
    ·
      refine ⟨21427212045881805910494647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57139232122351482427985725 21427212045881805910494647)
      ·
        refine ⟨32140818068822708865741971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21427212045881805910494647 32140818068822708865741971)
        ·
          refine ⟨48211227103234063298612957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32140818068822708865741971 48211227103234063298612957)
          ·
            refine ⟨18079210163712773736979859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48211227103234063298612957 18079210163712773736979859)
            ·
              refine ⟨27118815245569160605469789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18079210163712773736979859 27118815245569160605469789)
              ·
                refine ⟨10169555717088435227051171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27118815245569160605469789 10169555717088435227051171)
                ·
                  refine ⟨15254333575632652840576757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10169555717088435227051171 15254333575632652840576757)
                  ·
                    refine ⟨1430093772715561203804071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15254333575632652840576757 1430093772715561203804071)
                    ·
                      rfl

theorem cell23_8355293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_8355293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355293 prefixEnd_8355293 := by exact prefixLift 8355293
  have htrace : WordTrace (prefixWord ++ tailWord_8355293) baseStart_8355293 baseEnd_8355293 := by
    simpa [prefixWord, tailWord_8355293, baseEnd_8355293] using wordTrace_append hprefix tailTrace_8355293
  have hstable : (prefixWord ++ tailWord_8355293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355293).length < 2 ^ (prefixWord ++ tailWord_8355293).sum := by decide
  have hdescent : baseEnd_8355293 < baseStart_8355293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355330 : List Nat := [3, 4, 1, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_8355330 : Nat := 118140960795 + 8355330 * 2 ^ 59
def prefixEnd_8355330 : Nat := 4983230072969 + 3 ^ 40 * 8355330 * 2
def baseEnd_8355330 : Nat := 4290300316930899966649543

theorem tailTrace_8355330 : CollatzResearch.WordTrace tailWord_8355330 prefixEnd_8355330 4290300316930899966649543 := by
  unfold tailWord_8355330
  simp only [CollatzResearch.WordTrace]
  refine ⟨76185980205018465400421861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203162613880049241067791629 76185980205018465400421861)
  ·
    refine ⟨14284871288440962262579099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76185980205018465400421861 14284871288440962262579099)
    ·
      refine ⟨21427306932661443393868649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14284871288440962262579099 21427306932661443393868649)
      ·
        refine ⟨16070480199496082545401487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21427306932661443393868649 16070480199496082545401487)
        ·
          refine ⟨24105720299244123818102231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16070480199496082545401487 24105720299244123818102231)
          ·
            refine ⟨36158580448866185727153347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24105720299244123818102231 36158580448866185727153347)
            ·
              refine ⟨54237870673299278590730021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36158580448866185727153347 54237870673299278590730021)
              ·
                refine ⟨10169600751243614735761879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54237870673299278590730021 10169600751243614735761879)
                ·
                  refine ⟨15254401126865422103642819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10169600751243614735761879 15254401126865422103642819)
                  ·
                    refine ⟨22881601690298133155464229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15254401126865422103642819 22881601690298133155464229)
                    ·
                      refine ⟨4290300316930899966649543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22881601690298133155464229 4290300316930899966649543)
                      ·
                        rfl

theorem cell23_8355330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_8355330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355330 prefixEnd_8355330 := by exact prefixLift 8355330
  have htrace : WordTrace (prefixWord ++ tailWord_8355330) baseStart_8355330 baseEnd_8355330 := by
    simpa [prefixWord, tailWord_8355330, baseEnd_8355330] using wordTrace_append hprefix tailTrace_8355330
  have hstable : (prefixWord ++ tailWord_8355330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355330).length < 2 ^ (prefixWord ++ tailWord_8355330).sum := by decide
  have hdescent : baseEnd_8355330 < baseStart_8355330 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355336 : List Nat := [2, 1, 3, 2, 1, 1, 6, 7]
def baseStart_8355336 : Nat := 118140960795 + 8355336 * 2 ^ 59
def prefixEnd_8355336 : Nat := 4983230072969 + 3 ^ 40 * 8355336 * 2
def baseEnd_8355336 : Nat := 158900125844993590487945

theorem tailTrace_8355336 : CollatzResearch.WordTrace tailWord_8355336 prefixEnd_8355336 158900125844993590487945 := by
  unfold tailWord_8355336
  simp only [CollatzResearch.WordTrace]
  refine ⟨152372069829026062313202931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203162759772034749750937241 152372069829026062313202931)
  ·
    refine ⟨228558104743539093469804397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152372069829026062313202931 228558104743539093469804397)
    ·
      refine ⟨85709289278827160051176649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228558104743539093469804397 85709289278827160051176649)
      ·
        refine ⟨64281966959120370038382487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85709289278827160051176649 64281966959120370038382487)
        ·
          refine ⟨96422950438680555057573731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64281966959120370038382487 96422950438680555057573731)
          ·
            refine ⟨144634425658020832586360597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96422950438680555057573731 144634425658020832586360597)
            ·
              refine ⟨6779738702719726527485653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144634425658020832586360597 6779738702719726527485653)
              ·
                refine ⟨158900125844993590487945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6779738702719726527485653 158900125844993590487945)
                ·
                  rfl

theorem cell23_8355336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 7].length) (baseStart_8355336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355336 prefixEnd_8355336 := by exact prefixLift 8355336
  have htrace : WordTrace (prefixWord ++ tailWord_8355336) baseStart_8355336 baseEnd_8355336 := by
    simpa [prefixWord, tailWord_8355336, baseEnd_8355336] using wordTrace_append hprefix tailTrace_8355336
  have hstable : (prefixWord ++ tailWord_8355336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355336).length < 2 ^ (prefixWord ++ tailWord_8355336).sum := by decide
  have hdescent : baseEnd_8355336 < baseStart_8355336 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355347 : List Nat := [1, 1, 1, 2, 1, 6, 3, 3, 1, 2, 2]
def baseStart_8355347 : Nat := 118140960795 + 8355347 * 2 ^ 59
def prefixEnd_8355347 : Nat := 4983230072969 + 3 ^ 40 * 8355347 * 2
def baseEnd_8355347 : Nat := 4290309046102026400136965

theorem tailTrace_8355347 : CollatzResearch.WordTrace tailWord_8355347 prefixEnd_8355347 4290309046102026400136965 := by
  unfold tailWord_8355347
  simp only [CollatzResearch.WordTrace]
  refine ⟨304744540861012273505056295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203163027240674849003370863 304744540861012273505056295)
  ·
    refine ⟨457116811291518410257584443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304744540861012273505056295 457116811291518410257584443)
    ·
      refine ⟨685675216937277615386376665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457116811291518410257584443 685675216937277615386376665)
      ·
        refine ⟨514256412702958211539782499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685675216937277615386376665 514256412702958211539782499)
        ·
          refine ⟨771384619054437317309673749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514256412702958211539782499 771384619054437317309673749)
          ·
            refine ⟨36158654018176749248890957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 771384619054437317309673749 36158654018176749248890957)
            ·
              refine ⟨13559495256816280968334109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36158654018176749248890957 13559495256816280968334109)
              ·
                refine ⟨5084810721306105363125291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13559495256816280968334109 5084810721306105363125291)
                ·
                  refine ⟨7627216081959158044687937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5084810721306105363125291 7627216081959158044687937)
                  ·
                    refine ⟨5720412061469368533515953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7627216081959158044687937 5720412061469368533515953)
                    ·
                      refine ⟨4290309046102026400136965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5720412061469368533515953 4290309046102026400136965)
                      ·
                        rfl

theorem cell23_8355347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 1, 2, 2].length) (baseStart_8355347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355347 prefixEnd_8355347 := by exact prefixLift 8355347
  have htrace : WordTrace (prefixWord ++ tailWord_8355347) baseStart_8355347 baseEnd_8355347 := by
    simpa [prefixWord, tailWord_8355347, baseEnd_8355347] using wordTrace_append hprefix tailTrace_8355347
  have hstable : (prefixWord ++ tailWord_8355347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355347).length < 2 ^ (prefixWord ++ tailWord_8355347).sum := by decide
  have hdescent : baseEnd_8355347 < baseStart_8355347 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355358 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_8355358 : Nat := 118140960795 + 8355358 * 2 ^ 59
def prefixEnd_8355358 : Nat := 4983230072969 + 3 ^ 40 * 8355358 * 2
def baseEnd_8355358 : Nat := 4290314694389225857099415

theorem tailTrace_8355358 : CollatzResearch.WordTrace tailWord_8355358 prefixEnd_8355358 4290314694389225857099415 := by
  unfold tailWord_8355358
  simp only [CollatzResearch.WordTrace]
  refine ⟨38093117757996552797963341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203163294709314948255804485 38093117757996552797963341)
  ·
    refine ⟨14284919159248707299236253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38093117757996552797963341 14284919159248707299236253)
    ·
      refine ⟨5356844684718265237213595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14284919159248707299236253 5356844684718265237213595)
      ·
        refine ⟨8035267027077397855820393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5356844684718265237213595 8035267027077397855820393)
        ·
          refine ⟨6026450270308048391865295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8035267027077397855820393 6026450270308048391865295)
          ·
            refine ⟨9039675405462072587797943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6026450270308048391865295 9039675405462072587797943)
            ·
              refine ⟨13559513108193108881696915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9039675405462072587797943 13559513108193108881696915)
              ·
                refine ⟨20339269662289663322545373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13559513108193108881696915 20339269662289663322545373)
                ·
                  refine ⟨7627226123358623745954515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20339269662289663322545373 7627226123358623745954515)
                  ·
                    refine ⟨11440839185037935618931773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7627226123358623745954515 11440839185037935618931773)
                    ·
                      refine ⟨4290314694389225857099415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11440839185037935618931773 4290314694389225857099415)
                      ·
                        rfl

theorem cell23_8355358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_8355358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355358 prefixEnd_8355358 := by exact prefixLift 8355358
  have htrace : WordTrace (prefixWord ++ tailWord_8355358) baseStart_8355358 baseEnd_8355358 := by
    simpa [prefixWord, tailWord_8355358, baseEnd_8355358] using wordTrace_append hprefix tailTrace_8355358
  have hstable : (prefixWord ++ tailWord_8355358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355358).length < 2 ^ (prefixWord ++ tailWord_8355358).sum := by decide
  have hdescent : baseEnd_8355358 < baseStart_8355358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355416 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_8355416 : Nat := 118140960795 + 8355416 * 2 ^ 59
def prefixEnd_8355416 : Nat := 4983230072969 + 3 ^ 40 * 8355416 * 2
def baseEnd_8355416 : Nat := 4290344476267186630174147

theorem tailTrace_8355416 : CollatzResearch.WordTrace tailWord_8355416 prefixEnd_8355416 4290344476267186630174147 := by
  unfold tailWord_8355416
  simp only [CollatzResearch.WordTrace]
  refine ⟨152373528748881149144659051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203164704998508198859545401 152373528748881149144659051)
  ·
    refine ⟨228560293123321723716988577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152373528748881149144659051 228560293123321723716988577)
    ·
      refine ⟨171420219842491292787741433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228560293123321723716988577 171420219842491292787741433)
      ·
        refine ⟨128565164881868469590806075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171420219842491292787741433 128565164881868469590806075)
        ·
          refine ⟨192847747322802704386209113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128565164881868469590806075 192847747322802704386209113)
          ·
            refine ⟨144635810492102028289656835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192847747322802704386209113 144635810492102028289656835)
            ·
              refine ⟨216953715738153042434485253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144635810492102028289656835 216953715738153042434485253)
              ·
                refine ⟨40678821700903695456465985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216953715738153042434485253 40678821700903695456465985)
                ·
                  refine ⟨30509116275677771592349489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40678821700903695456465985 30509116275677771592349489)
                  ·
                    refine ⟨22881837206758328694262117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30509116275677771592349489 22881837206758328694262117)
                    ·
                      refine ⟨4290344476267186630174147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22881837206758328694262117 4290344476267186630174147)
                      ·
                        rfl

theorem cell23_8355416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_8355416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355416 prefixEnd_8355416 := by exact prefixLift 8355416
  have htrace : WordTrace (prefixWord ++ tailWord_8355416) baseStart_8355416 baseEnd_8355416 := by
    simpa [prefixWord, tailWord_8355416, baseEnd_8355416] using wordTrace_append hprefix tailTrace_8355416
  have hstable : (prefixWord ++ tailWord_8355416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355416).length < 2 ^ (prefixWord ++ tailWord_8355416).sum := by decide
  have hdescent : baseEnd_8355416 < baseStart_8355416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355437 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_8355437 : Nat := 118140960795 + 8355437 * 2 ^ 59
def prefixEnd_8355437 : Nat := 4983230072969 + 3 ^ 40 * 8355437 * 2
def baseEnd_8355437 : Nat := 4290355259360931048011551

theorem tailTrace_8355437 : CollatzResearch.WordTrace tailWord_8355437 prefixEnd_8355437 4290355259360931048011551 := by
  unfold tailWord_8355437
  simp only [CollatzResearch.WordTrace]
  refine ⟨304747823430686218875832565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203165215620457479250555043 304747823430686218875832565)
  ·
    refine ⟨28570108446626833019609303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304747823430686218875832565 28570108446626833019609303)
    ·
      refine ⟨42855162669940249529413955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28570108446626833019609303 42855162669940249529413955)
      ·
        refine ⟨64282744004910374294120933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42855162669940249529413955 64282744004910374294120933)
        ·
          refine ⟨12053014500920695180147675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64282744004910374294120933 12053014500920695180147675)
          ·
            refine ⟨18079521751381042770221513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12053014500920695180147675 18079521751381042770221513)
            ·
              refine ⟨13559641313535782077666135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18079521751381042770221513 13559641313535782077666135)
              ·
                refine ⟨20339461970303673116499203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13559641313535782077666135 20339461970303673116499203)
                ·
                  refine ⟨30509192955455509674748805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20339461970303673116499203 30509192955455509674748805)
                  ·
                    refine ⟨5720473679147908064015401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30509192955455509674748805 5720473679147908064015401)
                    ·
                      refine ⟨4290355259360931048011551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5720473679147908064015401 4290355259360931048011551)
                      ·
                        rfl

theorem cell23_8355437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_8355437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355437 prefixEnd_8355437 := by exact prefixLift 8355437
  have htrace : WordTrace (prefixWord ++ tailWord_8355437) baseStart_8355437 baseEnd_8355437 := by
    simpa [prefixWord, tailWord_8355437, baseEnd_8355437] using wordTrace_append hprefix tailTrace_8355437
  have hstable : (prefixWord ++ tailWord_8355437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355437).length < 2 ^ (prefixWord ++ tailWord_8355437).sum := by decide
  have hdescent : baseEnd_8355437 < baseStart_8355437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355456 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 1, 7]
def baseStart_8355456 : Nat := 118140960795 + 8355456 * 2 ^ 59
def prefixEnd_8355456 : Nat := 4983230072969 + 3 ^ 40 * 8355456 * 2
def baseEnd_8355456 : Nat := 1430121671831122157891321

theorem tailTrace_8355456 : CollatzResearch.WordTrace tailWord_8355456 prefixEnd_8355456 1430121671831122157891321 := by
  unfold tailWord_8355456
  simp only [CollatzResearch.WordTrace]
  refine ⟨152374258208808692560387111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203165677611744923413849481 152374258208808692560387111)
  ·
    refine ⟨228561387313213038840580667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152374258208808692560387111 228561387313213038840580667)
    ·
      refine ⟨342842080969819558260871001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228561387313213038840580667 342842080969819558260871001)
      ·
        refine ⟨257131560727364668695653251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342842080969819558260871001 257131560727364668695653251)
        ·
          refine ⟨385697341091047003043479877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257131560727364668695653251 385697341091047003043479877)
          ·
            refine ⟨72318251454571313070652477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 385697341091047003043479877 72318251454571313070652477)
            ·
              refine ⟨27119344295464242401494679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72318251454571313070652477 27119344295464242401494679)
              ·
                refine ⟨40679016443196363602242019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27119344295464242401494679 40679016443196363602242019)
                ·
                  refine ⟨61018524664794545403363029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40679016443196363602242019 61018524664794545403363029)
                  ·
                    refine ⟨1430121671831122157891321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61018524664794545403363029 1430121671831122157891321)
                    ·
                      rfl

theorem cell23_8355456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_8355456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355456 prefixEnd_8355456 := by exact prefixLift 8355456
  have htrace : WordTrace (prefixWord ++ tailWord_8355456) baseStart_8355456 baseEnd_8355456 := by
    simpa [prefixWord, tailWord_8355456, baseEnd_8355456] using wordTrace_append hprefix tailTrace_8355456
  have hstable : (prefixWord ++ tailWord_8355456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355456).length < 2 ^ (prefixWord ++ tailWord_8355456).sum := by decide
  have hdescent : baseEnd_8355456 < baseStart_8355456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355503 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 3, 4]
def baseStart_8355503 : Nat := 118140960795 + 8355503 * 2 ^ 59
def prefixEnd_8355503 : Nat := 4983230072969 + 3 ^ 40 * 8355503 * 2
def baseEnd_8355503 : Nat := 1430129716361375929928749

theorem tailTrace_8355503 : CollatzResearch.WordTrace tailWord_8355503 prefixEnd_8355503 1430129716361375929928749 := by
  unfold tailWord_8355503
  simp only [CollatzResearch.WordTrace]
  refine ⟨304750230648447112147735163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203166820432298074765156775 304750230648447112147735163)
  ·
    refine ⟨457125345972670668221602745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304750230648447112147735163 457125345972670668221602745)
    ·
      refine ⟨342844009479503001166202059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457125345972670668221602745 342844009479503001166202059)
      ·
        refine ⟨514266014219254501749303089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342844009479503001166202059 514266014219254501749303089)
        ·
          refine ⟨385699510664440876311977317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514266014219254501749303089 385699510664440876311977317)
          ·
            refine ⟨72318658249582664308495747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 385699510664440876311977317 72318658249582664308495747)
            ·
              refine ⟨108477987374373996462743621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72318658249582664308495747 108477987374373996462743621)
              ·
                refine ⟨20339622632695124336764429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108477987374373996462743621 20339622632695124336764429)
                ·
                  refine ⟨7627358487260671626286661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20339622632695124336764429 7627358487260671626286661)
                  ·
                    refine ⟨1430129716361375929928749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7627358487260671626286661 1430129716361375929928749)
                    ·
                      rfl

theorem cell23_8355503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 4].length) (baseStart_8355503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355503 prefixEnd_8355503 := by exact prefixLift 8355503
  have htrace : WordTrace (prefixWord ++ tailWord_8355503) baseStart_8355503 baseEnd_8355503 := by
    simpa [prefixWord, tailWord_8355503, baseEnd_8355503] using wordTrace_append hprefix tailTrace_8355503
  have hstable : (prefixWord ++ tailWord_8355503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355503).length < 2 ^ (prefixWord ++ tailWord_8355503).sum := by decide
  have hdescent : baseEnd_8355503 < baseStart_8355503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355513 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 1, 4, 3]
def baseStart_8355513 : Nat := 118140960795 + 8355513 * 2 ^ 59
def prefixEnd_8355513 : Nat := 4983230072969 + 3 ^ 40 * 8355513 * 2
def baseEnd_8355513 : Nat := 4290394283890672750661201

theorem tailTrace_8355513 : CollatzResearch.WordTrace tailWord_8355513 prefixEnd_8355513 4290394283890672750661201 := by
  unfold tailWord_8355513
  simp only [CollatzResearch.WordTrace]
  refine ⟨304750595378410883855599193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203167063585607255903732795 304750595378410883855599193)
  ·
    refine ⟨228562946533808162891699395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304750595378410883855599193 228562946533808162891699395)
    ·
      refine ⟨342844419800712244337549093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228562946533808162891699395 342844419800712244337549093)
      ·
        refine ⟨64283328712633545813290455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342844419800712244337549093 64283328712633545813290455)
        ·
          refine ⟨96424993068950318719935683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64283328712633545813290455 96424993068950318719935683)
          ·
            refine ⟨144637489603425478079903525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96424993068950318719935683 144637489603425478079903525)
            ·
              refine ⟨27119529300642277139981911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144637489603425478079903525 27119529300642277139981911)
              ·
                refine ⟨40679293950963415709972867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27119529300642277139981911 40679293950963415709972867)
                ·
                  refine ⟨61018940926445123564959301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40679293950963415709972867 61018940926445123564959301)
                  ·
                    refine ⟨11441051423708460668429869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61018940926445123564959301 11441051423708460668429869)
                    ·
                      refine ⟨4290394283890672750661201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11441051423708460668429869 4290394283890672750661201)
                      ·
                        rfl

theorem cell23_8355513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_8355513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355513 prefixEnd_8355513 := by exact prefixLift 8355513
  have htrace : WordTrace (prefixWord ++ tailWord_8355513) baseStart_8355513 baseEnd_8355513 := by
    simpa [prefixWord, tailWord_8355513, baseEnd_8355513] using wordTrace_append hprefix tailTrace_8355513
  have hstable : (prefixWord ++ tailWord_8355513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355513).length < 2 ^ (prefixWord ++ tailWord_8355513).sum := by decide
  have hdescent : baseEnd_8355513 < baseStart_8355513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355536 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 6]
def baseStart_8355536 : Nat := 118140960795 + 8355536 * 2 ^ 59
def prefixEnd_8355536 : Nat := 4983230072969 + 3 ^ 40 * 8355536 * 2
def baseEnd_8355536 : Nat := 4290406093945726160673595

theorem tailTrace_8355536 : CollatzResearch.WordTrace tailWord_8355536 prefixEnd_8355536 4290406093945726160673595 := by
  unfold tailWord_8355536
  simp only [CollatzResearch.WordTrace]
  refine ⟨152375717128663779391843231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203167622838218372522457641 152375717128663779391843231)
  ·
    refine ⟨228563575692995669087764847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152375717128663779391843231 228563575692995669087764847)
    ·
      refine ⟨342845363539493503631647271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228563575692995669087764847 342845363539493503631647271)
      ·
        refine ⟨514268045309240255447470907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342845363539493503631647271 514268045309240255447470907)
        ·
          refine ⟨771402067963860383171206361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514268045309240255447470907 771402067963860383171206361)
          ·
            refine ⟨578551550972895287378404771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 771402067963860383171206361 578551550972895287378404771)
            ·
              refine ⟨867827326459342931067607157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578551550972895287378404771 867827326459342931067607157)
              ·
                refine ⟨81358811855563399787588171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 867827326459342931067607157 81358811855563399787588171)
                ·
                  refine ⟨122038217783345099681382257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81358811855563399787588171 122038217783345099681382257)
                  ·
                    refine ⟨91528663337508824761036693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122038217783345099681382257 91528663337508824761036693)
                    ·
                      refine ⟨4290406093945726160673595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91528663337508824761036693 4290406093945726160673595)
                      ·
                        rfl

theorem cell23_8355536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_8355536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355536 prefixEnd_8355536 := by exact prefixLift 8355536
  have htrace : WordTrace (prefixWord ++ tailWord_8355536) baseStart_8355536 baseEnd_8355536 := by
    simpa [prefixWord, tailWord_8355536, baseEnd_8355536] using wordTrace_append hprefix tailTrace_8355536
  have hstable : (prefixWord ++ tailWord_8355536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355536).length < 2 ^ (prefixWord ++ tailWord_8355536).sum := by decide
  have hdescent : baseEnd_8355536 < baseStart_8355536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355594 : List Nat := [3, 1, 2, 2, 1, 4, 1, 4, 1, 1, 3]
def baseStart_8355594 : Nat := 118140960795 + 8355594 * 2 ^ 59
def prefixEnd_8355594 : Nat := 4983230072969 + 3 ^ 40 * 8355594 * 2
def baseEnd_8355594 : Nat := 4290435875823686933748329

theorem tailTrace_8355594 : CollatzResearch.WordTrace tailWord_8355594 prefixEnd_8355594 4290435875823686933748329 := by
  unfold tailWord_8355594
  simp only [CollatzResearch.WordTrace]
  refine ⟨76188387422779358672324459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203169033127411623126198557 76188387422779358672324459)
  ·
    refine ⟨114282581134169038008486689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76188387422779358672324459 114282581134169038008486689)
    ·
      refine ⟨85711935850626778506365017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114282581134169038008486689 85711935850626778506365017)
      ·
        refine ⟨64283951887970083879773763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85711935850626778506365017 64283951887970083879773763)
        ·
          refine ⟨96425927831955125819660645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64283951887970083879773763 96425927831955125819660645)
          ·
            refine ⟨18079861468491586091186371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96425927831955125819660645 18079861468491586091186371)
            ·
              refine ⟨27119792202737379136779557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18079861468491586091186371 27119792202737379136779557)
              ·
                refine ⟨5084961038013258588146167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27119792202737379136779557 5084961038013258588146167)
                ·
                  refine ⟨7627441557019887882219251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5084961038013258588146167 7627441557019887882219251)
                  ·
                    refine ⟨11441162335529831823328877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7627441557019887882219251 11441162335529831823328877)
                    ·
                      refine ⟨4290435875823686933748329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11441162335529831823328877 4290435875823686933748329)
                      ·
                        rfl

theorem cell23_8355594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_8355594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355594 prefixEnd_8355594 := by exact prefixLift 8355594
  have htrace : WordTrace (prefixWord ++ tailWord_8355594) baseStart_8355594 baseEnd_8355594 := by
    simpa [prefixWord, tailWord_8355594, baseEnd_8355594] using wordTrace_append hprefix tailTrace_8355594
  have hstable : (prefixWord ++ tailWord_8355594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355594).length < 2 ^ (prefixWord ++ tailWord_8355594).sum := by decide
  have hdescent : baseEnd_8355594 < baseStart_8355594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355610 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 1, 6]
def baseStart_8355610 : Nat := 118140960795 + 8355610 * 2 ^ 59
def prefixEnd_8355610 : Nat := 4983230072969 + 3 ^ 40 * 8355610 * 2
def baseEnd_8355610 : Nat := 1430148030504719623716085

theorem tailTrace_8355610 : CollatzResearch.WordTrace tailWord_8355610 prefixEnd_8355610 1430148030504719623716085 := by
  unfold tailWord_8355610
  simp only [CollatzResearch.WordTrace]
  refine ⟨76188533314764867355470071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203169422172706312947920189 76188533314764867355470071)
  ·
    refine ⟨114282799972147301033205107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76188533314764867355470071 114282799972147301033205107)
    ·
      refine ⟨171424199958220951549807661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114282799972147301033205107 171424199958220951549807661)
      ·
        refine ⟨64284074984332856831177873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171424199958220951549807661 64284074984332856831177873)
        ·
          refine ⟨48213056238249642623383405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64284074984332856831177873 48213056238249642623383405)
          ·
            refine ⟨18079896089343615983768777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48213056238249642623383405 18079896089343615983768777)
            ·
              refine ⟨13559922067007711987826583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18079896089343615983768777 13559922067007711987826583)
              ·
                refine ⟨20339883100511567981739875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13559922067007711987826583 20339883100511567981739875)
                ·
                  refine ⟨30509824650767351972609813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20339883100511567981739875 30509824650767351972609813)
                  ·
                    refine ⟨1430148030504719623716085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30509824650767351972609813 1430148030504719623716085)
                    ·
                      rfl

theorem cell23_8355610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_8355610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355610 prefixEnd_8355610 := by exact prefixLift 8355610
  have htrace : WordTrace (prefixWord ++ tailWord_8355610) baseStart_8355610 baseEnd_8355610 := by
    simpa [prefixWord, tailWord_8355610, baseEnd_8355610] using wordTrace_append hprefix tailTrace_8355610
  have hstable : (prefixWord ++ tailWord_8355610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355610).length < 2 ^ (prefixWord ++ tailWord_8355610).sum := by decide
  have hdescent : baseEnd_8355610 < baseStart_8355610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355617 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 5, 2, 2]
def baseStart_8355617 : Nat := 118140960795 + 8355617 * 2 ^ 59
def prefixEnd_8355617 : Nat := 4983230072969 + 3 ^ 40 * 8355617 * 2
def baseEnd_8355617 : Nat := 4290447685878740343760723

theorem tailTrace_8355617 : CollatzResearch.WordTrace tailWord_8355617 prefixEnd_8355617 4290447685878740343760723 := by
  unfold tailWord_8355617
  simp only [CollatzResearch.WordTrace]
  refine ⟨304754388570034109617385105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203169592380022739744923403 304754388570034109617385105)
  ·
    refine ⟨228565791427525582213038829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304754388570034109617385105 228565791427525582213038829)
    ·
      refine ⟨85712171785322093329889561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228565791427525582213038829 85712171785322093329889561)
      ·
        refine ⟨64284128838991569997417171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85712171785322093329889561 64284128838991569997417171)
        ·
          refine ⟨96426193258487354996125757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64284128838991569997417171 96426193258487354996125757)
          ·
            refine ⟨36159822471932758123547159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96426193258487354996125757 36159822471932758123547159)
            ·
              refine ⟨54239733707899137185320739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36159822471932758123547159 54239733707899137185320739)
              ·
                refine ⟨81359600561848705777981109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54239733707899137185320739 81359600561848705777981109)
                ·
                  refine ⟨7627462552673316166685729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81359600561848705777981109 7627462552673316166685729)
                  ·
                    refine ⟨5720596914504987125014297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7627462552673316166685729 5720596914504987125014297)
                    ·
                      refine ⟨4290447685878740343760723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5720596914504987125014297 4290447685878740343760723)
                      ·
                        rfl

theorem cell23_8355617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_8355617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355617 prefixEnd_8355617 := by exact prefixLift 8355617
  have htrace : WordTrace (prefixWord ++ tailWord_8355617) baseStart_8355617 baseEnd_8355617 := by
    simpa [prefixWord, tailWord_8355617, baseEnd_8355617] using wordTrace_append hprefix tailTrace_8355617
  have hstable : (prefixWord ++ tailWord_8355617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355617).length < 2 ^ (prefixWord ++ tailWord_8355617).sum := by decide
  have hdescent : baseEnd_8355617 < baseStart_8355617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355634 : List Nat := [3, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4]
def baseStart_8355634 : Nat := 118140960795 + 8355634 * 2 ^ 59
def prefixEnd_8355634 : Nat := 4983230072969 + 3 ^ 40 * 8355634 * 2
def baseEnd_8355634 : Nat := 4290456415049866777248145

theorem tailTrace_8355634 : CollatzResearch.WordTrace tailWord_8355634 prefixEnd_8355634 4290456415049866777248145 := by
  unfold tailWord_8355634
  simp only [CollatzResearch.WordTrace]
  refine ⟨76188752152743130380188489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203170005740648347680502637 76188752152743130380188489)
  ·
    refine ⟨57141564114557347785141367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76188752152743130380188489 57141564114557347785141367)
    ·
      refine ⟨85712346171836021677712051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57141564114557347785141367 85712346171836021677712051)
      ·
        refine ⟨128568519257754032516568077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85712346171836021677712051 128568519257754032516568077)
        ·
          refine ⟨48213194721657762193713029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128568519257754032516568077 48213194721657762193713029)
          ·
            refine ⟨9039974010310830411321193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48213194721657762193713029 9039974010310830411321193)
            ·
              refine ⟨6779980507733122808490895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9039974010310830411321193 6779980507733122808490895)
              ·
                refine ⟨10169970761599684212736343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6779980507733122808490895 10169970761599684212736343)
                ·
                  refine ⟨15254956142399526319104515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10169970761599684212736343 15254956142399526319104515)
                  ·
                    refine ⟨22882434213599289478656773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15254956142399526319104515 22882434213599289478656773)
                    ·
                      refine ⟨4290456415049866777248145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22882434213599289478656773 4290456415049866777248145)
                      ·
                        rfl

theorem cell23_8355634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_8355634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355634 prefixEnd_8355634 := by exact prefixLift 8355634
  have htrace : WordTrace (prefixWord ++ tailWord_8355634) baseStart_8355634 baseEnd_8355634 := by
    simpa [prefixWord, tailWord_8355634, baseEnd_8355634] using wordTrace_append hprefix tailTrace_8355634
  have hstable : (prefixWord ++ tailWord_8355634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355634).length < 2 ^ (prefixWord ++ tailWord_8355634).sum := by decide
  have hdescent : baseEnd_8355634 < baseStart_8355634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355654 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_8355654 : Nat := 118140960795 + 8355654 * 2 ^ 59
def prefixEnd_8355654 : Nat := 4983230072969 + 3 ^ 40 * 8355654 * 2
def baseEnd_8355654 : Nat := 4290466684662956698998053

theorem tailTrace_8355654 : CollatzResearch.WordTrace tailWord_8355654 prefixEnd_8355654 4290466684662956698998053 := by
  unfold tailWord_8355654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9523616814715627029265063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203170492047266709957654677 9523616814715627029265063)
  ·
    refine ⟨14285425222073440543897595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9523616814715627029265063 14285425222073440543897595)
    ·
      refine ⟨21428137833110160815846393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14285425222073440543897595 21428137833110160815846393)
      ·
        refine ⟨16071103374832620611884795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21428137833110160815846393 16071103374832620611884795)
        ·
          refine ⟨24106655062248930917827193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16071103374832620611884795 24106655062248930917827193)
          ·
            refine ⟨18079991296686698188370395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24106655062248930917827193 18079991296686698188370395)
            ·
              refine ⟨27119986945030047282555593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18079991296686698188370395 27119986945030047282555593)
              ·
                refine ⟨20339990208772535461916695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27119986945030047282555593 20339990208772535461916695)
                ·
                  refine ⟨30509985313158803192875043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20339990208772535461916695 30509985313158803192875043)
                  ·
                    refine ⟨45764977969738204789312565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30509985313158803192875043 45764977969738204789312565)
                    ·
                      refine ⟨4290466684662956698998053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45764977969738204789312565 4290466684662956698998053)
                      ·
                        rfl

theorem cell23_8355654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_8355654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355654 prefixEnd_8355654 := by exact prefixLift 8355654
  have htrace : WordTrace (prefixWord ++ tailWord_8355654) baseStart_8355654 baseEnd_8355654 := by
    simpa [prefixWord, tailWord_8355654, baseEnd_8355654] using wordTrace_append hprefix tailTrace_8355654
  have hstable : (prefixWord ++ tailWord_8355654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355654).length < 2 ^ (prefixWord ++ tailWord_8355654).sum := by decide
  have hdescent : baseEnd_8355654 < baseStart_8355654 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355661 : List Nat := [1, 6, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_8355661 : Nat := 118140960795 + 8355661 * 2 ^ 59
def prefixEnd_8355661 : Nat := 4983230072969 + 3 ^ 40 * 8355661 * 2
def baseEnd_8355661 : Nat := 1430156759675846057203507

theorem tailTrace_8355661 : CollatzResearch.WordTrace tailWord_8355661 prefixEnd_8355661 1430156759675846057203507 := by
  unfold tailWord_8355661
  simp only [CollatzResearch.WordTrace]
  refine ⟨304755993381874705131986837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203170662254583136754657891 304755993381874705131986837)
  ·
    refine ⟨14285437189775376803061883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 304755993381874705131986837 14285437189775376803061883)
    ·
      refine ⟨21428155784663065204592825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14285437189775376803061883 21428155784663065204592825)
      ·
        refine ⟨16071116838497298903444619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21428155784663065204592825 16071116838497298903444619)
        ·
          refine ⟨24106675257745948355166929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16071116838497298903444619 24106675257745948355166929)
          ·
            refine ⟨18080006443309461266375197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24106675257745948355166929 18080006443309461266375197)
            ·
              refine ⟨6780002416241047974890699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18080006443309461266375197 6780002416241047974890699)
              ·
                refine ⟨10170003624361571962336049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6780002416241047974890699 10170003624361571962336049)
                ·
                  refine ⟨7627502718271178971752037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10170003624361571962336049 7627502718271178971752037)
                  ·
                    refine ⟨1430156759675846057203507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7627502718271178971752037 1430156759675846057203507)
                    ·
                      rfl

theorem cell23_8355661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_8355661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355661 prefixEnd_8355661 := by exact prefixLift 8355661
  have htrace : WordTrace (prefixWord ++ tailWord_8355661) baseStart_8355661 baseEnd_8355661 := by
    simpa [prefixWord, tailWord_8355661, baseEnd_8355661] using wordTrace_append hprefix tailTrace_8355661
  have hstable : (prefixWord ++ tailWord_8355661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355661).length < 2 ^ (prefixWord ++ tailWord_8355661).sum := by decide
  have hdescent : baseEnd_8355661 < baseStart_8355661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355797 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_8355797 : Nat := 118140960795 + 8355797 * 2 ^ 59
def prefixEnd_8355797 : Nat := 4983230072969 + 3 ^ 40 * 8355797 * 2
def baseEnd_8355797 : Nat := 4290540112396549639509895

theorem tailTrace_8355797 : CollatzResearch.WordTrace tailWord_8355797 prefixEnd_8355797 4290540112396549639509895 := by
  unfold tailWord_8355797
  simp only [CollatzResearch.WordTrace]
  refine ⟨304760953709382000358937645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203173969139588000239291763 304760953709382000358937645)
  ·
    refine ⟨114285357641018250134601617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304760953709382000358937645 114285357641018250134601617)
    ·
      refine ⟨85714018230763687600951213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114285357641018250134601617 85714018230763687600951213)
      ·
        refine ⟨32142756836536382850356705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85714018230763687600951213 32142756836536382850356705)
        ·
          refine ⟨24107067627402287137767529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32142756836536382850356705 24107067627402287137767529)
          ·
            refine ⟨18080300720551715353325647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24107067627402287137767529 18080300720551715353325647)
            ·
              refine ⟨27120451080827573029988471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18080300720551715353325647 27120451080827573029988471)
              ·
                refine ⟨40680676621241359544982707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27120451080827573029988471 40680676621241359544982707)
                ·
                  refine ⟨61021014931862039317474061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40680676621241359544982707 61021014931862039317474061)
                  ·
                    refine ⟨22882880599448264744052773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61021014931862039317474061 22882880599448264744052773)
                    ·
                      refine ⟨4290540112396549639509895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22882880599448264744052773 4290540112396549639509895)
                      ·
                        rfl

theorem cell23_8355797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_8355797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355797 prefixEnd_8355797 := by exact prefixLift 8355797
  have htrace : WordTrace (prefixWord ++ tailWord_8355797) baseStart_8355797 baseEnd_8355797 := by
    simpa [prefixWord, tailWord_8355797, baseEnd_8355797] using wordTrace_append hprefix tailTrace_8355797
  have hstable : (prefixWord ++ tailWord_8355797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355797).length < 2 ^ (prefixWord ++ tailWord_8355797).sum := by decide
  have hdescent : baseEnd_8355797 < baseStart_8355797 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355824 : List Nat := [2, 1, 1, 1, 3, 2, 4, 4, 1, 4]
def baseStart_8355824 : Nat := 118140960795 + 8355824 * 2 ^ 59
def prefixEnd_8355824 : Nat := 4983230072969 + 3 ^ 40 * 8355824 * 2
def baseEnd_8355824 : Nat := 1430184658791407011290757

theorem tailTrace_8355824 : CollatzResearch.WordTrace tailWord_8355824 prefixEnd_8355824 1430184658791407011290757 := by
  unfold tailWord_8355824
  simp only [CollatzResearch.WordTrace]
  refine ⟨152380969240142091985085263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203174625653522789313447017 152380969240142091985085263)
  ·
    refine ⟨228571453860213137977627895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152380969240142091985085263 228571453860213137977627895)
    ·
      refine ⟨342857180790319706966441843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228571453860213137977627895 342857180790319706966441843)
      ·
        refine ⟨514285771185479560449662765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342857180790319706966441843 514285771185479560449662765)
        ·
          refine ⟨192857164194554835168623537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 514285771185479560449662765 192857164194554835168623537)
          ·
            refine ⟨144642873145916126376467653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192857164194554835168623537 144642873145916126376467653)
            ·
              refine ⟨27120538714859273695587685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144642873145916126376467653 27120538714859273695587685)
              ·
                refine ⟨5085101009036113817922691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27120538714859273695587685 5085101009036113817922691)
                ·
                  refine ⟨7627651513554170726884037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5085101009036113817922691 7627651513554170726884037)
                  ·
                    refine ⟨1430184658791407011290757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7627651513554170726884037 1430184658791407011290757)
                    ·
                      rfl

theorem cell23_8355824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 1, 4].length) (baseStart_8355824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355824 prefixEnd_8355824 := by exact prefixLift 8355824
  have htrace : WordTrace (prefixWord ++ tailWord_8355824) baseStart_8355824 baseEnd_8355824 := by
    simpa [prefixWord, tailWord_8355824, baseEnd_8355824] using wordTrace_append hprefix tailTrace_8355824
  have hstable : (prefixWord ++ tailWord_8355824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355824).length < 2 ^ (prefixWord ++ tailWord_8355824).sum := by decide
  have hdescent : baseEnd_8355824 < baseStart_8355824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355887 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 2, 6, 2]
def baseStart_8355887 : Nat := 118140960795 + 8355887 * 2 ^ 59
def prefixEnd_8355887 : Nat := 4983230072969 + 3 ^ 40 * 8355887 * 2
def baseEnd_8355887 : Nat := 4290586325655454287384481

theorem tailTrace_8355887 : CollatzResearch.WordTrace tailWord_8355887 prefixEnd_8355887 4290586325655454287384481 := by
  unfold tailWord_8355887
  simp only [CollatzResearch.WordTrace]
  refine ⟨304764236279055945729713915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203176157519370630486475943 304764236279055945729713915)
  ·
    refine ⟨457146354418583918594570873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304764236279055945729713915 457146354418583918594570873)
    ·
      refine ⟨342859765813937938945928155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457146354418583918594570873 342859765813937938945928155)
      ·
        refine ⟨514289648720906908418892233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342859765813937938945928155 514289648720906908418892233)
        ·
          refine ⟨385717236540680181314169175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514289648720906908418892233 385717236540680181314169175)
          ·
            refine ⟨578575854811020271971253763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385717236540680181314169175 578575854811020271971253763)
            ·
              refine ⟨867863782216530407956880645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578575854811020271971253763 867863782216530407956880645)
              ·
                refine ⟨162724459165599451491915121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 867863782216530407956880645 162724459165599451491915121)
                ·
                  refine ⟨122043344374199588618936341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162724459165599451491915121 122043344374199588618936341)
                  ·
                    refine ⟨5720781767540605716512641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122043344374199588618936341 5720781767540605716512641)
                    ·
                      refine ⟨4290586325655454287384481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5720781767540605716512641 4290586325655454287384481)
                      ·
                        rfl

theorem cell23_8355887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 6, 2].length) (baseStart_8355887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355887 prefixEnd_8355887 := by exact prefixLift 8355887
  have htrace : WordTrace (prefixWord ++ tailWord_8355887) baseStart_8355887 baseEnd_8355887 := by
    simpa [prefixWord, tailWord_8355887, baseEnd_8355887] using wordTrace_append hprefix tailTrace_8355887
  have hstable : (prefixWord ++ tailWord_8355887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355887).length < 2 ^ (prefixWord ++ tailWord_8355887).sum := by decide
  have hdescent : baseEnd_8355887 < baseStart_8355887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355904 : List Nat := [2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 4]
def baseStart_8355904 : Nat := 118140960795 + 8355904 * 2 ^ 59
def prefixEnd_8355904 : Nat := 4983230072969 + 3 ^ 40 * 8355904 * 2
def baseEnd_8355904 : Nat := 4290595054826580720871903

theorem tailTrace_8355904 : CollatzResearch.WordTrace tailWord_8355904 prefixEnd_8355904 4290595054826580720871903 := by
  unfold tailWord_8355904
  simp only [CollatzResearch.WordTrace]
  refine ⟨152382428159997178816541383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203176570879996238422055177 152382428159997178816541383)
  ·
    refine ⟨228573642239995768224812075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152382428159997178816541383 228573642239995768224812075)
    ·
      refine ⟨342860463359993652337218113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228573642239995768224812075 342860463359993652337218113)
      ·
        refine ⟨257145347519995239252913585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342860463359993652337218113 257145347519995239252913585)
        ·
          refine ⟨192859010639996429439685189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257145347519995239252913585 192859010639996429439685189)
          ·
            refine ⟨36161064494999330519940973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192859010639996429439685189 36161064494999330519940973)
            ·
              refine ⟨13560399185624748944977865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36161064494999330519940973 13560399185624748944977865)
              ·
                refine ⟨10170299389218561708733399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13560399185624748944977865 10170299389218561708733399)
                ·
                  refine ⟨15255449083827842563100099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10170299389218561708733399 15255449083827842563100099)
                  ·
                    refine ⟨22883173625741763844650149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15255449083827842563100099 22883173625741763844650149)
                    ·
                      refine ⟨4290595054826580720871903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22883173625741763844650149 4290595054826580720871903)
                      ·
                        rfl

theorem cell23_8355904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_8355904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355904 prefixEnd_8355904 := by exact prefixLift 8355904
  have htrace : WordTrace (prefixWord ++ tailWord_8355904) baseStart_8355904 baseEnd_8355904 := by
    simpa [prefixWord, tailWord_8355904, baseEnd_8355904] using wordTrace_append hprefix tailTrace_8355904
  have hstable : (prefixWord ++ tailWord_8355904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355904).length < 2 ^ (prefixWord ++ tailWord_8355904).sum := by decide
  have hdescent : baseEnd_8355904 < baseStart_8355904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355937 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_8355937 : Nat := 118140960795 + 8355937 * 2 ^ 59
def prefixEnd_8355937 : Nat := 4983230072969 + 3 ^ 40 * 8355937 * 2
def baseEnd_8355937 : Nat := 4290611999688179091759251

theorem tailTrace_8355937 : CollatzResearch.WordTrace tailWord_8355937 prefixEnd_8355937 4290611999688179091759251 := by
  unfold tailWord_8355937
  simp only [CollatzResearch.WordTrace]
  refine ⟨304766059928874804269034065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203177373285916536179356043 304766059928874804269034065)
  ·
    refine ⟨228574544946656103201775549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304766059928874804269034065 228574544946656103201775549)
    ·
      refine ⟨85715454354996038700665831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228574544946656103201775549 85715454354996038700665831)
      ·
        refine ⟨128573181532494058050998747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85715454354996038700665831 128573181532494058050998747)
        ·
          refine ⟨192859772298741087076498121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128573181532494058050998747 192859772298741087076498121)
          ·
            refine ⟨144644829224055815307373591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192859772298741087076498121 144644829224055815307373591)
            ·
              refine ⟨216967243836083722961060387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144644829224055815307373591 216967243836083722961060387)
              ·
                refine ⟨325450865754125584441590581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216967243836083722961060387 325450865754125584441590581)
                ·
                  refine ⟨30511018664449273541399117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 325450865754125584441590581 30511018664449273541399117)
                  ·
                    refine ⟨11441631999168477578024669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30511018664449273541399117 11441631999168477578024669)
                    ·
                      refine ⟨4290611999688179091759251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11441631999168477578024669 4290611999688179091759251)
                      ·
                        rfl

theorem cell23_8355937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_8355937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355937 prefixEnd_8355937 := by exact prefixLift 8355937
  have htrace : WordTrace (prefixWord ++ tailWord_8355937) baseStart_8355937 baseEnd_8355937 := by
    simpa [prefixWord, tailWord_8355937, baseEnd_8355937] using wordTrace_append hprefix tailTrace_8355937
  have hstable : (prefixWord ++ tailWord_8355937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355937).length < 2 ^ (prefixWord ++ tailWord_8355937).sum := by decide
  have hdescent : baseEnd_8355937 < baseStart_8355937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8355954 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_8355954 : Nat := 118140960795 + 8355954 * 2 ^ 59
def prefixEnd_8355954 : Nat := 4983230072969 + 3 ^ 40 * 8355954 * 2
def baseEnd_8355954 : Nat := 4290620728859305525246673

theorem tailTrace_8355954 : CollatzResearch.WordTrace tailWord_8355954 prefixEnd_8355954 4290620728859305525246673 := by
  unfold tailWord_8355954
  simp only [CollatzResearch.WordTrace]
  refine ⟨76191669992453304043100729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203177786646542144114935277 76191669992453304043100729)
  ·
    refine ⟨57143752494339978032325547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76191669992453304043100729 57143752494339978032325547)
    ·
      refine ⟨85715628741509967048488321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57143752494339978032325547 85715628741509967048488321)
      ·
        refine ⟨64286721556132475286366241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85715628741509967048488321 64286721556132475286366241)
        ·
          refine ⟨48215041167099356464774681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64286721556132475286366241 48215041167099356464774681)
          ·
            refine ⟨36161280875324517348581011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48215041167099356464774681 36161280875324517348581011)
            ·
              refine ⟨54241921312986776022871517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36161280875324517348581011 54241921312986776022871517)
              ·
                refine ⟨20340720492370041008576819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54241921312986776022871517 20340720492370041008576819)
                ·
                  refine ⟨30511080738555061512865229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20340720492370041008576819 30511080738555061512865229)
                  ·
                    refine ⟨11441655276958148067324461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30511080738555061512865229 11441655276958148067324461)
                    ·
                      refine ⟨4290620728859305525246673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11441655276958148067324461 4290620728859305525246673)
                      ·
                        rfl

theorem cell23_8355954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_8355954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8355954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8355954 prefixEnd_8355954 := by exact prefixLift 8355954
  have htrace : WordTrace (prefixWord ++ tailWord_8355954) baseStart_8355954 baseEnd_8355954 := by
    simpa [prefixWord, tailWord_8355954, baseEnd_8355954] using wordTrace_append hprefix tailTrace_8355954
  have hstable : (prefixWord ++ tailWord_8355954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8355954).length < 2 ^ (prefixWord ++ tailWord_8355954).sum := by decide
  have hdescent : baseEnd_8355954 < baseStart_8355954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8355954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356057 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 7]
def baseStart_8356057 : Nat := 118140960795 + 8356057 * 2 ^ 59
def prefixEnd_8356057 : Nat := 4983230072969 + 3 ^ 40 * 8356057 * 2
def baseEnd_8356057 : Nat := 4290673617366718622258699

theorem tailTrace_8356057 : CollatzResearch.WordTrace tailWord_8356057 prefixEnd_8356057 4290673617366718622258699 := by
  unfold tailWord_8356057
  simp only [CollatzResearch.WordTrace]
  refine ⟨304770436688440064763402425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203180291125626709842268283 304770436688440064763402425)
  ·
    refine ⟨228577827516330048572551819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304770436688440064763402425 228577827516330048572551819)
    ·
      refine ⟨342866741274495072858827729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228577827516330048572551819 342866741274495072858827729)
      ·
        refine ⟨257150055955871304644120797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342866741274495072858827729 257150055955871304644120797)
        ·
          refine ⟨96431270983451739241545299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257150055955871304644120797 96431270983451739241545299)
          ·
            refine ⟨144646906475177608862317949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96431270983451739241545299 144646906475177608862317949)
            ·
              refine ⟨54242589928191603323369231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144646906475177608862317949 54242589928191603323369231)
              ·
                refine ⟨81363884892287404985053847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54242589928191603323369231 81363884892287404985053847)
                ·
                  refine ⟨122045827338431107477580771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81363884892287404985053847 122045827338431107477580771)
                  ·
                    refine ⟨183068741007646661216371157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122045827338431107477580771 183068741007646661216371157)
                    ·
                      refine ⟨4290673617366718622258699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183068741007646661216371157 4290673617366718622258699)
                      ·
                        rfl

theorem cell23_8356057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_8356057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356057 prefixEnd_8356057 := by exact prefixLift 8356057
  have htrace : WordTrace (prefixWord ++ tailWord_8356057) baseStart_8356057 baseEnd_8356057 := by
    simpa [prefixWord, tailWord_8356057, baseEnd_8356057] using wordTrace_append hprefix tailTrace_8356057
  have hstable : (prefixWord ++ tailWord_8356057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356057).length < 2 ^ (prefixWord ++ tailWord_8356057).sum := by decide
  have hdescent : baseEnd_8356057 < baseStart_8356057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356066 : List Nat := [3, 3, 4, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_8356066 : Nat := 118140960795 + 8356066 * 2 ^ 59
def prefixEnd_8356066 : Nat := 4983230072969 + 3 ^ 40 * 8356066 * 2
def baseEnd_8356066 : Nat := 4290678238692609087046159

theorem tailTrace_8356066 : CollatzResearch.WordTrace tailWord_8356066 prefixEnd_8356066 4290678238692609087046159 := by
  unfold tailWord_8356066
  simp only [CollatzResearch.WordTrace]
  refine ⟨76192691236351864825120013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203180509963604972866986701 76192691236351864825120013)
  ·
    refine ⟨28572259213631949309420005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76192691236351864825120013 28572259213631949309420005)
    ·
      refine ⟨5357298602555990495516251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28572259213631949309420005 5357298602555990495516251)
      ·
        refine ⟨8035947903833985743274377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5357298602555990495516251 8035947903833985743274377)
        ·
          refine ⟨6026960927875489307455783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8035947903833985743274377 6026960927875489307455783)
          ·
            refine ⟨9040441391813233961183675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6026960927875489307455783 9040441391813233961183675)
            ·
              refine ⟨13560662087719850941775513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9040441391813233961183675 13560662087719850941775513)
              ·
                refine ⟨10170496565789888206331635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13560662087719850941775513 10170496565789888206331635)
                ·
                  refine ⟨15255744848684832309497453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10170496565789888206331635 15255744848684832309497453)
                  ·
                    refine ⟨5720904318256812116061545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15255744848684832309497453 5720904318256812116061545)
                    ·
                      refine ⟨4290678238692609087046159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5720904318256812116061545 4290678238692609087046159)
                      ·
                        rfl

theorem cell23_8356066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_8356066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356066 prefixEnd_8356066 := by exact prefixLift 8356066
  have htrace : WordTrace (prefixWord ++ tailWord_8356066) baseStart_8356066 baseEnd_8356066 := by
    simpa [prefixWord, tailWord_8356066, baseEnd_8356066] using wordTrace_append hprefix tailTrace_8356066
  have hstable : (prefixWord ++ tailWord_8356066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356066).length < 2 ^ (prefixWord ++ tailWord_8356066).sum := by decide
  have hdescent : baseEnd_8356066 < baseStart_8356066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356087 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_8356087 : Nat := 118140960795 + 8356087 * 2 ^ 59
def prefixEnd_8356087 : Nat := 4983230072969 + 3 ^ 40 * 8356087 * 2
def baseEnd_8356087 : Nat := 4290689021786353504883561

theorem tailTrace_8356087 : CollatzResearch.WordTrace tailWord_8356087 prefixEnd_8356087 4290689021786353504883561 := by
  unfold tailWord_8356087
  simp only [CollatzResearch.WordTrace]
  refine ⟨304771530878331379886994515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203181020585554253257996343 304771530878331379886994515)
  ·
    refine ⟨457157296317497069830491773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304771530878331379886994515 457157296317497069830491773)
    ·
      refine ⟨171433986119061401186434415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457157296317497069830491773 171433986119061401186434415)
      ·
        refine ⟨257150979178592101779651623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171433986119061401186434415 257150979178592101779651623)
        ·
          refine ⟨385726468767888152669477435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257150979178592101779651623 385726468767888152669477435)
          ·
            refine ⟨578589703151832229004216153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385726468767888152669477435 578589703151832229004216153)
            ·
              refine ⟨433942277363874171753162115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578589703151832229004216153 433942277363874171753162115)
              ·
                refine ⟨650913416045811257629743173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433942277363874171753162115 650913416045811257629743173)
                ·
                  refine ⟨122046265508589610805576845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 650913416045811257629743173 122046265508589610805576845)
                  ·
                    refine ⟨45767349565721104052091317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122046265508589610805576845 45767349565721104052091317)
                    ·
                      refine ⟨4290689021786353504883561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45767349565721104052091317 4290689021786353504883561)
                      ·
                        rfl

theorem cell23_8356087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_8356087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356087 prefixEnd_8356087 := by exact prefixLift 8356087
  have htrace : WordTrace (prefixWord ++ tailWord_8356087) baseStart_8356087 baseEnd_8356087 := by
    simpa [prefixWord, tailWord_8356087, baseEnd_8356087] using wordTrace_append hprefix tailTrace_8356087
  have hstable : (prefixWord ++ tailWord_8356087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356087).length < 2 ^ (prefixWord ++ tailWord_8356087).sum := by decide
  have hdescent : baseEnd_8356087 < baseStart_8356087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356135 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_8356135 : Nat := 118140960795 + 8356135 * 2 ^ 59
def prefixEnd_8356135 : Nat := 4983230072969 + 3 ^ 40 * 8356135 * 2
def baseEnd_8356135 : Nat := 4290713668857769317083341

theorem tailTrace_8356135 : CollatzResearch.WordTrace tailWord_8356135 prefixEnd_8356135 4290713668857769317083341 := by
  unfold tailWord_8356135
  simp only [CollatzResearch.WordTrace]
  refine ⟨304773281582157484084741859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203182187721438322723161239 304773281582157484084741859)
  ·
    refine ⟨457159922373236226127112789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304773281582157484084741859 457159922373236226127112789)
    ·
      refine ⟨5357342840311362024927103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 457159922373236226127112789 5357342840311362024927103)
      ·
        refine ⟨8036014260467043037390655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5357342840311362024927103 8036014260467043037390655)
        ·
          refine ⟨12054021390700564556085983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8036014260467043037390655 12054021390700564556085983)
          ·
            refine ⟨18081032086050846834128975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12054021390700564556085983 18081032086050846834128975)
            ·
              refine ⟨27121548129076270251193463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18081032086050846834128975 27121548129076270251193463)
              ·
                refine ⟨40682322193614405376790195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27121548129076270251193463 40682322193614405376790195)
                ·
                  refine ⟨61023483290421608065185293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40682322193614405376790195 61023483290421608065185293)
                  ·
                    refine ⟨22883806233908103024444485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61023483290421608065185293 22883806233908103024444485)
                    ·
                      refine ⟨4290713668857769317083341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22883806233908103024444485 4290713668857769317083341)
                      ·
                        rfl

theorem cell23_8356135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_8356135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356135 prefixEnd_8356135 := by exact prefixLift 8356135
  have htrace : WordTrace (prefixWord ++ tailWord_8356135) baseStart_8356135 baseEnd_8356135 := by
    simpa [prefixWord, tailWord_8356135, baseEnd_8356135] using wordTrace_append hprefix tailTrace_8356135
  have hstable : (prefixWord ++ tailWord_8356135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356135).length < 2 ^ (prefixWord ++ tailWord_8356135).sum := by decide
  have hdescent : baseEnd_8356135 < baseStart_8356135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356138 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_8356138 : Nat := 118140960795 + 8356138 * 2 ^ 59
def prefixEnd_8356138 : Nat := 4983230072969 + 3 ^ 40 * 8356138 * 2
def baseEnd_8356138 : Nat := 4290715209299732805345827

theorem tailTrace_8356138 : CollatzResearch.WordTrace tailWord_8356138 prefixEnd_8356138 4290715209299732805345827 := by
  unfold tailWord_8356138
  simp only [CollatzResearch.WordTrace]
  refine ⟨76193347750286653899275267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203182260667431077064734045 76193347750286653899275267)
  ·
    refine ⟨114290021625429980848912901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76193347750286653899275267 114290021625429980848912901)
    ·
      refine ⟨21429379054768121409171169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114290021625429980848912901 21429379054768121409171169)
      ·
        refine ⟨16072034291076091056878377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21429379054768121409171169 16072034291076091056878377)
        ·
          refine ⟨12054025718307068292658783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16072034291076091056878377 12054025718307068292658783)
          ·
            refine ⟨18081038577460602438988175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12054025718307068292658783 18081038577460602438988175)
            ·
              refine ⟨27121557866190903658482263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18081038577460602438988175 27121557866190903658482263)
              ·
                refine ⟨40682336799286355487723395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27121557866190903658482263 40682336799286355487723395)
                ·
                  refine ⟨61023505198929533231585093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40682336799286355487723395 61023505198929533231585093)
                  ·
                    refine ⟨11441907224799287480922205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61023505198929533231585093 11441907224799287480922205)
                    ·
                      refine ⟨4290715209299732805345827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11441907224799287480922205 4290715209299732805345827)
                      ·
                        rfl

theorem cell23_8356138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_8356138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356138 prefixEnd_8356138 := by exact prefixLift 8356138
  have htrace : WordTrace (prefixWord ++ tailWord_8356138) baseStart_8356138 baseEnd_8356138 := by
    simpa [prefixWord, tailWord_8356138, baseEnd_8356138] using wordTrace_append hprefix tailTrace_8356138
  have hstable : (prefixWord ++ tailWord_8356138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356138).length < 2 ^ (prefixWord ++ tailWord_8356138).sum := by decide
  have hdescent : baseEnd_8356138 < baseStart_8356138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356145 : List Nat := [1, 2, 2, 3, 4, 1, 2, 3, 1, 4]
def baseStart_8356145 : Nat := 118140960795 + 8356145 * 2 ^ 59
def prefixEnd_8356145 : Nat := 4983230072969 + 3 ^ 40 * 8356145 * 2
def baseEnd_8356145 : Nat := 1430239601221438092652765

theorem tailTrace_8356145 : CollatzResearch.WordTrace tailWord_8356145 prefixEnd_8356145 1430239601221438092652765 := by
  unfold tailWord_8356145
  simp only [CollatzResearch.WordTrace]
  refine ⟨304773646312121255792605889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203182430874747503861737259 304773646312121255792605889)
  ·
    refine ⟨228580234734090941844454417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304773646312121255792605889 228580234734090941844454417)
    ·
      refine ⟨171435176050568206383340813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228580234734090941844454417 171435176050568206383340813)
      ·
        refine ⟨64288191018963077393752805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171435176050568206383340813 64288191018963077393752805)
        ·
          refine ⟨12054035816055577011328651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64288191018963077393752805 12054035816055577011328651)
          ·
            refine ⟨18081053724083365516992977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12054035816055577011328651 18081053724083365516992977)
            ·
              refine ⟨13560790293062524137744733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18081053724083365516992977 13560790293062524137744733)
              ·
                refine ⟨5085296359898446551654275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13560790293062524137744733 5085296359898446551654275)
                ·
                  refine ⟨7627944539847669827481413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5085296359898446551654275 7627944539847669827481413)
                  ·
                    refine ⟨1430239601221438092652765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7627944539847669827481413 1430239601221438092652765)
                    ·
                      rfl

theorem cell23_8356145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_8356145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356145 prefixEnd_8356145 := by exact prefixLift 8356145
  have htrace : WordTrace (prefixWord ++ tailWord_8356145) baseStart_8356145 baseEnd_8356145 := by
    simpa [prefixWord, tailWord_8356145, baseEnd_8356145] using wordTrace_append hprefix tailTrace_8356145
  have hstable : (prefixWord ++ tailWord_8356145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356145).length < 2 ^ (prefixWord ++ tailWord_8356145).sum := by decide
  have hdescent : baseEnd_8356145 < baseStart_8356145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356158 : List Nat := [4, 2, 1, 2, 1, 4, 1, 2, 6]
def baseStart_8356158 : Nat := 118140960795 + 8356158 * 2 ^ 59
def prefixEnd_8356158 : Nat := 4983230072969 + 3 ^ 40 * 8356158 * 2
def baseEnd_8356158 : Nat := 476747275434758080788415

theorem tailTrace_8356158 : CollatzResearch.WordTrace tailWord_8356158 prefixEnd_8356158 476747275434758080788415 := by
  unfold tailWord_8356158
  simp only [CollatzResearch.WordTrace]
  refine ⟨38096765057634269876603641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203182746974049439341886085 38096765057634269876603641)
  ·
    refine ⟨28572573793225702407452731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38096765057634269876603641 28572573793225702407452731)
    ·
      refine ⟨42858860689838553611179097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28572573793225702407452731 42858860689838553611179097)
      ·
        refine ⟨32144145517378915208384323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42858860689838553611179097 32144145517378915208384323)
        ·
          refine ⟨48216218276068372812576485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32144145517378915208384323 48216218276068372812576485)
          ·
            refine ⟨9040540926762819902358091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48216218276068372812576485 9040540926762819902358091)
            ·
              refine ⟨13560811390144229853537137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9040540926762819902358091 13560811390144229853537137)
              ·
                refine ⟨10170608542608172390152853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13560811390144229853537137 10170608542608172390152853)
                ·
                  refine ⟨476747275434758080788415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10170608542608172390152853 476747275434758080788415)
                  ·
                    rfl

theorem cell23_8356158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_8356158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356158 prefixEnd_8356158 := by exact prefixLift 8356158
  have htrace : WordTrace (prefixWord ++ tailWord_8356158) baseStart_8356158 baseEnd_8356158 := by
    simpa [prefixWord, tailWord_8356158, baseEnd_8356158] using wordTrace_append hprefix tailTrace_8356158
  have hstable : (prefixWord ++ tailWord_8356158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356158).length < 2 ^ (prefixWord ++ tailWord_8356158).sum := by decide
  have hdescent : baseEnd_8356158 < baseStart_8356158 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356174 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_8356174 : Nat := 118140960795 + 8356174 * 2 ^ 59
def prefixEnd_8356174 : Nat := 4983230072969 + 3 ^ 40 * 8356174 * 2
def baseEnd_8356174 : Nat := 4290733694603294664495661

theorem tailTrace_8356174 : CollatzResearch.WordTrace tailWord_8356174 prefixEnd_8356174 4290733694603294664495661 := by
  unfold tailWord_8356174
  simp only [CollatzResearch.WordTrace]
  refine ⟨38096838003627024218176447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203183136019344129163607717 38096838003627024218176447)
  ·
    refine ⟨57145257005440536327264671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38096838003627024218176447 57145257005440536327264671)
    ·
      refine ⟨85717885508160804490897007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57145257005440536327264671 85717885508160804490897007)
      ·
        refine ⟨128576828262241206736345511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85717885508160804490897007 128576828262241206736345511)
        ·
          refine ⟨192865242393361810104518267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128576828262241206736345511 192865242393361810104518267)
          ·
            refine ⟨289297863590042715156777401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192865242393361810104518267 289297863590042715156777401)
            ·
              refine ⟨216973397692532036367583051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289297863590042715156777401 216973397692532036367583051)
              ·
                refine ⟨325460096538798054551374577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216973397692532036367583051 325460096538798054551374577)
                ·
                  refine ⟨244095072404098540913530933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325460096538798054551374577 244095072404098540913530933)
                  ·
                    refine ⟨22883913037884238210643525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 244095072404098540913530933 22883913037884238210643525)
                    ·
                      refine ⟨4290733694603294664495661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22883913037884238210643525 4290733694603294664495661)
                      ·
                        rfl

theorem cell23_8356174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_8356174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356174 prefixEnd_8356174 := by exact prefixLift 8356174
  have htrace : WordTrace (prefixWord ++ tailWord_8356174) baseStart_8356174 baseEnd_8356174 := by
    simpa [prefixWord, tailWord_8356174, baseEnd_8356174] using wordTrace_append hprefix tailTrace_8356174
  have hstable : (prefixWord ++ tailWord_8356174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356174).length < 2 ^ (prefixWord ++ tailWord_8356174).sum := by decide
  have hdescent : baseEnd_8356174 < baseStart_8356174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356184 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 1, 6]
def baseStart_8356184 : Nat := 118140960795 + 8356184 * 2 ^ 59
def prefixEnd_8356184 : Nat := 4983230072969 + 3 ^ 40 * 8356184 * 2
def baseEnd_8356184 : Nat := 1430246276469946541790205

theorem tailTrace_8356184 : CollatzResearch.WordTrace tailWord_8356184 prefixEnd_8356184 1430246276469946541790205 := by
  unfold tailWord_8356184
  simp only [CollatzResearch.WordTrace]
  refine ⟨152387534379489982726637803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203183379172653310302183737 152387534379489982726637803)
  ·
    refine ⟨228581301569234974089956705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152387534379489982726637803 228581301569234974089956705)
    ·
      refine ⟨171435976176926230567467529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228581301569234974089956705 171435976176926230567467529)
      ·
        refine ⟨128576982132694672925600647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171435976176926230567467529 128576982132694672925600647)
        ·
          refine ⟨192865473199042009388400971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128576982132694672925600647 192865473199042009388400971)
          ·
            refine ⟨289298209798563014082601457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192865473199042009388400971 289298209798563014082601457)
            ·
              refine ⟨216973657348922260561951093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289298209798563014082601457 216973657348922260561951093)
              ·
                refine ⟨20341280376461461927682915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216973657348922260561951093 20341280376461461927682915)
                ·
                  refine ⟨30511920564692192891524373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20341280376461461927682915 30511920564692192891524373)
                  ·
                    refine ⟨1430246276469946541790205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30511920564692192891524373 1430246276469946541790205)
                    ·
                      rfl

theorem cell23_8356184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_8356184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356184 prefixEnd_8356184 := by exact prefixLift 8356184
  have htrace : WordTrace (prefixWord ++ tailWord_8356184) baseStart_8356184 baseEnd_8356184 := by
    simpa [prefixWord, tailWord_8356184, baseEnd_8356184] using wordTrace_append hprefix tailTrace_8356184
  have hstable : (prefixWord ++ tailWord_8356184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356184).length < 2 ^ (prefixWord ++ tailWord_8356184).sum := by decide
  have hdescent : baseEnd_8356184 < baseStart_8356184 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356191 : List Nat := [1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 4]
def baseStart_8356191 : Nat := 118140960795 + 8356191 * 2 ^ 59
def prefixEnd_8356191 : Nat := 4983230072969 + 3 ^ 40 * 8356191 * 2
def baseEnd_8356191 : Nat := 4290742423774421097983083

theorem tailTrace_8356191 : CollatzResearch.WordTrace tailWord_8356191 prefixEnd_8356191 4290742423774421097983083 := by
  unfold tailWord_8356191
  simp only [CollatzResearch.WordTrace]
  refine ⟨304775324069954605648780427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203183549379969737099186951 304775324069954605648780427)
  ·
    refine ⟨457162986104931908473170641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304775324069954605648780427 457162986104931908473170641)
    ·
      refine ⟨342872239578698931354877981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457162986104931908473170641 342872239578698931354877981)
      ·
        refine ⟨128577089842012099258079243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342872239578698931354877981 128577089842012099258079243)
        ·
          refine ⟨192865634763018148887118865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128577089842012099258079243 192865634763018148887118865)
          ·
            refine ⟨144649226072263611665339149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192865634763018148887118865 144649226072263611665339149)
            ·
              refine ⟨54243459777098854374502181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144649226072263611665339149 54243459777098854374502181)
              ·
                refine ⟨10170648708206035195219159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54243459777098854374502181 10170648708206035195219159)
                ·
                  refine ⟨15255973062309052792828739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10170648708206035195219159 15255973062309052792828739)
                  ·
                    refine ⟨22883959593463579189243109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15255973062309052792828739 22883959593463579189243109)
                    ·
                      refine ⟨4290742423774421097983083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22883959593463579189243109 4290742423774421097983083)
                      ·
                        rfl

theorem cell23_8356191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_8356191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356191 prefixEnd_8356191 := by exact prefixLift 8356191
  have htrace : WordTrace (prefixWord ++ tailWord_8356191) baseStart_8356191 baseEnd_8356191 := by
    simpa [prefixWord, tailWord_8356191, baseEnd_8356191] using wordTrace_append hprefix tailTrace_8356191
  have hstable : (prefixWord ++ tailWord_8356191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356191).length < 2 ^ (prefixWord ++ tailWord_8356191).sum := by decide
  have hdescent : baseEnd_8356191 < baseStart_8356191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356202 : List Nat := [3, 1, 3, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_8356202 : Nat := 118140960795 + 8356202 * 2 ^ 59
def prefixEnd_8356202 : Nat := 4983230072969 + 3 ^ 40 * 8356202 * 2
def baseEnd_8356202 : Nat := 4290748072061620554945533

theorem tailTrace_8356202 : CollatzResearch.WordTrace tailWord_8356202 prefixEnd_8356202 4290748072061620554945533 := by
  unfold tailWord_8356202
  simp only [CollatzResearch.WordTrace]
  refine ⟨76193931318228688631857715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203183816848609836351620573 76193931318228688631857715)
  ·
    refine ⟨114290896977343032947786573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76193931318228688631857715 114290896977343032947786573)
    ·
      refine ⟨42859086366503637355419965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114290896977343032947786573 42859086366503637355419965)
      ·
        refine ⟨16072157387438864008282487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42859086366503637355419965 16072157387438864008282487)
        ·
          refine ⟨24108236081158296012423731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16072157387438864008282487 24108236081158296012423731)
          ·
            refine ⟨36162354121737444018635597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24108236081158296012423731 36162354121737444018635597)
            ·
              refine ⟨13560882795651541506988349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36162354121737444018635597 13560882795651541506988349)
              ·
                refine ⟨5085331048369328065120631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13560882795651541506988349 5085331048369328065120631)
                ·
                  refine ⟨7627996572553992097680947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5085331048369328065120631 7627996572553992097680947)
                  ·
                    refine ⟨11441994858830988146521421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7627996572553992097680947 11441994858830988146521421)
                    ·
                      refine ⟨4290748072061620554945533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11441994858830988146521421 4290748072061620554945533)
                      ·
                        rfl

theorem cell23_8356202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_8356202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356202 prefixEnd_8356202 := by exact prefixLift 8356202
  have htrace : WordTrace (prefixWord ++ tailWord_8356202) baseStart_8356202 baseEnd_8356202 := by
    simpa [prefixWord, tailWord_8356202, baseEnd_8356202] using wordTrace_append hprefix tailTrace_8356202
  have hstable : (prefixWord ++ tailWord_8356202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356202).length < 2 ^ (prefixWord ++ tailWord_8356202).sum := by decide
  have hdescent : baseEnd_8356202 < baseStart_8356202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356235 : List Nat := [1, 1, 1, 1, 4, 6, 2, 1, 2, 4]
def baseStart_8356235 : Nat := 118140960795 + 8356235 * 2 ^ 59
def prefixEnd_8356235 : Nat := 4983230072969 + 3 ^ 40 * 8356235 * 2
def baseEnd_8356235 : Nat := 1430255005641072975277627

theorem tailTrace_8356235 : CollatzResearch.WordTrace tailWord_8356235 prefixEnd_8356235 1430255005641072975277627 := by
  unfold tailWord_8356235
  simp only [CollatzResearch.WordTrace]
  refine ⟨304776928881795201163382159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203184619254530134108921439 304776928881795201163382159)
  ·
    refine ⟨457165393322692801745073239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304776928881795201163382159 457165393322692801745073239)
    ·
      refine ⟨685748089984039202617609859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457165393322692801745073239 685748089984039202617609859)
      ·
        refine ⟨1028622134976058803926414789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685748089984039202617609859 1028622134976058803926414789)
        ·
          refine ⟨192866650308011025736202773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1028622134976058803926414789 192866650308011025736202773)
          ·
            refine ⟨9040624233188016831384505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192866650308011025736202773 9040624233188016831384505)
            ·
              refine ⟨6780468174891012623538379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9040624233188016831384505 6780468174891012623538379)
              ·
                refine ⟨10170702262336518935307569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6780468174891012623538379 10170702262336518935307569)
                ·
                  refine ⟨7628026696752389201480677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10170702262336518935307569 7628026696752389201480677)
                  ·
                    refine ⟨1430255005641072975277627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7628026696752389201480677 1430255005641072975277627)
                    ·
                      rfl

theorem cell23_8356235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 2, 4].length) (baseStart_8356235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356235 prefixEnd_8356235 := by exact prefixLift 8356235
  have htrace : WordTrace (prefixWord ++ tailWord_8356235) baseStart_8356235 baseEnd_8356235 := by
    simpa [prefixWord, tailWord_8356235, baseEnd_8356235] using wordTrace_append hprefix tailTrace_8356235
  have hstable : (prefixWord ++ tailWord_8356235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356235).length < 2 ^ (prefixWord ++ tailWord_8356235).sum := by decide
  have hdescent : baseEnd_8356235 < baseStart_8356235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356246 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_8356246 : Nat := 118140960795 + 8356246 * 2 ^ 59
def prefixEnd_8356246 : Nat := 4983230072969 + 3 ^ 40 * 8356246 * 2
def baseEnd_8356246 : Nat := 4290770665210418382795331

theorem tailTrace_8356246 : CollatzResearch.WordTrace tailWord_8356246 prefixEnd_8356246 4290770665210418382795331 := by
  unfold tailWord_8356246
  simp only [CollatzResearch.WordTrace]
  refine ⟨19048583130297209377627037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203184886723170233361355061 19048583130297209377627037)
  ·
    refine ⟨7143218673861453516610139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19048583130297209377627037 7143218673861453516610139)
    ·
      refine ⟨10714828010792180274915209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7143218673861453516610139 10714828010792180274915209)
      ·
        refine ⟨8036121008094135206186407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10714828010792180274915209 8036121008094135206186407)
        ·
          refine ⟨12054181512141202809279611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8036121008094135206186407 12054181512141202809279611)
          ·
            refine ⟨18081272268211804213919417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12054181512141202809279611 18081272268211804213919417)
            ·
              refine ⟨13560954201158853160439563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18081272268211804213919417 13560954201158853160439563)
              ·
                refine ⟨20341431301738279740659345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13560954201158853160439563 20341431301738279740659345)
                ·
                  refine ⟨15256073476303709805494509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20341431301738279740659345 15256073476303709805494509)
                  ·
                    refine ⟨5721027553613891177060441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15256073476303709805494509 5721027553613891177060441)
                    ·
                      refine ⟨4290770665210418382795331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5721027553613891177060441 4290770665210418382795331)
                      ·
                        rfl

theorem cell23_8356246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_8356246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356246 prefixEnd_8356246 := by exact prefixLift 8356246
  have htrace : WordTrace (prefixWord ++ tailWord_8356246) baseStart_8356246 baseEnd_8356246 := by
    simpa [prefixWord, tailWord_8356246, baseEnd_8356246] using wordTrace_append hprefix tailTrace_8356246
  have hstable : (prefixWord ++ tailWord_8356246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356246).length < 2 ^ (prefixWord ++ tailWord_8356246).sum := by decide
  have hdescent : baseEnd_8356246 < baseStart_8356246 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356258 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_8356258 : Nat := 118140960795 + 8356258 * 2 ^ 59
def prefixEnd_8356258 : Nat := 4983230072969 + 3 ^ 40 * 8356258 * 2
def baseEnd_8356258 : Nat := 4290776826978272335845275

theorem tailTrace_8356258 : CollatzResearch.WordTrace tailWord_8356258 prefixEnd_8356258 4290776826978272335845275 := by
  unfold tailWord_8356258
  simp only [CollatzResearch.WordTrace]
  refine ⟨76194441940177969022867357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203185178507141250727646285 76194441940177969022867357)
  ·
    refine ⟨28572915727566738383575259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76194441940177969022867357 28572915727566738383575259)
    ·
      refine ⟨42859373591350107575362889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28572915727566738383575259 42859373591350107575362889)
      ·
        refine ⟨32144530193512580681522167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42859373591350107575362889 32144530193512580681522167)
        ·
          refine ⟨48216795290268871022283251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32144530193512580681522167 48216795290268871022283251)
          ·
            refine ⟨72325192935403306533424877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48216795290268871022283251 72325192935403306533424877)
            ·
              refine ⟨27121947350776239950034329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72325192935403306533424877 27121947350776239950034329)
              ·
                refine ⟨20341460513082179962525747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27121947350776239950034329 20341460513082179962525747)
                ·
                  refine ⟨30512190769623269943788621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20341460513082179962525747 30512190769623269943788621)
                  ·
                    refine ⟨11442071538608726228920733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30512190769623269943788621 11442071538608726228920733)
                    ·
                      refine ⟨4290776826978272335845275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11442071538608726228920733 4290776826978272335845275)
                      ·
                        rfl

theorem cell23_8356258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_8356258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356258 prefixEnd_8356258 := by exact prefixLift 8356258
  have htrace : WordTrace (prefixWord ++ tailWord_8356258) baseStart_8356258 baseEnd_8356258 := by
    simpa [prefixWord, tailWord_8356258, baseEnd_8356258] using wordTrace_append hprefix tailTrace_8356258
  have hstable : (prefixWord ++ tailWord_8356258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356258).length < 2 ^ (prefixWord ++ tailWord_8356258).sum := by decide
  have hdescent : baseEnd_8356258 < baseStart_8356258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356281 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 2, 3, 4]
def baseStart_8356281 : Nat := 118140960795 + 8356281 * 2 ^ 59
def prefixEnd_8356281 : Nat := 4983230072969 + 3 ^ 40 * 8356281 * 2
def baseEnd_8356281 : Nat := 4290788637033325745857669

theorem tailTrace_8356281 : CollatzResearch.WordTrace tailWord_8356281 prefixEnd_8356281 4290788637033325745857669 := by
  unfold tailWord_8356281
  simp only [CollatzResearch.WordTrace]
  refine ⟨304778606639628551019556697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203185737759752367346371131 304778606639628551019556697)
  ·
    refine ⟨228583954979721413264667523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304778606639628551019556697 228583954979721413264667523)
    ·
      refine ⟨342875932469582119897001285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228583954979721413264667523 342875932469582119897001285)
      ·
        refine ⟨64289237338046647480687741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342875932469582119897001285 64289237338046647480687741)
        ·
          refine ⟨24108464001767492805257903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64289237338046647480687741 24108464001767492805257903)
          ·
            refine ⟨36162696002651239207886855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24108464001767492805257903 36162696002651239207886855)
            ·
              refine ⟨54244044003976858811830283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36162696002651239207886855 54244044003976858811830283)
              ·
                refine ⟨81366066005965288217745425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54244044003976858811830283 81366066005965288217745425)
                ·
                  refine ⟨61024549504473966163309069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81366066005965288217745425 61024549504473966163309069)
                  ·
                    refine ⟨22884206064177737311240901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61024549504473966163309069 22884206064177737311240901)
                    ·
                      refine ⟨4290788637033325745857669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22884206064177737311240901 4290788637033325745857669)
                      ·
                        rfl

theorem cell23_8356281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_8356281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356281 prefixEnd_8356281 := by exact prefixLift 8356281
  have htrace : WordTrace (prefixWord ++ tailWord_8356281) baseStart_8356281 baseEnd_8356281 := by
    simpa [prefixWord, tailWord_8356281, baseEnd_8356281] using wordTrace_append hprefix tailTrace_8356281
  have hstable : (prefixWord ++ tailWord_8356281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356281).length < 2 ^ (prefixWord ++ tailWord_8356281).sum := by decide
  have hdescent : baseEnd_8356281 < baseStart_8356281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356331 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 3]
def baseStart_8356331 : Nat := 118140960795 + 8356331 * 2 ^ 59
def prefixEnd_8356331 : Nat := 4983230072969 + 3 ^ 40 * 8356331 * 2
def baseEnd_8356331 : Nat := 4290814311066050550232439

theorem tailTrace_8356331 : CollatzResearch.WordTrace tailWord_8356331 prefixEnd_8356331 4290814311066050550232439 := by
  unfold tailWord_8356331
  simp only [CollatzResearch.WordTrace]
  refine ⟨304780430289447409558876847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203186953526298273039251231 304780430289447409558876847)
  ·
    refine ⟨457170645434171114338315271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304780430289447409558876847 457170645434171114338315271)
    ·
      refine ⟨685755968151256671507472907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457170645434171114338315271 685755968151256671507472907)
      ·
        refine ⟨1028633952226885007261209361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685755968151256671507472907 1028633952226885007261209361)
        ·
          refine ⟨771475464170163755445907021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1028633952226885007261209361 771475464170163755445907021)
          ·
            refine ⟨289303299063811408292215133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 771475464170163755445907021 289303299063811408292215133)
            ·
              refine ⟨108488737148929278109580675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289303299063811408292215133 108488737148929278109580675)
              ·
                refine ⟨162733105723393917164371013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108488737148929278109580675 162733105723393917164371013)
                ·
                  refine ⟨30512457323136359468319565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162733105723393917164371013 30512457323136359468319565)
                  ·
                    refine ⟨11442171496176134800619837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30512457323136359468319565 11442171496176134800619837)
                    ·
                      refine ⟨4290814311066050550232439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11442171496176134800619837 4290814311066050550232439)
                      ·
                        rfl

theorem cell23_8356331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 3].length) (baseStart_8356331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356331 prefixEnd_8356331 := by exact prefixLift 8356331
  have htrace : WordTrace (prefixWord ++ tailWord_8356331) baseStart_8356331 baseEnd_8356331 := by
    simpa [prefixWord, tailWord_8356331, baseEnd_8356331] using wordTrace_append hprefix tailTrace_8356331
  have hstable : (prefixWord ++ tailWord_8356331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356331).length < 2 ^ (prefixWord ++ tailWord_8356331).sum := by decide
  have hdescent : baseEnd_8356331 < baseStart_8356331 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356371 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 4]
def baseStart_8356371 : Nat := 118140960795 + 8356371 * 2 ^ 59
def prefixEnd_8356371 : Nat := 4983230072969 + 3 ^ 40 * 8356371 * 2
def baseEnd_8356371 : Nat := 4290834850292230393732255

theorem tailTrace_8356371 : CollatzResearch.WordTrace tailWord_8356371 prefixEnd_8356371 4290834850292230393732255 := by
  unfold tailWord_8356371
  simp only [CollatzResearch.WordTrace]
  refine ⟨304781889209302496390332967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203187926139534997593555311 304781889209302496390332967)
  ·
    refine ⟨457172833813953744585499451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304781889209302496390332967 457172833813953744585499451)
    ·
      refine ⟨685759250720930616878249177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457172833813953744585499451 685759250720930616878249177)
      ·
        refine ⟨514319438040697962658686883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685759250720930616878249177 514319438040697962658686883)
        ·
          refine ⟨771479157061046943988030325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514319438040697962658686883 771479157061046943988030325)
          ·
            refine ⟨72326170974473150998877843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 771479157061046943988030325 72326170974473150998877843)
            ·
              refine ⟨108489256461709726498316765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72326170974473150998877843 108489256461709726498316765)
              ·
                refine ⟨40683471173141147436868787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108489256461709726498316765 40683471173141147436868787)
                ·
                  refine ⟨61025206759711721155303181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40683471173141147436868787 61025206759711721155303181)
                  ·
                    refine ⟨22884452534891895433238693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61025206759711721155303181 22884452534891895433238693)
                    ·
                      refine ⟨4290834850292230393732255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22884452534891895433238693 4290834850292230393732255)
                      ·
                        rfl

theorem cell23_8356371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_8356371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356371 prefixEnd_8356371 := by exact prefixLift 8356371
  have htrace : WordTrace (prefixWord ++ tailWord_8356371) baseStart_8356371 baseEnd_8356371 := by
    simpa [prefixWord, tailWord_8356371, baseEnd_8356371] using wordTrace_append hprefix tailTrace_8356371
  have hstable : (prefixWord ++ tailWord_8356371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356371).length < 2 ^ (prefixWord ++ tailWord_8356371).sum := by decide
  have hdescent : baseEnd_8356371 < baseStart_8356371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356372 : List Nat := [2, 4, 3, 1, 1, 1, 3, 3, 5]
def baseStart_8356372 : Nat := 118140960795 + 8356372 * 2 ^ 59
def prefixEnd_8356372 : Nat := 4983230072969 + 3 ^ 40 * 8356372 * 2
def baseEnd_8356372 : Nat := 476759484863653876646639

theorem tailTrace_8356372 : CollatzResearch.WordTrace tailWord_8356372 prefixEnd_8356372 476759484863653876646639 := by
  unfold tailWord_8356372
  simp only [CollatzResearch.WordTrace]
  refine ⟨152390962841149436780559685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203187950454865915707412913 152390962841149436780559685)
  ·
    refine ⟨28573305532715519396354941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152390962841149436780559685 28573305532715519396354941)
    ·
      refine ⟨10714989574768319773633103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28573305532715519396354941 10714989574768319773633103)
      ·
        refine ⟨16072484362152479660449655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10714989574768319773633103 16072484362152479660449655)
        ·
          refine ⟨24108726543228719490674483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16072484362152479660449655 24108726543228719490674483)
          ·
            refine ⟨36163089814843079236011725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24108726543228719490674483 36163089814843079236011725)
            ·
              refine ⟨13561158680566154713504397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36163089814843079236011725 13561158680566154713504397)
              ·
                refine ⟨5085434505212308017564149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13561158680566154713504397 5085434505212308017564149)
                ·
                  refine ⟨476759484863653876646639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5085434505212308017564149 476759484863653876646639)
                  ·
                    rfl

theorem cell23_8356372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_8356372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356372 prefixEnd_8356372 := by exact prefixLift 8356372
  have htrace : WordTrace (prefixWord ++ tailWord_8356372) baseStart_8356372 baseEnd_8356372 := by
    simpa [prefixWord, tailWord_8356372, baseEnd_8356372] using wordTrace_append hprefix tailTrace_8356372
  have hstable : (prefixWord ++ tailWord_8356372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356372).length < 2 ^ (prefixWord ++ tailWord_8356372).sum := by decide
  have hdescent : baseEnd_8356372 < baseStart_8356372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356401 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_8356401 : Nat := 118140960795 + 8356401 * 2 ^ 59
def prefixEnd_8356401 : Nat := 4983230072969 + 3 ^ 40 * 8356401 * 2
def baseEnd_8356401 : Nat := 4290850254711865276357117

theorem tailTrace_8356401 : CollatzResearch.WordTrace tailWord_8356401 prefixEnd_8356401 4290850254711865276357117 := by
  unfold tailWord_8356401
  simp only [CollatzResearch.WordTrace]
  refine ⟨304782983399193811513925057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203188655599462541009283371 304782983399193811513925057)
  ·
    refine ⟨228587237549395358635443793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304782983399193811513925057 228587237549395358635443793)
    ·
      refine ⟨171440428162046518976582845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228587237549395358635443793 171440428162046518976582845)
      ·
        refine ⟨64290160560767444616218567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171440428162046518976582845 64290160560767444616218567)
        ·
          refine ⟨96435240841151166924327851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64290160560767444616218567 96435240841151166924327851)
          ·
            refine ⟨144652861261726750386491777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96435240841151166924327851 144652861261726750386491777)
            ·
              refine ⟨108489645946295062789868833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144652861261726750386491777 108489645946295062789868833)
              ·
                refine ⟨81367234459721297092401625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108489645946295062789868833 81367234459721297092401625)
                ·
                  refine ⟨61025425844790972819301219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81367234459721297092401625 61025425844790972819301219)
                  ·
                    refine ⟨91538138767186459228951829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61025425844790972819301219 91538138767186459228951829)
                    ·
                      refine ⟨4290850254711865276357117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91538138767186459228951829 4290850254711865276357117)
                      ·
                        rfl

theorem cell23_8356401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_8356401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356401 prefixEnd_8356401 := by exact prefixLift 8356401
  have htrace : WordTrace (prefixWord ++ tailWord_8356401) baseStart_8356401 baseEnd_8356401 := by
    simpa [prefixWord, tailWord_8356401, baseEnd_8356401] using wordTrace_append hprefix tailTrace_8356401
  have hstable : (prefixWord ++ tailWord_8356401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356401).length < 2 ^ (prefixWord ++ tailWord_8356401).sum := by decide
  have hdescent : baseEnd_8356401 < baseStart_8356401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356408 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 4, 2, 3]
def baseStart_8356408 : Nat := 118140960795 + 8356408 * 2 ^ 59
def prefixEnd_8356408 : Nat := 4983230072969 + 3 ^ 40 * 8356408 * 2
def baseEnd_8356408 : Nat := 4290853849076446748969585

theorem tailTrace_8356408 : CollatzResearch.WordTrace tailWord_8356408 prefixEnd_8356408 4290853849076446748969585 := by
  unfold tailWord_8356408
  simp only [CollatzResearch.WordTrace]
  refine ⟨152391619355084225854714939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203188825806778967806286585 152391619355084225854714939)
  ·
    refine ⟨228587429032626338782072409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152391619355084225854714939 228587429032626338782072409)
    ·
      refine ⟨171440571774469754086554307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228587429032626338782072409 171440571774469754086554307)
      ·
        refine ⟨257160857661704631129831461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171440571774469754086554307 257160857661704631129831461)
        ·
          refine ⟨48217660811569618336843399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257160857661704631129831461 48217660811569618336843399)
          ·
            refine ⟨72326491217354427505265099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48217660811569618336843399 72326491217354427505265099)
            ·
              refine ⟨108489736826031641257897649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72326491217354427505265099 108489736826031641257897649)
              ·
                refine ⟨81367302619523730943423237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108489736826031641257897649 81367302619523730943423237)
                ·
                  refine ⟨15256369241160699551891857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81367302619523730943423237 15256369241160699551891857)
                  ·
                    refine ⟨11442276930870524663918893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15256369241160699551891857 11442276930870524663918893)
                    ·
                      refine ⟨4290853849076446748969585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11442276930870524663918893 4290853849076446748969585)
                      ·
                        rfl

theorem cell23_8356408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_8356408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356408 prefixEnd_8356408 := by exact prefixLift 8356408
  have htrace : WordTrace (prefixWord ++ tailWord_8356408) baseStart_8356408 baseEnd_8356408 := by
    simpa [prefixWord, tailWord_8356408, baseEnd_8356408] using wordTrace_append hprefix tailTrace_8356408
  have hstable : (prefixWord ++ tailWord_8356408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356408).length < 2 ^ (prefixWord ++ tailWord_8356408).sum := by decide
  have hdescent : baseEnd_8356408 < baseStart_8356408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356422 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_8356422 : Nat := 118140960795 + 8356422 * 2 ^ 59
def prefixEnd_8356422 : Nat := 4983230072969 + 3 ^ 40 * 8356422 * 2
def baseEnd_8356422 : Nat := 4290861037805609694194521

theorem tailTrace_8356422 : CollatzResearch.WordTrace tailWord_8356422 prefixEnd_8356422 4290861037805609694194521 := by
  unfold tailWord_8356422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9524492166628679128138735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203189166221411821400293013 9524492166628679128138735)
  ·
    refine ⟨14286738249943018692208103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9524492166628679128138735 14286738249943018692208103)
    ·
      refine ⟨21430107374914528038312155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14286738249943018692208103 21430107374914528038312155)
      ·
        refine ⟨32145161062371792057468233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21430107374914528038312155 32145161062371792057468233)
        ·
          refine ⟨24108870796778844043101175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32145161062371792057468233 24108870796778844043101175)
          ·
            refine ⟨36163306195168266064651763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24108870796778844043101175 36163306195168266064651763)
            ·
              refine ⟨54244959292752399096977645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36163306195168266064651763 54244959292752399096977645)
              ·
                refine ⟨20341859734782149661366617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54244959292752399096977645 20341859734782149661366617)
                ·
                  refine ⟨15256394801086612246024963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20341859734782149661366617 15256394801086612246024963)
                  ·
                    refine ⟨22884592201629918369037445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15256394801086612246024963 22884592201629918369037445)
                    ·
                      refine ⟨4290861037805609694194521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22884592201629918369037445 4290861037805609694194521)
                      ·
                        rfl

theorem cell23_8356422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_8356422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356422 prefixEnd_8356422 := by exact prefixLift 8356422
  have htrace : WordTrace (prefixWord ++ tailWord_8356422) baseStart_8356422 baseEnd_8356422 := by
    simpa [prefixWord, tailWord_8356422, baseEnd_8356422] using wordTrace_append hprefix tailTrace_8356422
  have hstable : (prefixWord ++ tailWord_8356422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356422).length < 2 ^ (prefixWord ++ tailWord_8356422).sum := by decide
  have hdescent : baseEnd_8356422 < baseStart_8356422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356449 : List Nat := [1, 2, 3, 1, 1, 6, 2, 2, 1, 4]
def baseStart_8356449 : Nat := 118140960795 + 8356449 * 2 ^ 59
def prefixEnd_8356449 : Nat := 4983230072969 + 3 ^ 40 * 8356449 * 2
def baseEnd_8356449 : Nat := 1430291633927760362852299

theorem tailTrace_8356449 : CollatzResearch.WordTrace tailWord_8356449 prefixEnd_8356449 1430291633927760362852299 := by
  unfold tailWord_8356449
  simp only [CollatzResearch.WordTrace]
  refine ⟨304784734103019915711672401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203189822735346610474448267 304784734103019915711672401)
  ·
    refine ⟨228588550577264936783754301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304784734103019915711672401 228588550577264936783754301)
    ·
      refine ⟨85720706466474351293907863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228588550577264936783754301 85720706466474351293907863)
      ·
        refine ⟨128581059699711526940861795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85720706466474351293907863 128581059699711526940861795)
        ·
          refine ⟨192871589549567290411292693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128581059699711526940861795 192871589549567290411292693)
          ·
            refine ⟨9040855760135966738029345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192871589549567290411292693 9040855760135966738029345)
            ·
              refine ⟨6780641820101975053522009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9040855760135966738029345 6780641820101975053522009)
              ·
                refine ⟨5085481365076481290141507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6780641820101975053522009 5085481365076481290141507)
                ·
                  refine ⟨7628222047614721935212261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5085481365076481290141507 7628222047614721935212261)
                  ·
                    refine ⟨1430291633927760362852299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7628222047614721935212261 1430291633927760362852299)
                    ·
                      rfl

theorem cell23_8356449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_8356449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356449 prefixEnd_8356449 := by exact prefixLift 8356449
  have htrace : WordTrace (prefixWord ++ tailWord_8356449) baseStart_8356449 baseEnd_8356449 := by
    simpa [prefixWord, tailWord_8356449, baseEnd_8356449] using wordTrace_append hprefix tailTrace_8356449
  have hstable : (prefixWord ++ tailWord_8356449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356449).length < 2 ^ (prefixWord ++ tailWord_8356449).sum := by decide
  have hdescent : baseEnd_8356449 < baseStart_8356449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356455 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_8356455 : Nat := 118140960795 + 8356455 * 2 ^ 59
def prefixEnd_8356455 : Nat := 4983230072969 + 3 ^ 40 * 8356455 * 2
def baseEnd_8356455 : Nat := 4290877982667208065081869

theorem tailTrace_8356455 : CollatzResearch.WordTrace tailWord_8356455 prefixEnd_8356455 4290877982667208065081869 := by
  unfold tailWord_8356455
  simp only [CollatzResearch.WordTrace]
  refine ⟨304784952940998178736390819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203189968627332119157593879 304784952940998178736390819)
  ·
    refine ⟨457177429411497268104586229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304784952940998178736390819 457177429411497268104586229)
    ·
      refine ⟨42860384007327868884804959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 457177429411497268104586229 42860384007327868884804959)
      ·
        refine ⟨64290576010991803327207439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42860384007327868884804959 64290576010991803327207439)
        ·
          refine ⟨96435864016487704990811159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64290576010991803327207439 96435864016487704990811159)
          ·
            refine ⟨144653796024731557486216739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96435864016487704990811159 144653796024731557486216739)
            ·
              refine ⟨216980694037097336229325109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144653796024731557486216739 216980694037097336229325109)
              ·
                refine ⟨20341940065977875271499229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216980694037097336229325109 20341940065977875271499229)
                ·
                  refine ⟨7628227524741703226812211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20341940065977875271499229 7628227524741703226812211)
                  ·
                    refine ⟨11442341287112554840218317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7628227524741703226812211 11442341287112554840218317)
                    ·
                      refine ⟨4290877982667208065081869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11442341287112554840218317 4290877982667208065081869)
                      ·
                        rfl

theorem cell23_8356455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_8356455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356455 prefixEnd_8356455 := by exact prefixLift 8356455
  have htrace : WordTrace (prefixWord ++ tailWord_8356455) baseStart_8356455 baseEnd_8356455 := by
    simpa [prefixWord, tailWord_8356455, baseEnd_8356455] using wordTrace_append hprefix tailTrace_8356455
  have hstable : (prefixWord ++ tailWord_8356455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356455).length < 2 ^ (prefixWord ++ tailWord_8356455).sum := by decide
  have hdescent : baseEnd_8356455 < baseStart_8356455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356458 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 5, 5]
def baseStart_8356458 : Nat := 118140960795 + 8356458 * 2 ^ 59
def prefixEnd_8356458 : Nat := 4983230072969 + 3 ^ 40 * 8356458 * 2
def baseEnd_8356458 : Nat := 1430293174369723851114785

theorem tailTrace_8356458 : CollatzResearch.WordTrace tailWord_8356458 prefixEnd_8356458 1430293174369723851114785 := by
  unfold tailWord_8356458
  simp only [CollatzResearch.WordTrace]
  refine ⟨76196265589996827562187507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203190041573324873499166685 76196265589996827562187507)
  ·
    refine ⟨114294398384995241343281261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76196265589996827562187507 114294398384995241343281261)
    ·
      refine ⟨42860399394373215503730473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114294398384995241343281261 42860399394373215503730473)
      ·
        refine ⟨32145299545779911627797855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42860399394373215503730473 32145299545779911627797855)
        ·
          refine ⟨48217949318669867441696783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32145299545779911627797855 48217949318669867441696783)
          ·
            refine ⟨72326923978004801162545175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48217949318669867441696783 72326923978004801162545175)
            ·
              refine ⟨108490385967007201743817763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72326923978004801162545175 108490385967007201743817763)
              ·
                refine ⟨162735578950510802615726645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108490385967007201743817763 162735578950510802615726645)
                ·
                  refine ⟨15256460526610387745224373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162735578950510802615726645 15256460526610387745224373)
                  ·
                    refine ⟨1430293174369723851114785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15256460526610387745224373 1430293174369723851114785)
                    ·
                      rfl

theorem cell23_8356458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_8356458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356458 prefixEnd_8356458 := by exact prefixLift 8356458
  have htrace : WordTrace (prefixWord ++ tailWord_8356458) baseStart_8356458 baseEnd_8356458 := by
    simpa [prefixWord, tailWord_8356458, baseEnd_8356458] using wordTrace_append hprefix tailTrace_8356458
  have hstable : (prefixWord ++ tailWord_8356458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356458).length < 2 ^ (prefixWord ++ tailWord_8356458).sum := by decide
  have hdescent : baseEnd_8356458 < baseStart_8356458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356525 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_8356525 : Nat := 118140960795 + 8356525 * 2 ^ 59
def prefixEnd_8356525 : Nat := 4983230072969 + 3 ^ 40 * 8356525 * 2
def baseEnd_8356525 : Nat := 4290913926313022791206547

theorem tailTrace_8356525 : CollatzResearch.WordTrace tailWord_8356525 prefixEnd_8356525 4290913926313022791206547 := by
  unfold tailWord_8356525
  simp only [CollatzResearch.WordTrace]
  refine ⟨304787506050744580691439029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203191670700496387127626019 304787506050744580691439029)
  ·
    refine ⟨28573828692257304439822409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304787506050744580691439029 28573828692257304439822409)
    ·
      refine ⟨21430371519192978329866807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28573828692257304439822409 21430371519192978329866807)
      ·
        refine ⟨32145557278789467494800211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21430371519192978329866807 32145557278789467494800211)
        ·
          refine ⟨48218335918184201242200317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32145557278789467494800211 48218335918184201242200317)
          ·
            refine ⟨18081875969319075465825119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48218335918184201242200317 18081875969319075465825119)
            ·
              refine ⟨27122813953978613198737679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18081875969319075465825119 27122813953978613198737679)
              ·
                refine ⟨40684220930967919798106519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27122813953978613198737679 40684220930967919798106519)
                ·
                  refine ⟨61026331396451879697159779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40684220930967919798106519 61026331396451879697159779)
                  ·
                    refine ⟨91539497094677819545739669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61026331396451879697159779 91539497094677819545739669)
                    ·
                      refine ⟨4290913926313022791206547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91539497094677819545739669 4290913926313022791206547)
                      ·
                        rfl

theorem cell23_8356525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_8356525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356525 prefixEnd_8356525 := by exact prefixLift 8356525
  have htrace : WordTrace (prefixWord ++ tailWord_8356525) baseStart_8356525 baseEnd_8356525 := by
    simpa [prefixWord, tailWord_8356525, baseEnd_8356525] using wordTrace_append hprefix tailTrace_8356525
  have hstable : (prefixWord ++ tailWord_8356525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356525).length < 2 ^ (prefixWord ++ tailWord_8356525).sum := by decide
  have hdescent : baseEnd_8356525 < baseStart_8356525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356529 : List Nat := [1, 2, 2, 6, 1, 1, 2, 2, 1, 1, 4]
def baseStart_8356529 : Nat := 118140960795 + 8356529 * 2 ^ 59
def prefixEnd_8356529 : Nat := 4983230072969 + 3 ^ 40 * 8356529 * 2
def baseEnd_8356529 : Nat := 4290915980235640775556529

theorem tailTrace_8356529 : CollatzResearch.WordTrace tailWord_8356529 prefixEnd_8356529 4290915980235640775556529 := by
  unfold tailWord_8356529
  simp only [CollatzResearch.WordTrace]
  refine ⟨304787651942730089374584641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203191767961820059583056427 304787651942730089374584641)
  ·
    refine ⟨228590738957047567030938481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304787651942730089374584641 228590738957047567030938481)
    ·
      refine ⟨171443054217785675273203861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228590738957047567030938481 171443054217785675273203861)
      ·
        refine ⟨8036393166458703528431431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171443054217785675273203861 8036393166458703528431431)
        ·
          refine ⟨12054589749688055292647147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8036393166458703528431431 12054589749688055292647147)
          ·
            refine ⟨18081884624532082938970721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12054589749688055292647147 18081884624532082938970721)
            ·
              refine ⟨13561413468399062204228041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18081884624532082938970721 13561413468399062204228041)
              ·
                refine ⟨10171060101299296653171031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13561413468399062204228041 10171060101299296653171031)
                ·
                  refine ⟨15256590151948944979756547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10171060101299296653171031 15256590151948944979756547)
                  ·
                    refine ⟨22884885227923417469634821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15256590151948944979756547 22884885227923417469634821)
                    ·
                      refine ⟨4290915980235640775556529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22884885227923417469634821 4290915980235640775556529)
                      ·
                        rfl

theorem cell23_8356529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_8356529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356529 prefixEnd_8356529 := by exact prefixLift 8356529
  have htrace : WordTrace (prefixWord ++ tailWord_8356529) baseStart_8356529 baseEnd_8356529 := by
    simpa [prefixWord, tailWord_8356529, baseEnd_8356529] using wordTrace_append hprefix tailTrace_8356529
  have hstable : (prefixWord ++ tailWord_8356529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356529).length < 2 ^ (prefixWord ++ tailWord_8356529).sum := by decide
  have hdescent : baseEnd_8356529 < baseStart_8356529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356555 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 7, 3, 2]
def baseStart_8356555 : Nat := 118140960795 + 8356555 * 2 ^ 59
def prefixEnd_8356555 : Nat := 4983230072969 + 3 ^ 40 * 8356555 * 2
def baseEnd_8356555 : Nat := 4290929330732657673831409

theorem tailTrace_8356555 : CollatzResearch.WordTrace tailWord_8356555 prefixEnd_8356555 4290929330732657673831409 := by
  unfold tailWord_8356555
  simp only [CollatzResearch.WordTrace]
  refine ⟨304788600240635895815031119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203192400160423930543354079 304788600240635895815031119)
  ·
    refine ⟨457182900360953843722546679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304788600240635895815031119 457182900360953843722546679)
    ·
      refine ⟨685774350541430765583820019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457182900360953843722546679 685774350541430765583820019)
      ·
        refine ⟨1028661525812146148375730029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685774350541430765583820019 1028661525812146148375730029)
        ·
          refine ⟨385748072179554805640898761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1028661525812146148375730029 385748072179554805640898761)
          ·
            refine ⟨289311054134666104230674071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385748072179554805640898761 289311054134666104230674071)
            ·
              refine ⟨433966581201999156346011107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289311054134666104230674071 433966581201999156346011107)
              ·
                refine ⟨650949871802998734519016661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433966581201999156346011107 650949871802998734519016661)
                ·
                  refine ⟨15256637620382782840289453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 650949871802998734519016661 15256637620382782840289453)
                  ·
                    refine ⟨5721239107643543565108545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15256637620382782840289453 5721239107643543565108545)
                    ·
                      refine ⟨4290929330732657673831409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5721239107643543565108545 4290929330732657673831409)
                      ·
                        rfl

theorem cell23_8356555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 3, 2].length) (baseStart_8356555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356555 prefixEnd_8356555 := by exact prefixLift 8356555
  have htrace : WordTrace (prefixWord ++ tailWord_8356555) baseStart_8356555 baseEnd_8356555 := by
    simpa [prefixWord, tailWord_8356555, baseEnd_8356555] using wordTrace_append hprefix tailTrace_8356555
  have hstable : (prefixWord ++ tailWord_8356555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356555).length < 2 ^ (prefixWord ++ tailWord_8356555).sum := by decide
  have hdescent : baseEnd_8356555 < baseStart_8356555 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356579 : List Nat := [1, 1, 1, 7, 1, 2, 1, 3, 2, 1, 3]
def baseStart_8356579 : Nat := 118140960795 + 8356579 * 2 ^ 59
def prefixEnd_8356579 : Nat := 4983230072969 + 3 ^ 40 * 8356579 * 2
def baseEnd_8356579 : Nat := 4290941654268365579931299

theorem tailTrace_8356579 : CollatzResearch.WordTrace tailWord_8356579 prefixEnd_8356579 4290941654268365579931299 := by
  unfold tailWord_8356579
  simp only [CollatzResearch.WordTrace]
  refine ⟨304789475592548947913904791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203192983728365965275936527 304789475592548947913904791)
  ·
    refine ⟨457184213388823421870857187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304789475592548947913904791 457184213388823421870857187)
    ·
      refine ⟨685776320083235132806285781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457184213388823421870857187 685776320083235132806285781)
      ·
        refine ⟨16072882501950823425147323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 685776320083235132806285781 16072882501950823425147323)
        ·
          refine ⟨24109323752926235137720985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16072882501950823425147323 24109323752926235137720985)
          ·
            refine ⟨18081992814694676353290739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24109323752926235137720985 18081992814694676353290739)
            ·
              refine ⟨27122989222042014529936109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18081992814694676353290739 27122989222042014529936109)
              ·
                refine ⟨10171120958265755448726041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27122989222042014529936109 10171120958265755448726041)
                ·
                  refine ⟨7628340718699316586544531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10171120958265755448726041 7628340718699316586544531)
                  ·
                    refine ⟨11442511078048974879816797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7628340718699316586544531 11442511078048974879816797)
                    ·
                      refine ⟨4290941654268365579931299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11442511078048974879816797 4290941654268365579931299)
                      ·
                        rfl

theorem cell23_8356579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_8356579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356579 prefixEnd_8356579 := by exact prefixLift 8356579
  have htrace : WordTrace (prefixWord ++ tailWord_8356579) baseStart_8356579 baseEnd_8356579 := by
    simpa [prefixWord, tailWord_8356579, baseEnd_8356579] using wordTrace_append hprefix tailTrace_8356579
  have hstable : (prefixWord ++ tailWord_8356579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356579).length < 2 ^ (prefixWord ++ tailWord_8356579).sum := by decide
  have hdescent : baseEnd_8356579 < baseStart_8356579 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356596 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_8356596 : Nat := 118140960795 + 8356596 * 2 ^ 59
def prefixEnd_8356596 : Nat := 4983230072969 + 3 ^ 40 * 8356596 * 2
def baseEnd_8356596 : Nat := 4290950383439492013418721

theorem tailTrace_8356596 : CollatzResearch.WordTrace tailWord_8356596 prefixEnd_8356596 4290950383439492013418721 := by
  unfold tailWord_8356596
  simp only [CollatzResearch.WordTrace]
  refine ⟨152395047816743679908636821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203193397088991573211515761 152395047816743679908636821)
  ·
    refine ⟨7143517866409859995717351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152395047816743679908636821 7143517866409859995717351)
    ·
      refine ⟨10715276799614789993576027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7143517866409859995717351 10715276799614789993576027)
      ·
        refine ⟨16072915199422184990364041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10715276799614789993576027 16072915199422184990364041)
        ·
          refine ⟨12054686399566638742773031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16072915199422184990364041 12054686399566638742773031)
          ·
            refine ⟨18082029599349958114159547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12054686399566638742773031 18082029599349958114159547)
            ·
              refine ⟨27123044399024937171239321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18082029599349958114159547 27123044399024937171239321)
              ·
                refine ⟨20342283299268702878429491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27123044399024937171239321 20342283299268702878429491)
                ·
                  refine ⟨30513424948903054317644237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20342283299268702878429491 30513424948903054317644237)
                  ·
                    refine ⟨11442534355838645369116589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30513424948903054317644237 11442534355838645369116589)
                    ·
                      refine ⟨4290950383439492013418721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11442534355838645369116589 4290950383439492013418721)
                      ·
                        rfl

theorem cell23_8356596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_8356596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356596 prefixEnd_8356596 := by exact prefixLift 8356596
  have htrace : WordTrace (prefixWord ++ tailWord_8356596) baseStart_8356596 baseEnd_8356596 := by
    simpa [prefixWord, tailWord_8356596, baseEnd_8356596] using wordTrace_append hprefix tailTrace_8356596
  have hstable : (prefixWord ++ tailWord_8356596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356596).length < 2 ^ (prefixWord ++ tailWord_8356596).sum := by decide
  have hdescent : baseEnd_8356596 < baseStart_8356596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356602 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2]
def baseStart_8356602 : Nat := 118140960795 + 8356602 * 2 ^ 59
def prefixEnd_8356602 : Nat := 4983230072969 + 3 ^ 40 * 8356602 * 2
def baseEnd_8356602 : Nat := 4290953464323418989943693

theorem tailTrace_8356602 : CollatzResearch.WordTrace tailWord_8356602 prefixEnd_8356602 4290953464323418989943693 := by
  unfold tailWord_8356602
  simp only [CollatzResearch.WordTrace]
  refine ⟨76197578617866405710498015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203193542980977081894661373 76197578617866405710498015)
  ·
    refine ⟨114296367926799608565747023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76197578617866405710498015 114296367926799608565747023)
    ·
      refine ⟨171444551890199412848620535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114296367926799608565747023 171444551890199412848620535)
      ·
        refine ⟨257166827835299119272930803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171444551890199412848620535 257166827835299119272930803)
        ·
          refine ⟨385750241752948678909396205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257166827835299119272930803 385750241752948678909396205)
          ·
            refine ⟨144656340657355754591023577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385750241752948678909396205 144656340657355754591023577)
            ·
              refine ⟨108492255493016815943267683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144656340657355754591023577 108492255493016815943267683)
              ·
                refine ⟨162738383239525223914901525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108492255493016815943267683 162738383239525223914901525)
                ·
                  refine ⟨7628361714352744871011009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162738383239525223914901525 7628361714352744871011009)
                  ·
                    refine ⟨5721271285764558653258257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7628361714352744871011009 5721271285764558653258257)
                    ·
                      refine ⟨4290953464323418989943693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5721271285764558653258257 4290953464323418989943693)
                      ·
                        rfl

theorem cell23_8356602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2].length) (baseStart_8356602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356602 prefixEnd_8356602 := by exact prefixLift 8356602
  have htrace : WordTrace (prefixWord ++ tailWord_8356602) baseStart_8356602 baseEnd_8356602 := by
    simpa [prefixWord, tailWord_8356602, baseEnd_8356602] using wordTrace_append hprefix tailTrace_8356602
  have hstable : (prefixWord ++ tailWord_8356602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356602).length < 2 ^ (prefixWord ++ tailWord_8356602).sum := by decide
  have hdescent : baseEnd_8356602 < baseStart_8356602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356670 : List Nat := [4, 2, 1, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_8356670 : Nat := 118140960795 + 8356670 * 2 ^ 59
def prefixEnd_8356670 : Nat := 4983230072969 + 3 ^ 40 * 8356670 * 2
def baseEnd_8356670 : Nat := 4290988381007924723893381

theorem tailTrace_8356670 : CollatzResearch.WordTrace tailWord_8356670 prefixEnd_8356670 4290988381007924723893381 := by
  unfold tailWord_8356670
  simp only [CollatzResearch.WordTrace]
  refine ⟨38099099329402408806933433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203195196423479513636978309 38099099329402408806933433)
  ·
    refine ⟨28574324497051806605200075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38099099329402408806933433 28574324497051806605200075)
    ·
      refine ⟨42861486745577709907800113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28574324497051806605200075 42861486745577709907800113)
      ·
        refine ⟨32146115059183282430850085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42861486745577709907800113 32146115059183282430850085)
        ·
          refine ⟨6027396573596865455784391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32146115059183282430850085 6027396573596865455784391)
          ·
            refine ⟨9041094860395298183676587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6027396573596865455784391 9041094860395298183676587)
            ·
              refine ⟨13561642290592947275514881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9041094860395298183676587 13561642290592947275514881)
              ·
                refine ⟨10171231717944710456636161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13561642290592947275514881 10171231717944710456636161)
                ·
                  refine ⟨7628423788458532842477121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10171231717944710456636161 7628423788458532842477121)
                  ·
                    refine ⟨5721317841343899631857841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7628423788458532842477121 5721317841343899631857841)
                    ·
                      refine ⟨4290988381007924723893381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5721317841343899631857841 4290988381007924723893381)
                      ·
                        rfl

theorem cell23_8356670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_8356670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356670 prefixEnd_8356670 := by exact prefixLift 8356670
  have htrace : WordTrace (prefixWord ++ tailWord_8356670) baseStart_8356670 baseEnd_8356670 := by
    simpa [prefixWord, tailWord_8356670, baseEnd_8356670] using wordTrace_append hprefix tailTrace_8356670
  have hstable : (prefixWord ++ tailWord_8356670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356670).length < 2 ^ (prefixWord ++ tailWord_8356670).sum := by decide
  have hdescent : baseEnd_8356670 < baseStart_8356670 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356675 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 4]
def baseStart_8356675 : Nat := 118140960795 + 8356675 * 2 ^ 59
def prefixEnd_8356675 : Nat := 4983230072969 + 3 ^ 40 * 8356675 * 2
def baseEnd_8356675 : Nat := 4290990948411197204330857

theorem tailTrace_8356675 : CollatzResearch.WordTrace tailWord_8356675 prefixEnd_8356675 4290990948411197204330857 := by
  unfold tailWord_8356675
  simp only [CollatzResearch.WordTrace]
  refine ⟨304792977000201156309399479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203195318000134104206266319 304792977000201156309399479)
  ·
    refine ⟨457189465500301734464099219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304792977000201156309399479 457189465500301734464099219)
    ·
      refine ⟨685784198250452601696148829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457189465500301734464099219 685784198250452601696148829)
      ·
        refine ⟨257169074343919725636055811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 685784198250452601696148829 257169074343919725636055811)
        ·
          refine ⟨385753611515879588454083717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257169074343919725636055811 385753611515879588454083717)
          ·
            refine ⟨72328802159227422835140697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 385753611515879588454083717 72328802159227422835140697)
            ·
              refine ⟨54246601619420567126355523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72328802159227422835140697 54246601619420567126355523)
              ·
                refine ⟨81369902429130850689533285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54246601619420567126355523 81369902429130850689533285)
                ·
                  refine ⟨15256856705462034504287491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81369902429130850689533285 15256856705462034504287491)
                  ·
                    refine ⟨22885285058193051756431237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15256856705462034504287491 22885285058193051756431237)
                    ·
                      refine ⟨4290990948411197204330857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22885285058193051756431237 4290990948411197204330857)
                      ·
                        rfl

theorem cell23_8356675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_8356675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356675 prefixEnd_8356675 := by exact prefixLift 8356675
  have htrace : WordTrace (prefixWord ++ tailWord_8356675) baseStart_8356675 baseEnd_8356675 := by
    simpa [prefixWord, tailWord_8356675, baseEnd_8356675] using wordTrace_append hprefix tailTrace_8356675
  have hstable : (prefixWord ++ tailWord_8356675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356675).length < 2 ^ (prefixWord ++ tailWord_8356675).sum := by decide
  have hdescent : baseEnd_8356675 < baseStart_8356675 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356712 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_8356712 : Nat := 118140960795 + 8356712 * 2 ^ 59
def prefixEnd_8356712 : Nat := 4983230072969 + 3 ^ 40 * 8356712 * 2
def baseEnd_8356712 : Nat := 4291009947195413559568187

theorem tailTrace_8356712 : CollatzResearch.WordTrace tailWord_8356712 prefixEnd_8356712 4291009947195413559568187 := by
  unfold tailWord_8356712
  simp only [CollatzResearch.WordTrace]
  refine ⟨152397163250533555814248195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203196217667378074418997593 152397163250533555814248195)
  ·
    refine ⟨228595744875800333721372293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152397163250533555814248195 228595744875800333721372293)
    ·
      refine ⟨42861702164212562572757305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228595744875800333721372293 42861702164212562572757305)
      ·
        refine ⟨32146276623159421929567979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42861702164212562572757305 32146276623159421929567979)
        ·
          refine ⟨48219414934739132894351969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32146276623159421929567979 48219414934739132894351969)
          ·
            refine ⟨36164561201054349670763977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48219414934739132894351969 36164561201054349670763977)
            ·
              refine ⟨27123420900790762253072983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36164561201054349670763977 27123420900790762253072983)
              ·
                refine ⟨40685131351186143379609475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27123420900790762253072983 40685131351186143379609475)
                ·
                  refine ⟨61027697026779215069414213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40685131351186143379609475 61027697026779215069414213)
                  ·
                    refine ⟨11442693192521102825515165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61027697026779215069414213 11442693192521102825515165)
                    ·
                      refine ⟨4291009947195413559568187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11442693192521102825515165 4291009947195413559568187)
                      ·
                        rfl

theorem cell23_8356712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_8356712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356712 prefixEnd_8356712 := by exact prefixLift 8356712
  have htrace : WordTrace (prefixWord ++ tailWord_8356712) baseStart_8356712 baseEnd_8356712 := by
    simpa [prefixWord, tailWord_8356712, baseEnd_8356712] using wordTrace_append hprefix tailTrace_8356712
  have hstable : (prefixWord ++ tailWord_8356712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356712).length < 2 ^ (prefixWord ++ tailWord_8356712).sum := by decide
  have hdescent : baseEnd_8356712 < baseStart_8356712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356793 : List Nat := [1, 2, 1, 4, 2, 2, 4, 2, 1, 1, 3]
def baseStart_8356793 : Nat := 118140960795 + 8356793 * 2 ^ 59
def prefixEnd_8356793 : Nat := 4983230072969 + 3 ^ 40 * 8356793 * 2
def baseEnd_8356793 : Nat := 4291051539128427742655315

theorem tailTrace_8356793 : CollatzResearch.WordTrace tailWord_8356793 prefixEnd_8356793 4291051539128427742655315 := by
  unfold tailWord_8356793
  simp only [CollatzResearch.WordTrace]
  refine ⟨304797280813773662462195033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203198187209182441641463355 304797280813773662462195033)
  ·
    refine ⟨228597960610330246846646275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304797280813773662462195033 228597960610330246846646275)
    ·
      refine ⟨342896940915495370269969413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228597960610330246846646275 342896940915495370269969413)
      ·
        refine ⟨64293176421655381925619265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342896940915495370269969413 64293176421655381925619265)
        ·
          refine ⟨48219882316241536444214449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64293176421655381925619265 48219882316241536444214449)
          ·
            refine ⟨36164911737181152333160837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48219882316241536444214449 36164911737181152333160837)
            ·
              refine ⟨6780920950721466062467657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36164911737181152333160837 6780920950721466062467657)
              ·
                refine ⟨5085690713041099546850743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6780920950721466062467657 5085690713041099546850743)
                ·
                  refine ⟨7628536069561649320276115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5085690713041099546850743 7628536069561649320276115)
                  ·
                    refine ⟨11442804104342473980414173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7628536069561649320276115 11442804104342473980414173)
                    ·
                      refine ⟨4291051539128427742655315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11442804104342473980414173 4291051539128427742655315)
                      ·
                        rfl

theorem cell23_8356793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_8356793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356793 prefixEnd_8356793 := by exact prefixLift 8356793
  have htrace : WordTrace (prefixWord ++ tailWord_8356793) baseStart_8356793 baseEnd_8356793 := by
    simpa [prefixWord, tailWord_8356793, baseEnd_8356793] using wordTrace_append hprefix tailTrace_8356793
  have hstable : (prefixWord ++ tailWord_8356793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356793).length < 2 ^ (prefixWord ++ tailWord_8356793).sum := by decide
  have hdescent : baseEnd_8356793 < baseStart_8356793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356829 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_8356829 : Nat := 118140960795 + 8356829 * 2 ^ 59
def prefixEnd_8356829 : Nat := 4983230072969 + 3 ^ 40 * 8356829 * 2
def baseEnd_8356829 : Nat := 4291070024431989601805149

theorem tailTrace_8356829 : CollatzResearch.WordTrace tailWord_8356829 prefixEnd_8356829 4291070024431989601805149 := by
  unfold tailWord_8356829
  simp only [CollatzResearch.WordTrace]
  refine ⟨304798593841643240610505541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203199062561095493740337027 304798593841643240610505541)
  ·
    refine ⟨57149736345308107614469789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304798593841643240610505541 57149736345308107614469789)
    ·
      refine ⟨21431151129490540355426171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57149736345308107614469789 21431151129490540355426171)
      ·
        refine ⟨32146726694235810533139257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21431151129490540355426171 32146726694235810533139257)
        ·
          refine ⟨24110045020676857899854443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32146726694235810533139257 24110045020676857899854443)
          ·
            refine ⟨36165067531015286849781665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24110045020676857899854443 36165067531015286849781665)
            ·
              refine ⟨27123800648261465137336249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36165067531015286849781665 27123800648261465137336249)
              ·
                refine ⟨20342850486196098853002187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27123800648261465137336249 20342850486196098853002187)
                ·
                  refine ⟨30514275729294148279503281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20342850486196098853002187 30514275729294148279503281)
                  ·
                    refine ⟨22885706796970611209627461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30514275729294148279503281 22885706796970611209627461)
                    ·
                      refine ⟨4291070024431989601805149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22885706796970611209627461 4291070024431989601805149)
                      ·
                        rfl

theorem cell23_8356829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_8356829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356829 prefixEnd_8356829 := by exact prefixLift 8356829
  have htrace : WordTrace (prefixWord ++ tailWord_8356829) baseStart_8356829 baseEnd_8356829 := by
    simpa [prefixWord, tailWord_8356829, baseEnd_8356829] using wordTrace_append hprefix tailTrace_8356829
  have hstable : (prefixWord ++ tailWord_8356829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356829).length < 2 ^ (prefixWord ++ tailWord_8356829).sum := by decide
  have hdescent : baseEnd_8356829 < baseStart_8356829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356850 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 3, 2, 2]
def baseStart_8356850 : Nat := 118140960795 + 8356850 * 2 ^ 59
def prefixEnd_8356850 : Nat := 4983230072969 + 3 ^ 40 * 8356850 * 2
def baseEnd_8356850 : Nat := 4291080807525734019642553

theorem tailTrace_8356850 : CollatzResearch.WordTrace tailWord_8356850 prefixEnd_8356850 4291080807525734019642553 := by
  unfold tailWord_8356850
  simp only [CollatzResearch.WordTrace]
  refine ⟨76199839943641790299255001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203199573183044774131346669 76199839943641790299255001)
  ·
    refine ⟨57149879957731342724441251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76199839943641790299255001 57149879957731342724441251)
    ·
      refine ⟨85724819936597014086661877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57149879957731342724441251 85724819936597014086661877)
      ·
        refine ⟨8036701869055970070624551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85724819936597014086661877 8036701869055970070624551)
        ·
          refine ⟨12055052803583955105936827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8036701869055970070624551 12055052803583955105936827)
          ·
            refine ⟨18082579205375932658905241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12055052803583955105936827 18082579205375932658905241)
            ·
              refine ⟨13561934404031949494178931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18082579205375932658905241 13561934404031949494178931)
              ·
                refine ⟨20342901606047924241268397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13561934404031949494178931 20342901606047924241268397)
                ·
                  refine ⟨7628588102267971590475649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20342901606047924241268397 7628588102267971590475649)
                  ·
                    refine ⟨5721441076700978692856737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7628588102267971590475649 5721441076700978692856737)
                    ·
                      refine ⟨4291080807525734019642553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5721441076700978692856737 4291080807525734019642553)
                      ·
                        rfl

theorem cell23_8356850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_8356850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356850 prefixEnd_8356850 := by exact prefixLift 8356850
  have htrace : WordTrace (prefixWord ++ tailWord_8356850) baseStart_8356850 baseEnd_8356850 := by
    simpa [prefixWord, tailWord_8356850, baseEnd_8356850] using wordTrace_append hprefix tailTrace_8356850
  have hstable : (prefixWord ++ tailWord_8356850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356850).length < 2 ^ (prefixWord ++ tailWord_8356850).sum := by decide
  have hdescent : baseEnd_8356850 < baseStart_8356850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356876 : List Nat := [2, 2, 1, 2, 3, 2, 1, 4, 1, 3, 2]
def baseStart_8356876 : Nat := 118140960795 + 8356876 * 2 ^ 59
def prefixEnd_8356876 : Nat := 4983230072969 + 3 ^ 40 * 8356876 * 2
def baseEnd_8356876 : Nat := 4291094158022750917917433

theorem tailTrace_8356876 : CollatzResearch.WordTrace tailWord_8356876 prefixEnd_8356876 4291094158022750917917433 := by
  unfold tailWord_8356876
  simp only [CollatzResearch.WordTrace]
  refine ⟨152400154036236483818733241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203200205381648645091644321 152400154036236483818733241)
  ·
    refine ⟨114300115527177362864049931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152400154036236483818733241 114300115527177362864049931)
    ·
      refine ⟨171450173290766044296074897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114300115527177362864049931 171450173290766044296074897)
      ·
        refine ⟨128587629968074533222056173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171450173290766044296074897 128587629968074533222056173)
        ·
          refine ⟨48220361238027949958271065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128587629968074533222056173 48220361238027949958271065)
          ·
            refine ⟨36165270928520962468703299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48220361238027949958271065 36165270928520962468703299)
            ·
              refine ⟨54247906392781443703054949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36165270928520962468703299 54247906392781443703054949)
              ·
                refine ⟨10171482448646520694322803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54247906392781443703054949 10171482448646520694322803)
                ·
                  refine ⟨15257223672969781041484205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10171482448646520694322803 15257223672969781041484205)
                  ·
                    refine ⟨5721458877363667890556577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15257223672969781041484205 5721458877363667890556577)
                    ·
                      refine ⟨4291094158022750917917433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5721458877363667890556577 4291094158022750917917433)
                      ·
                        rfl

theorem cell23_8356876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_8356876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356876 prefixEnd_8356876 := by exact prefixLift 8356876
  have htrace : WordTrace (prefixWord ++ tailWord_8356876) baseStart_8356876 baseEnd_8356876 := by
    simpa [prefixWord, tailWord_8356876, baseEnd_8356876] using wordTrace_append hprefix tailTrace_8356876
  have hstable : (prefixWord ++ tailWord_8356876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356876).length < 2 ^ (prefixWord ++ tailWord_8356876).sum := by decide
  have hdescent : baseEnd_8356876 < baseStart_8356876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356889 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 1, 4, 2]
def baseStart_8356889 : Nat := 118140960795 + 8356889 * 2 ^ 59
def prefixEnd_8356889 : Nat := 4983230072969 + 3 ^ 40 * 8356889 * 2
def baseEnd_8356889 : Nat := 4291100833271259367054873

theorem tailTrace_8356889 : CollatzResearch.WordTrace tailWord_8356889 prefixEnd_8356889 4291100833271259367054873 := by
  unfold tailWord_8356889
  simp only [CollatzResearch.WordTrace]
  refine ⟨304800782221425870857689721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203200521480950580571793147 304800782221425870857689721)
  ·
    refine ⟨228600586666069403143267291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304800782221425870857689721 228600586666069403143267291)
    ·
      refine ⟨342900879999104104714900937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228600586666069403143267291 342900879999104104714900937)
      ·
        refine ⟨257175659999328078536175703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342900879999104104714900937 257175659999328078536175703)
        ·
          refine ⟨385763489998992117804263555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257175659999328078536175703 385763489998992117804263555)
          ·
            refine ⟨578645234998488176706395333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385763489998992117804263555 578645234998488176706395333)
            ·
              refine ⟨108495981562216533132449125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 578645234998488176706395333 108495981562216533132449125)
              ·
                refine ⟨20342996542915599962334211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108495981562216533132449125 20342996542915599962334211)
                ·
                  refine ⟨30514494814373399943501317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20342996542915599962334211 30514494814373399943501317)
                  ·
                    refine ⟨5721467777695012489406497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30514494814373399943501317 5721467777695012489406497)
                    ·
                      refine ⟨4291100833271259367054873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5721467777695012489406497 4291100833271259367054873)
                      ·
                        rfl

theorem cell23_8356889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 4, 2].length) (baseStart_8356889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356889 prefixEnd_8356889 := by exact prefixLift 8356889
  have htrace : WordTrace (prefixWord ++ tailWord_8356889) baseStart_8356889 baseEnd_8356889 := by
    simpa [prefixWord, tailWord_8356889, baseEnd_8356889] using wordTrace_append hprefix tailTrace_8356889
  have hstable : (prefixWord ++ tailWord_8356889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356889).length < 2 ^ (prefixWord ++ tailWord_8356889).sum := by decide
  have hdescent : baseEnd_8356889 < baseStart_8356889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356952 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_8356952 : Nat := 118140960795 + 8356952 * 2 ^ 59
def prefixEnd_8356952 : Nat := 4983230072969 + 3 ^ 40 * 8356952 * 2
def baseEnd_8356952 : Nat := 4291133182552492620567083

theorem tailTrace_8356952 : CollatzResearch.WordTrace tailWord_8356952 prefixEnd_8356952 4291133182552492620567083 := by
  unfold tailWord_8356952
  simp only [CollatzResearch.WordTrace]
  refine ⟨152401540010098816308616555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203202053346798421744822073 152401540010098816308616555)
  ·
    refine ⟨228602310015148224462924833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152401540010098816308616555 228602310015148224462924833)
    ·
      refine ⟨171451732511361168347193625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228602310015148224462924833 171451732511361168347193625)
      ·
        refine ⟨128588799383520876260395219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171451732511361168347193625 128588799383520876260395219)
        ·
          refine ⟨192883199075281314390592829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128588799383520876260395219 192883199075281314390592829)
          ·
            refine ⟨72331199653230492896472311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192883199075281314390592829 72331199653230492896472311)
            ·
              refine ⟨108496799479845739344708467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72331199653230492896472311 108496799479845739344708467)
              ·
                refine ⟨162745199219768609017062701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108496799479845739344708467 162745199219768609017062701)
                ·
                  refine ⟨61029449707413228381398513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162745199219768609017062701 61029449707413228381398513)
                  ·
                    refine ⟨45772087280559921286048885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61029449707413228381398513 45772087280559921286048885)
                    ·
                      refine ⟨4291133182552492620567083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45772087280559921286048885 4291133182552492620567083)
                      ·
                        rfl

theorem cell23_8356952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_8356952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356952 prefixEnd_8356952 := by exact prefixLift 8356952
  have htrace : WordTrace (prefixWord ++ tailWord_8356952) baseStart_8356952 baseEnd_8356952 := by
    simpa [prefixWord, tailWord_8356952, baseEnd_8356952] using wordTrace_append hprefix tailTrace_8356952
  have hstable : (prefixWord ++ tailWord_8356952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356952).length < 2 ^ (prefixWord ++ tailWord_8356952).sum := by decide
  have hdescent : baseEnd_8356952 < baseStart_8356952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356957 : List Nat := [1, 4, 4, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_8356957 : Nat := 118140960795 + 8356957 * 2 ^ 59
def prefixEnd_8356957 : Nat := 4983230072969 + 3 ^ 40 * 8356957 * 2
def baseEnd_8356957 : Nat := 4291135749955765101004561

theorem tailTrace_8356957 : CollatzResearch.WordTrace tailWord_8356957 prefixEnd_8356957 4291135749955765101004561 := by
  unfold tailWord_8356957
  simp only [CollatzResearch.WordTrace]
  refine ⟨304803262385179518471165125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203202174923453012314110083 304803262385179518471165125)
  ·
    refine ⟨57150611697221159713343461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 304803262385179518471165125 57150611697221159713343461)
    ·
      refine ⟨10715739693228967446251899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57150611697221159713343461 10715739693228967446251899)
      ·
        refine ⟨16073609539843451169377849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10715739693228967446251899 16073609539843451169377849)
        ·
          refine ⟨12055207154882588377033387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16073609539843451169377849 12055207154882588377033387)
          ·
            refine ⟨18082810732323882565550081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12055207154882588377033387 18082810732323882565550081)
            ·
              refine ⟨13562108049242911924162561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18082810732323882565550081 13562108049242911924162561)
              ·
                refine ⟨10171581036932183943121921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13562108049242911924162561 10171581036932183943121921)
                ·
                  refine ⟨7628685777699137957341441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10171581036932183943121921 7628685777699137957341441)
                  ·
                    refine ⟨5721514333274353468006081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7628685777699137957341441 5721514333274353468006081)
                    ·
                      refine ⟨4291135749955765101004561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5721514333274353468006081 4291135749955765101004561)
                      ·
                        rfl

theorem cell23_8356957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_8356957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356957 prefixEnd_8356957 := by exact prefixLift 8356957
  have htrace : WordTrace (prefixWord ++ tailWord_8356957) baseStart_8356957 baseEnd_8356957 := by
    simpa [prefixWord, tailWord_8356957, baseEnd_8356957] using wordTrace_append hprefix tailTrace_8356957
  have hstable : (prefixWord ++ tailWord_8356957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356957).length < 2 ^ (prefixWord ++ tailWord_8356957).sum := by decide
  have hdescent : baseEnd_8356957 < baseStart_8356957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8356996 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_8356996 : Nat := 118140960795 + 8356996 * 2 ^ 59
def prefixEnd_8356996 : Nat := 4983230072969 + 3 ^ 40 * 8356996 * 2
def baseEnd_8356996 : Nat := 4291155775701290448416881

theorem tailTrace_8356996 : CollatzResearch.WordTrace tailWord_8356996 prefixEnd_8356996 4291155775701290448416881 := by
  unfold tailWord_8356996
  simp only [CollatzResearch.WordTrace]
  refine ⟨152402342416019114065917421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203203123221358818754556561 152402342416019114065917421)
  ·
    refine ⟨57150878406007167774719033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152402342416019114065917421 57150878406007167774719033)
    ·
      refine ⟨42863158804505375831039275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57150878406007167774719033 42863158804505375831039275)
      ·
        refine ⟨64294738206758063746558913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42863158804505375831039275 64294738206758063746558913)
        ·
          refine ⟨48221053655068547809919185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64294738206758063746558913 48221053655068547809919185)
          ·
            refine ⟨36165790241301410857439389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48221053655068547809919185 36165790241301410857439389)
            ·
              refine ⟨13562171340488029071539771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36165790241301410857439389 13562171340488029071539771)
              ·
                refine ⟨20343257010732043607309657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13562171340488029071539771 20343257010732043607309657)
                ·
                  refine ⟨15257442758049032705482243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20343257010732043607309657 15257442758049032705482243)
                  ·
                    refine ⟨22886164137073549058223365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15257442758049032705482243 22886164137073549058223365)
                    ·
                      refine ⟨4291155775701290448416881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22886164137073549058223365 4291155775701290448416881)
                      ·
                        rfl

theorem cell23_8356996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_8356996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8356996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8356996 prefixEnd_8356996 := by exact prefixLift 8356996
  have htrace : WordTrace (prefixWord ++ tailWord_8356996) baseStart_8356996 baseEnd_8356996 := by
    simpa [prefixWord, tailWord_8356996, baseEnd_8356996] using wordTrace_append hprefix tailTrace_8356996
  have hstable : (prefixWord ++ tailWord_8356996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8356996).length < 2 ^ (prefixWord ++ tailWord_8356996).sum := by decide
  have hdescent : baseEnd_8356996 < baseStart_8356996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8356996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357023 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 3, 4]
def baseStart_8357023 : Nat := 118140960795 + 8357023 * 2 ^ 59
def prefixEnd_8357023 : Nat := 4983230072969 + 3 ^ 40 * 8357023 * 2
def baseEnd_8357023 : Nat := 1430389879892987280926419

theorem tailTrace_8357023 : CollatzResearch.WordTrace tailWord_8357023 prefixEnd_8357023 1430389879892987280926419 := by
  unfold tailWord_8357023
  simp only [CollatzResearch.WordTrace]
  refine ⟨304805669602940411743067723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203203779735293607828711815 304805669602940411743067723)
  ·
    refine ⟨457208504404410617614601585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304805669602940411743067723 457208504404410617614601585)
    ·
      refine ⟨342906378303307963210951189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457208504404410617614601585 342906378303307963210951189)
      ·
        refine ⟨16073736482967560775513337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 342906378303307963210951189 16073736482967560775513337)
        ·
          refine ⟨12055302362225670581635003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16073736482967560775513337 12055302362225670581635003)
          ·
            refine ⟨18082953543338505872452505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12055302362225670581635003 18082953543338505872452505)
            ·
              refine ⟨13562215157503879404339379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18082953543338505872452505 13562215157503879404339379)
              ·
                refine ⟨20343322736255819106509069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13562215157503879404339379 20343322736255819106509069)
                ·
                  refine ⟨7628746026095932164940901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20343322736255819106509069 7628746026095932164940901)
                  ·
                    refine ⟨1430389879892987280926419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7628746026095932164940901 1430389879892987280926419)
                    ·
                      rfl

theorem cell23_8357023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 4].length) (baseStart_8357023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357023 prefixEnd_8357023 := by exact prefixLift 8357023
  have htrace : WordTrace (prefixWord ++ tailWord_8357023) baseStart_8357023 baseEnd_8357023 := by
    simpa [prefixWord, tailWord_8357023, baseEnd_8357023] using wordTrace_append hprefix tailTrace_8357023
  have hstable : (prefixWord ++ tailWord_8357023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357023).length < 2 ^ (prefixWord ++ tailWord_8357023).sum := by decide
  have hdescent : baseEnd_8357023 < baseStart_8357023 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357057 : List Nat := [1, 2, 6, 1, 1, 3, 1, 3, 1, 4]
def baseStart_8357057 : Nat := 118140960795 + 8357057 * 2 ^ 59
def prefixEnd_8357057 : Nat := 4983230072969 + 3 ^ 40 * 8357057 * 2
def baseEnd_8357057 : Nat := 1430395699340404903251367

theorem tailTrace_8357057 : CollatzResearch.WordTrace tailWord_8357057 prefixEnd_8357057 1430395699340404903251367 := by
  unfold tailWord_8357057
  simp only [CollatzResearch.WordTrace]
  refine ⟨304806909684817235549805425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203204606456544823699870283 304806909684817235549805425)
  ·
    refine ⟨228605182263612926662354069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304806909684817235549805425 228605182263612926662354069)
    ·
      refine ⟨10715867918606855937297847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228605182263612926662354069 10715867918606855937297847)
      ·
        refine ⟨16073801877910283905946771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10715867918606855937297847 16073801877910283905946771)
        ·
          refine ⟨24110702816865425858920157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16073801877910283905946771 24110702816865425858920157)
          ·
            refine ⟨9041513556324534697095059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24110702816865425858920157 9041513556324534697095059)
            ·
              refine ⟨13562270334486802045642589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9041513556324534697095059 13562270334486802045642589)
              ·
                refine ⟨5085851375432550767115971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13562270334486802045642589 5085851375432550767115971)
                ·
                  refine ⟨7628777063148826150673957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5085851375432550767115971 7628777063148826150673957)
                  ·
                    refine ⟨1430395699340404903251367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7628777063148826150673957 1430395699340404903251367)
                    ·
                      rfl

theorem cell23_8357057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_8357057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357057 prefixEnd_8357057 := by exact prefixLift 8357057
  have htrace : WordTrace (prefixWord ++ tailWord_8357057) baseStart_8357057 baseEnd_8357057 := by
    simpa [prefixWord, tailWord_8357057, baseEnd_8357057] using wordTrace_append hprefix tailTrace_8357057
  have hstable : (prefixWord ++ tailWord_8357057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357057).length < 2 ^ (prefixWord ++ tailWord_8357057).sum := by decide
  have hdescent : baseEnd_8357057 < baseStart_8357057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357066 : List Nat := [3, 1, 2, 1, 3, 2, 2, 3, 1, 5]
def baseStart_8357066 : Nat := 118140960795 + 8357066 * 2 ^ 59
def prefixEnd_8357066 : Nat := 4983230072969 + 3 ^ 40 * 8357066 * 2
def baseEnd_8357066 : Nat := 1430397239782368391513853

theorem tailTrace_8357066 : CollatzResearch.WordTrace tailWord_8357066 prefixEnd_8357066 1430397239782368391513853 := by
  unfold tailWord_8357066
  simp only [CollatzResearch.WordTrace]
  refine ⟨76201809485446157521720763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203204825294523086724588701 76201809485446157521720763)
  ·
    refine ⟨114302714228169236282581145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76201809485446157521720763 114302714228169236282581145)
    ·
      refine ⟨85727035671126927211935859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114302714228169236282581145 85727035671126927211935859)
      ·
        refine ⟨128590553506690390817903789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85727035671126927211935859 128590553506690390817903789)
        ·
          refine ⟨48221457565008896556713921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128590553506690390817903789 48221457565008896556713921)
          ·
            refine ⟨36166093173756672417535441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48221457565008896556713921 36166093173756672417535441)
            ·
              refine ⟨27124569880317504313151581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36166093173756672417535441 27124569880317504313151581)
              ·
                refine ⟨10171713705119064117431843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27124569880317504313151581 10171713705119064117431843)
                ·
                  refine ⟨15257570557678596176147765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10171713705119064117431843 15257570557678596176147765)
                  ·
                    refine ⟨1430397239782368391513853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15257570557678596176147765 1430397239782368391513853)
                    ·
                      rfl

theorem cell23_8357066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_8357066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357066 prefixEnd_8357066 := by exact prefixLift 8357066
  have htrace : WordTrace (prefixWord ++ tailWord_8357066) baseStart_8357066 baseEnd_8357066 := by
    simpa [prefixWord, tailWord_8357066, baseEnd_8357066] using wordTrace_append hprefix tailTrace_8357066
  have hstable : (prefixWord ++ tailWord_8357066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357066).length < 2 ^ (prefixWord ++ tailWord_8357066).sum := by decide
  have hdescent : baseEnd_8357066 < baseStart_8357066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357080 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 3, 1, 3]
def baseStart_8357080 : Nat := 118140960795 + 8357080 * 2 ^ 59
def prefixEnd_8357080 : Nat := 4983230072969 + 3 ^ 40 * 8357080 * 2
def baseEnd_8357080 : Nat := 4291198908076268119766495

theorem tailTrace_8357080 : CollatzResearch.WordTrace tailWord_8357080 prefixEnd_8357080 4291198908076268119766495 := by
  unfold tailWord_8357080
  simp only [CollatzResearch.WordTrace]
  refine ⟨152403874281866955238946347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203205165709155940318595129 152403874281866955238946347)
  ·
    refine ⟨228605811422800432858419521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152403874281866955238946347 228605811422800432858419521)
    ·
      refine ⟨171454358567100324643814641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228605811422800432858419521 171454358567100324643814641)
      ·
        refine ⟨128590768925325243482860981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171454358567100324643814641 128590768925325243482860981)
        ·
          refine ⟨12055384586749241576518217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128590768925325243482860981 12055384586749241576518217)
          ·
            refine ⟨9041538440061931182388663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12055384586749241576518217 9041538440061931182388663)
            ·
              refine ⟨13562307660092896773582995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9041538440061931182388663 13562307660092896773582995)
              ·
                refine ⟨20343461490139345160374493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13562307660092896773582995 20343461490139345160374493)
                ·
                  refine ⟨7628798058802254435140435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20343461490139345160374493 7628798058802254435140435)
                  ·
                    refine ⟨11443197088203381652710653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7628798058802254435140435 11443197088203381652710653)
                    ·
                      refine ⟨4291198908076268119766495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11443197088203381652710653 4291198908076268119766495)
                      ·
                        rfl

theorem cell23_8357080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_8357080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357080 prefixEnd_8357080 := by exact prefixLift 8357080
  have htrace : WordTrace (prefixWord ++ tailWord_8357080) baseStart_8357080 baseEnd_8357080 := by
    simpa [prefixWord, tailWord_8357080, baseEnd_8357080] using wordTrace_append hprefix tailTrace_8357080
  have hstable : (prefixWord ++ tailWord_8357080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357080).length < 2 ^ (prefixWord ++ tailWord_8357080).sum := by decide
  have hdescent : baseEnd_8357080 < baseStart_8357080 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357099 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 6]
def baseStart_8357099 : Nat := 118140960795 + 8357099 * 2 ^ 59
def prefixEnd_8357099 : Nat := 4983230072969 + 3 ^ 40 * 8357099 * 2
def baseEnd_8357099 : Nat := 4291208664208703545428907

theorem tailTrace_8357099 : CollatzResearch.WordTrace tailWord_8357099 prefixEnd_8357099 4291208664208703545428907 := by
  unfold tailWord_8357099
  simp only [CollatzResearch.WordTrace]
  refine ⟨304808441550665076722834351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203205627700443384481889567 304808441550665076722834351)
  ·
    refine ⟨457212662325997615084251527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304808441550665076722834351 457212662325997615084251527)
    ·
      refine ⟨685818993488996422626377291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457212662325997615084251527 685818993488996422626377291)
      ·
        refine ⟨1028728490233494633939565937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685818993488996422626377291 1028728490233494633939565937)
        ·
          refine ⟨771546367675120975454674453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1028728490233494633939565937 771546367675120975454674453)
          ·
            refine ⟨36166235984771295724437865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 771546367675120975454674453 36166235984771295724437865)
            ·
              refine ⟨27124676988578471793328399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36166235984771295724437865 27124676988578471793328399)
              ·
                refine ⟨40687015482867707689992599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27124676988578471793328399 40687015482867707689992599)
                ·
                  refine ⟨61030523224301561534988899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40687015482867707689992599 61030523224301561534988899)
                  ·
                    refine ⟨91545784836452342302483349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61030523224301561534988899 91545784836452342302483349)
                    ·
                      refine ⟨4291208664208703545428907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91545784836452342302483349 4291208664208703545428907)
                      ·
                        rfl

theorem cell23_8357099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 6].length) (baseStart_8357099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357099 prefixEnd_8357099 := by exact prefixLift 8357099
  have htrace : WordTrace (prefixWord ++ tailWord_8357099) baseStart_8357099 baseEnd_8357099 := by
    simpa [prefixWord, tailWord_8357099, baseEnd_8357099] using wordTrace_append hprefix tailTrace_8357099
  have hstable : (prefixWord ++ tailWord_8357099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357099).length < 2 ^ (prefixWord ++ tailWord_8357099).sum := by decide
  have hdescent : baseEnd_8357099 < baseStart_8357099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357120 : List Nat := [2, 1, 1, 2, 1, 1, 3, 7, 1, 2, 2]
def baseStart_8357120 : Nat := 118140960795 + 8357120 * 2 ^ 59
def prefixEnd_8357120 : Nat := 4983230072969 + 3 ^ 40 * 8357120 * 2
def baseEnd_8357120 : Nat := 4291219447302447963266311

theorem tailTrace_8357120 : CollatzResearch.WordTrace tailWord_8357120 prefixEnd_8357120 4291219447302447963266311 := by
  unfold tailWord_8357120
  simp only [CollatzResearch.WordTrace]
  refine ⟨152404603741794498654674407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203206138322392664872899209 152404603741794498654674407)
  ·
    refine ⟨228606905612691747982011611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152404603741794498654674407 228606905612691747982011611)
    ·
      refine ⟨342910358419037621973017417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228606905612691747982011611 342910358419037621973017417)
      ·
        refine ⟨257182768814278216479763063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342910358419037621973017417 257182768814278216479763063)
        ·
          refine ⟨385774153221417324719644595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257182768814278216479763063 385774153221417324719644595)
          ·
            refine ⟨578661229832125987079466893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385774153221417324719644595 578661229832125987079466893)
            ·
              refine ⟨216997961187047245154800085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 578661229832125987079466893 216997961187047245154800085)
              ·
                refine ⟨5085889715321419808315627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 216997961187047245154800085 5085889715321419808315627)
                ·
                  refine ⟨7628834572982129712473441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5085889715321419808315627 7628834572982129712473441)
                  ·
                    refine ⟨5721625929736597284355081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7628834572982129712473441 5721625929736597284355081)
                    ·
                      refine ⟨4291219447302447963266311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5721625929736597284355081 4291219447302447963266311)
                      ·
                        rfl

theorem cell23_8357120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 1, 2, 2].length) (baseStart_8357120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357120 prefixEnd_8357120 := by exact prefixLift 8357120
  have htrace : WordTrace (prefixWord ++ tailWord_8357120) baseStart_8357120 baseEnd_8357120 := by
    simpa [prefixWord, tailWord_8357120, baseEnd_8357120] using wordTrace_append hprefix tailTrace_8357120
  have hstable : (prefixWord ++ tailWord_8357120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357120).length < 2 ^ (prefixWord ++ tailWord_8357120).sum := by decide
  have hdescent : baseEnd_8357120 < baseStart_8357120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357126 : List Nat := [6, 2, 15]
def baseStart_8357126 : Nat := 118140960795 + 8357126 * 2 ^ 59
def prefixEnd_8357126 : Nat := 4983230072969 + 3 ^ 40 * 8357126 * 2
def baseEnd_8357126 : Nat := 654050072883154235603

theorem tailTrace_8357126 : CollatzResearch.WordTrace tailWord_8357126 prefixEnd_8357126 654050072883154235603 := by
  unfold tailWord_8357126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9525294572548976885439601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203206284214378173556044821 9525294572548976885439601)
  ·
    refine ⟨7143970929411732664079701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9525294572548976885439601 7143970929411732664079701)
    ·
      refine ⟨654050072883154235603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 7143970929411732664079701 654050072883154235603)
      ·
        rfl

theorem cell23_8357126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 15].length) (baseStart_8357126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357126 prefixEnd_8357126 := by exact prefixLift 8357126
  have htrace : WordTrace (prefixWord ++ tailWord_8357126) baseStart_8357126 baseEnd_8357126 := by
    simpa [prefixWord, tailWord_8357126, baseEnd_8357126] using wordTrace_append hprefix tailTrace_8357126
  have hstable : (prefixWord ++ tailWord_8357126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357126).length < 2 ^ (prefixWord ++ tailWord_8357126).sum := by decide
  have hdescent : baseEnd_8357126 < baseStart_8357126 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357136 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 10, 1, 3]
def baseStart_8357136 : Nat := 118140960795 + 8357136 * 2 ^ 59
def prefixEnd_8357136 : Nat := 4983230072969 + 3 ^ 40 * 8357136 * 2
def baseEnd_8357136 : Nat := 4291227662992919900666237

theorem tailTrace_8357136 : CollatzResearch.WordTrace tailWord_8357136 prefixEnd_8357136 4291227662992919900666237 := by
  unfold tailWord_8357136
  simp only [CollatzResearch.WordTrace]
  refine ⟨152404895525765516020965631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203206527367687354694620841 152404895525765516020965631)
  ·
    refine ⟨228607343288648274031448447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152404895525765516020965631 228607343288648274031448447)
    ·
      refine ⟨342911014932972411047172671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228607343288648274031448447 342911014932972411047172671)
      ·
        refine ⟨514366522399458616570759007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342911014932972411047172671 514366522399458616570759007)
        ·
          refine ⟨771549783599187924856138511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514366522399458616570759007 771549783599187924856138511)
          ·
            refine ⟨1157324675398781887284207767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771549783599187924856138511 1157324675398781887284207767)
            ·
              refine ⟨1735987013098172830926311651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1157324675398781887284207767 1735987013098172830926311651)
              ·
                refine ⟨2603980519647259246389467477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1735987013098172830926311651 2603980519647259246389467477)
                ·
                  refine ⟨7628849178654079823406643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 2603980519647259246389467477 7628849178654079823406643)
                  ·
                    refine ⟨11443273767981119735109965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7628849178654079823406643 11443273767981119735109965)
                    ·
                      refine ⟨4291227662992919900666237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11443273767981119735109965 4291227662992919900666237)
                      ·
                        rfl

theorem cell23_8357136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 10, 1, 3].length) (baseStart_8357136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357136 prefixEnd_8357136 := by exact prefixLift 8357136
  have htrace : WordTrace (prefixWord ++ tailWord_8357136) baseStart_8357136 baseEnd_8357136 := by
    simpa [prefixWord, tailWord_8357136, baseEnd_8357136] using wordTrace_append hprefix tailTrace_8357136
  have hstable : (prefixWord ++ tailWord_8357136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357136).length < 2 ^ (prefixWord ++ tailWord_8357136).sum := by decide
  have hdescent : baseEnd_8357136 < baseStart_8357136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357179 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 5]
def baseStart_8357179 : Nat := 118140960795 + 8357179 * 2 ^ 59
def prefixEnd_8357179 : Nat := 4983230072969 + 3 ^ 40 * 8357179 * 2
def baseEnd_8357179 : Nat := 4291249742661063232428539

theorem tailTrace_8357179 : CollatzResearch.WordTrace tailWord_8357179 prefixEnd_8357179 4291249742661063232428539 := by
  unfold tailWord_8357179
  simp only [CollatzResearch.WordTrace]
  refine ⟨304811359390375250385746591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203207572926916833590497727 304811359390375250385746591)
  ·
    refine ⟨457217039085562875578619887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304811359390375250385746591 457217039085562875578619887)
    ·
      refine ⟨685825558628344313367929831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457217039085562875578619887 685825558628344313367929831)
      ·
        refine ⟨1028738337942516470051894747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685825558628344313367929831 1028738337942516470051894747)
        ·
          refine ⟨1543107506913774705077842121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028738337942516470051894747 1543107506913774705077842121)
          ·
            refine ⟨1157330630185331028808381591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1543107506913774705077842121 1157330630185331028808381591)
            ·
              refine ⟨1735995945277996543212572387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1157330630185331028808381591 1735995945277996543212572387)
              ·
                refine ⟨2603993917916994814818858581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1735995945277996543212572387 2603993917916994814818858581)
                ·
                  refine ⟨30515553725589782986158499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2603993917916994814818858581 30515553725589782986158499)
                  ·
                    refine ⟨45773330588384674479237749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30515553725589782986158499 45773330588384674479237749)
                    ·
                      refine ⟨4291249742661063232428539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45773330588384674479237749 4291249742661063232428539)
                      ·
                        rfl

theorem cell23_8357179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 5].length) (baseStart_8357179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357179 prefixEnd_8357179 := by exact prefixLift 8357179
  have htrace : WordTrace (prefixWord ++ tailWord_8357179) baseStart_8357179 baseEnd_8357179 := by
    simpa [prefixWord, tailWord_8357179, baseEnd_8357179] using wordTrace_append hprefix tailTrace_8357179
  have hstable : (prefixWord ++ tailWord_8357179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357179).length < 2 ^ (prefixWord ++ tailWord_8357179).sum := by decide
  have hdescent : baseEnd_8357179 < baseStart_8357179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357180 : List Nat := [2, 2, 2, 2, 1, 4, 1, 3, 1, 3, 2]
def baseStart_8357180 : Nat := 118140960795 + 8357180 * 2 ^ 59
def prefixEnd_8357180 : Nat := 4983230072969 + 3 ^ 40 * 8357180 * 2
def baseEnd_8357180 : Nat := 4291250256141717728516035

theorem tailTrace_8357180 : CollatzResearch.WordTrace tailWord_8357180 prefixEnd_8357180 4291250256141717728516035 := by
  unfold tailWord_8357180
  simp only [CollatzResearch.WordTrace]
  refine ⟨152405697931685813778266497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203207597242247751704355329 152405697931685813778266497)
  ·
    refine ⟨114304273448764360333699873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152405697931685813778266497 114304273448764360333699873)
    ·
      refine ⟨85728205086573270250274905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114304273448764360333699873 85728205086573270250274905)
      ·
        refine ⟨64296153814929952687706179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85728205086573270250274905 64296153814929952687706179)
        ·
          refine ⟨96444230722394929031559269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64296153814929952687706179 96444230722394929031559269)
          ·
            refine ⟨18083293260449049193417363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96444230722394929031559269 18083293260449049193417363)
            ·
              refine ⟨27124939890673573790126045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18083293260449049193417363 27124939890673573790126045)
              ·
                refine ⟨10171852459002590171297267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27124939890673573790126045 10171852459002590171297267)
                ·
                  refine ⟨15257778688503885256945901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10171852459002590171297267 15257778688503885256945901)
                  ·
                    refine ⟨5721667008188956971354713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15257778688503885256945901 5721667008188956971354713)
                    ·
                      refine ⟨4291250256141717728516035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5721667008188956971354713 4291250256141717728516035)
                      ·
                        rfl

theorem cell23_8357180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_8357180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357180 prefixEnd_8357180 := by exact prefixLift 8357180
  have htrace : WordTrace (prefixWord ++ tailWord_8357180) baseStart_8357180 baseEnd_8357180 := by
    simpa [prefixWord, tailWord_8357180, baseEnd_8357180] using wordTrace_append hprefix tailTrace_8357180
  have hstable : (prefixWord ++ tailWord_8357180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357180).length < 2 ^ (prefixWord ++ tailWord_8357180).sum := by decide
  have hdescent : baseEnd_8357180 < baseStart_8357180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357210 : List Nat := [3, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2]
def baseStart_8357210 : Nat := 118140960795 + 8357210 * 2 ^ 59
def prefixEnd_8357210 : Nat := 4983230072969 + 3 ^ 40 * 8357210 * 2
def baseEnd_8357210 : Nat := 4291265660561352611140897

theorem tailTrace_8357210 : CollatzResearch.WordTrace tailWord_8357210 prefixEnd_8357210 4291265660561352611140897 := by
  unfold tailWord_8357210
  simp only [CollatzResearch.WordTrace]
  refine ⟨76203122513315735670031271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203208326702175295120083389 76203122513315735670031271)
  ·
    refine ⟨114304683769973603505046907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76203122513315735670031271 114304683769973603505046907)
    ·
      refine ⟨171457025654960405257570361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114304683769973603505046907 171457025654960405257570361)
      ·
        refine ⟨128592769241220303943177771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171457025654960405257570361 128592769241220303943177771)
        ·
          refine ⟨192889153861830455914766657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128592769241220303943177771 192889153861830455914766657)
          ·
            refine ⟨144666865396372841936074993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192889153861830455914766657 144666865396372841936074993)
            ·
              refine ⟨108500149047279631452056245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144666865396372841936074993 108500149047279631452056245)
              ·
                refine ⟨10171888973182465448630273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108500149047279631452056245 10171888973182465448630273)
                ·
                  refine ⟨7628916729886849086472705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10171888973182465448630273 7628916729886849086472705)
                  ·
                    refine ⟨5721687547415136814854529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7628916729886849086472705 5721687547415136814854529)
                    ·
                      refine ⟨4291265660561352611140897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5721687547415136814854529 4291265660561352611140897)
                      ·
                        rfl

theorem cell23_8357210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_8357210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357210 prefixEnd_8357210 := by exact prefixLift 8357210
  have htrace : WordTrace (prefixWord ++ tailWord_8357210) baseStart_8357210 baseEnd_8357210 := by
    simpa [prefixWord, tailWord_8357210, baseEnd_8357210] using wordTrace_append hprefix tailTrace_8357210
  have hstable : (prefixWord ++ tailWord_8357210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357210).length < 2 ^ (prefixWord ++ tailWord_8357210).sum := by decide
  have hdescent : baseEnd_8357210 < baseStart_8357210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357216 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 7]
def baseStart_8357216 : Nat := 118140960795 + 8357216 * 2 ^ 59
def prefixEnd_8357216 : Nat := 4983230072969 + 3 ^ 40 * 8357216 * 2
def baseEnd_8357216 : Nat := 476807637938364398629541

theorem tailTrace_8357216 : CollatzResearch.WordTrace tailWord_8357216 prefixEnd_8357216 476807637938364398629541 := by
  unfold tailWord_8357216
  simp only [CollatzResearch.WordTrace]
  refine ⟨152406354445620602852421751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203208472594160803803229001 152406354445620602852421751)
  ·
    refine ⟨228609531668430904278632627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152406354445620602852421751 228609531668430904278632627)
    ·
      refine ⟨342914297502646356417948941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228609531668430904278632627 342914297502646356417948941)
      ·
        refine ⟨128592861563492383656730853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342914297502646356417948941 128592861563492383656730853)
        ·
          refine ⟨24111161543154821935637035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128592861563492383656730853 24111161543154821935637035)
          ·
            refine ⟨36166742314732232903455553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24111161543154821935637035 36166742314732232903455553)
            ·
              refine ⟨27125056736049174677591665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36166742314732232903455553 27125056736049174677591665)
              ·
                refine ⟨20343792552036881008193749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27125056736049174677591665 20343792552036881008193749)
                ·
                  refine ⟨476807637938364398629541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20343792552036881008193749 476807637938364398629541)
                  ·
                    rfl

theorem cell23_8357216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 7].length) (baseStart_8357216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357216 prefixEnd_8357216 := by exact prefixLift 8357216
  have htrace : WordTrace (prefixWord ++ tailWord_8357216) baseStart_8357216 baseEnd_8357216 := by
    simpa [prefixWord, tailWord_8357216, baseEnd_8357216] using wordTrace_append hprefix tailTrace_8357216
  have hstable : (prefixWord ++ tailWord_8357216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357216).length < 2 ^ (prefixWord ++ tailWord_8357216).sum := by decide
  have hdescent : baseEnd_8357216 < baseStart_8357216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357230 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_8357230 : Nat := 118140960795 + 8357230 * 2 ^ 59
def prefixEnd_8357230 : Nat := 4983230072969 + 3 ^ 40 * 8357230 * 2
def baseEnd_8357230 : Nat := 4291275930174442532890805

theorem tailTrace_8357230 : CollatzResearch.WordTrace tailWord_8357230 prefixEnd_8357230 4291275930174442532890805 := by
  unfold tailWord_8357230
  simp only [CollatzResearch.WordTrace]
  refine ⟨38101652439148810761981643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203208813008793657397235429 38101652439148810761981643)
  ·
    refine ⟨57152478658723216142972465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38101652439148810761981643 57152478658723216142972465)
    ·
      refine ⟨42864358994042412107229349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57152478658723216142972465 42864358994042412107229349)
      ·
        refine ⟨8037067311382952270105503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42864358994042412107229349 8037067311382952270105503)
        ·
          refine ⟨12055600967074428405158255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037067311382952270105503 12055600967074428405158255)
          ·
            refine ⟨18083401450611642607737383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12055600967074428405158255 18083401450611642607737383)
            ·
              refine ⟨27125102175917463911606075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18083401450611642607737383 27125102175917463911606075)
              ·
                refine ⟨40687653263876195867409113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27125102175917463911606075 40687653263876195867409113)
                ·
                  refine ⟨30515739947907146900556835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40687653263876195867409113 30515739947907146900556835)
                  ·
                    refine ⟨45773609921860720350835253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30515739947907146900556835 45773609921860720350835253)
                    ·
                      refine ⟨4291275930174442532890805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45773609921860720350835253 4291275930174442532890805)
                      ·
                        rfl

theorem cell23_8357230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_8357230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357230 prefixEnd_8357230 := by exact prefixLift 8357230
  have htrace : WordTrace (prefixWord ++ tailWord_8357230) baseStart_8357230 baseEnd_8357230 := by
    simpa [prefixWord, tailWord_8357230, baseEnd_8357230] using wordTrace_append hprefix tailTrace_8357230
  have hstable : (prefixWord ++ tailWord_8357230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357230).length < 2 ^ (prefixWord ++ tailWord_8357230).sum := by decide
  have hdescent : baseEnd_8357230 < baseStart_8357230 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357233 : List Nat := [1, 2, 2, 2, 1, 2, 5, 3, 5]
def baseStart_8357233 : Nat := 118140960795 + 8357233 * 2 ^ 59
def prefixEnd_8357233 : Nat := 4983230072969 + 3 ^ 40 * 8357233 * 2
def baseEnd_8357233 : Nat := 476808607846267335683699

theorem tailTrace_8357233 : CollatzResearch.WordTrace tailWord_8357233 prefixEnd_8357233 476808607846267335683699 := by
  unfold tailWord_8357233
  simp only [CollatzResearch.WordTrace]
  refine ⟨304813328932179617608212353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203208885954786411738808235 304813328932179617608212353)
  ·
    refine ⟨228609996699134713206159265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304813328932179617608212353 228609996699134713206159265)
    ·
      refine ⟨171457497524351034904619449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228609996699134713206159265 171457497524351034904619449)
      ·
        refine ⟨128593123143263276178464587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171457497524351034904619449 128593123143263276178464587)
        ·
          refine ⟨192889684714894914267696881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128593123143263276178464587 192889684714894914267696881)
          ·
            refine ⟨144667263536171185700772661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192889684714894914267696881 144667263536171185700772661)
            ·
              refine ⟨13562555956516048659447437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144667263536171185700772661 13562555956516048659447437)
              ·
                refine ⟨5085958483693518247292789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13562555956516048659447437 5085958483693518247292789)
                ·
                  refine ⟨476808607846267335683699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5085958483693518247292789 476808607846267335683699)
                  ·
                    rfl

theorem cell23_8357233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 5].length) (baseStart_8357233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357233 prefixEnd_8357233 := by exact prefixLift 8357233
  have htrace : WordTrace (prefixWord ++ tailWord_8357233) baseStart_8357233 baseEnd_8357233 := by
    simpa [prefixWord, tailWord_8357233, baseEnd_8357233] using wordTrace_append hprefix tailTrace_8357233
  have hstable : (prefixWord ++ tailWord_8357233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357233).length < 2 ^ (prefixWord ++ tailWord_8357233).sum := by decide
  have hdescent : baseEnd_8357233 < baseStart_8357233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357250 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 7]
def baseStart_8357250 : Nat := 118140960795 + 8357250 * 2 ^ 59
def prefixEnd_8357250 : Nat := 4983230072969 + 3 ^ 40 * 8357250 * 2
def baseEnd_8357250 : Nat := 476809577754170272737857

theorem tailTrace_8357250 : CollatzResearch.WordTrace tailWord_8357250 prefixEnd_8357250 476809577754170272737857 := by
  unfold tailWord_8357250
  simp only [CollatzResearch.WordTrace]
  refine ⟨76203487243279507377895301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203209299315412019674387469 76203487243279507377895301)
  ·
    refine ⟨14288153858114907633355369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76203487243279507377895301 14288153858114907633355369)
    ·
      refine ⟨10716115393586180725016527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14288153858114907633355369 10716115393586180725016527)
      ·
        refine ⟨16074173090379271087524791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10716115393586180725016527 16074173090379271087524791)
        ·
          refine ⟨24111259635568906631287187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16074173090379271087524791 24111259635568906631287187)
          ·
            refine ⟨36166889453353359946930781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24111259635568906631287187 36166889453353359946930781)
            ·
              refine ⟨13562583545007509980099043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36166889453353359946930781 13562583545007509980099043)
              ·
                refine ⟨20343875317511264970148565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13562583545007509980099043 20343875317511264970148565)
                ·
                  refine ⟨476809577754170272737857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20343875317511264970148565 476809577754170272737857)
                  ·
                    rfl

theorem cell23_8357250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_8357250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357250 prefixEnd_8357250 := by exact prefixLift 8357250
  have htrace : WordTrace (prefixWord ++ tailWord_8357250) baseStart_8357250 baseEnd_8357250 := by
    simpa [prefixWord, tailWord_8357250, baseEnd_8357250] using wordTrace_append hprefix tailTrace_8357250
  have hstable : (prefixWord ++ tailWord_8357250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357250).length < 2 ^ (prefixWord ++ tailWord_8357250).sum := by decide
  have hdescent : baseEnd_8357250 < baseStart_8357250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357256 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_8357256 : Nat := 118140960795 + 8357256 * 2 ^ 59
def prefixEnd_8357256 : Nat := 4983230072969 + 3 ^ 40 * 8357256 * 2
def baseEnd_8357256 : Nat := 4291289280671459431165685

theorem tailTrace_8357256 : CollatzResearch.WordTrace tailWord_8357256 prefixEnd_8357256 4291289280671459431165685 := by
  unfold tailWord_8357256
  simp only [CollatzResearch.WordTrace]
  refine ⟨152407083905548146268149811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203209445207397528357533081 152407083905548146268149811)
  ·
    refine ⟨228610625858322219402224717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152407083905548146268149811 228610625858322219402224717)
    ·
      refine ⟨85728984696870832275834269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228610625858322219402224717 85728984696870832275834269)
      ·
        refine ⟨32148369261326562103437851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85728984696870832275834269 32148369261326562103437851)
        ·
          refine ⟨48222553891989843155156777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32148369261326562103437851 48222553891989843155156777)
          ·
            refine ⟨36166915418992382366367583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48222553891989843155156777 36166915418992382366367583)
            ·
              refine ⟨54250373128488573549551375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36166915418992382366367583 54250373128488573549551375)
              ·
                refine ⟨81375559692732860324327063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54250373128488573549551375 81375559692732860324327063)
                ·
                  refine ⟨122063339539099290486490595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81375559692732860324327063 122063339539099290486490595)
                  ·
                    refine ⟨183095009308648935729735893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122063339539099290486490595 183095009308648935729735893)
                    ·
                      refine ⟨4291289280671459431165685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183095009308648935729735893 4291289280671459431165685)
                      ·
                        rfl

theorem cell23_8357256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_8357256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357256 prefixEnd_8357256 := by exact prefixLift 8357256
  have htrace : WordTrace (prefixWord ++ tailWord_8357256) baseStart_8357256 baseEnd_8357256 := by
    simpa [prefixWord, tailWord_8357256, baseEnd_8357256] using wordTrace_append hprefix tailTrace_8357256
  have hstable : (prefixWord ++ tailWord_8357256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357256).length < 2 ^ (prefixWord ++ tailWord_8357256).sum := by decide
  have hdescent : baseEnd_8357256 < baseStart_8357256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357283 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 4]
def baseStart_8357283 : Nat := 118140960795 + 8357283 * 2 ^ 59
def prefixEnd_8357283 : Nat := 4983230072969 + 3 ^ 40 * 8357283 * 2
def baseEnd_8357283 : Nat := 4291303144649130825528061

theorem tailTrace_8357283 : CollatzResearch.WordTrace tailWord_8357283 prefixEnd_8357283 4291303144649130825528061 := by
  unfold tailWord_8357283
  simp only [CollatzResearch.WordTrace]
  refine ⟨304815152581998476147532503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203210101721332317431688335 304815152581998476147532503)
  ·
    refine ⟨457222728872997714221298755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304815152581998476147532503 457222728872997714221298755)
    ·
      refine ⟨685834093309496571331948133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457222728872997714221298755 685834093309496571331948133)
      ·
        refine ⟨128593892495530607124740275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 685834093309496571331948133 128593892495530607124740275)
        ·
          refine ⟨192890838743295910687110413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128593892495530607124740275 192890838743295910687110413)
          ·
            refine ⟨72334064528735966507666405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192890838743295910687110413 72334064528735966507666405)
            ·
              refine ⟨13562637099137993720187451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72334064528735966507666405 13562637099137993720187451)
              ·
                refine ⟨20343955648706990580281177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13562637099137993720187451 20343955648706990580281177)
                ·
                  refine ⟨15257966736530242935210883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20343955648706990580281177 15257966736530242935210883)
                  ·
                    refine ⟨22886950104795364402816325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15257966736530242935210883 22886950104795364402816325)
                    ·
                      refine ⟨4291303144649130825528061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22886950104795364402816325 4291303144649130825528061)
                      ·
                        rfl

theorem cell23_8357283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_8357283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357283 prefixEnd_8357283 := by exact prefixLift 8357283
  have htrace : WordTrace (prefixWord ++ tailWord_8357283) baseStart_8357283 baseEnd_8357283 := by
    simpa [prefixWord, tailWord_8357283, baseEnd_8357283] using wordTrace_append hprefix tailTrace_8357283
  have hstable : (prefixWord ++ tailWord_8357283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357283).length < 2 ^ (prefixWord ++ tailWord_8357283).sum := by decide
  have hdescent : baseEnd_8357283 < baseStart_8357283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357303 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 3]
def baseStart_8357303 : Nat := 118140960795 + 8357303 * 2 ^ 59
def prefixEnd_8357303 : Nat := 4983230072969 + 3 ^ 40 * 8357303 * 2
def baseEnd_8357303 : Nat := 4291313414262220747277969

theorem tailTrace_8357303 : CollatzResearch.WordTrace tailWord_8357303 prefixEnd_8357303 4291313414262220747277969 := by
  unfold tailWord_8357303
  simp only [CollatzResearch.WordTrace]
  refine ⟨304815882041926019563260563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203210588027950679708840375 304815882041926019563260563)
  ·
    refine ⟨457223823062889029344890845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304815882041926019563260563 457223823062889029344890845)
    ·
      refine ⟨171458933648583386004334067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457223823062889029344890845 171458933648583386004334067)
      ·
        refine ⟨257188400472875079006501101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171458933648583386004334067 257188400472875079006501101)
        ·
          refine ⟨96445650177328154627437913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257188400472875079006501101 96445650177328154627437913)
          ·
            refine ⟨72334237632996115970578435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96445650177328154627437913 72334237632996115970578435)
            ·
              refine ⟨108501356449494173955867653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72334237632996115970578435 108501356449494173955867653)
              ·
                refine ⟨20344004334280157616725185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108501356449494173955867653 20344004334280157616725185)
                ·
                  refine ⟨15258003250710118212543889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20344004334280157616725185 15258003250710118212543889)
                  ·
                    refine ⟨11443502438032588659407917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15258003250710118212543889 11443502438032588659407917)
                    ·
                      refine ⟨4291313414262220747277969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11443502438032588659407917 4291313414262220747277969)
                      ·
                        rfl

theorem cell23_8357303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_8357303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357303 prefixEnd_8357303 := by exact prefixLift 8357303
  have htrace : WordTrace (prefixWord ++ tailWord_8357303) baseStart_8357303 baseEnd_8357303 := by
    simpa [prefixWord, tailWord_8357303, baseEnd_8357303] using wordTrace_append hprefix tailTrace_8357303
  have hstable : (prefixWord ++ tailWord_8357303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357303).length < 2 ^ (prefixWord ++ tailWord_8357303).sum := by decide
  have hdescent : baseEnd_8357303 < baseStart_8357303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357357 : List Nat := [1, 5, 1, 3, 2, 2, 1, 2, 6]
def baseStart_8357357 : Nat := 118140960795 + 8357357 * 2 ^ 59
def prefixEnd_8357357 : Nat := 4983230072969 + 3 ^ 40 * 8357357 * 2
def baseEnd_8357357 : Nat := 476815682468618170666969

theorem tailTrace_8357357 : CollatzResearch.WordTrace tailWord_8357357 prefixEnd_8357357 476815682468618170666969 := by
  unfold tailWord_8357357
  simp only [CollatzResearch.WordTrace]
  refine ⟨304817851583730386785726325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203211901055820257857150883 304817851583730386785726325)
  ·
    refine ⟨28576673585974723761161843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304817851583730386785726325 28576673585974723761161843)
    ·
      refine ⟨42865010378962085641742765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28576673585974723761161843 42865010378962085641742765)
      ·
        refine ⟨16074378892110782115653537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42865010378962085641742765 16074378892110782115653537)
        ·
          refine ⟨12055784169083086586740153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16074378892110782115653537 12055784169083086586740153)
          ·
            refine ⟨9041838126812314940055115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12055784169083086586740153 9041838126812314940055115)
            ·
              refine ⟨13562757190218472410082673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9041838126812314940055115 13562757190218472410082673)
              ·
                refine ⟨10172067892663854307562005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13562757190218472410082673 10172067892663854307562005)
                ·
                  refine ⟨476815682468618170666969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10172067892663854307562005 476815682468618170666969)
                  ·
                    rfl

theorem cell23_8357357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_8357357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357357 prefixEnd_8357357 := by exact prefixLift 8357357
  have htrace : WordTrace (prefixWord ++ tailWord_8357357) baseStart_8357357 baseEnd_8357357 := by
    simpa [prefixWord, tailWord_8357357, baseEnd_8357357] using wordTrace_append hprefix tailTrace_8357357
  have hstable : (prefixWord ++ tailWord_8357357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357357).length < 2 ^ (prefixWord ++ tailWord_8357357).sum := by decide
  have hdescent : baseEnd_8357357 < baseStart_8357357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357374 : List Nat := [4, 2, 2, 3, 1, 1, 3, 1, 6]
def baseStart_8357374 : Nat := 118140960795 + 8357374 * 2 ^ 59
def prefixEnd_8357374 : Nat := 4983230072969 + 3 ^ 40 * 8357374 * 2
def baseEnd_8357374 : Nat := 476816652376521107721127

theorem tailTrace_8357374 : CollatzResearch.WordTrace tailWord_8357374 prefixEnd_8357374 476816652376521107721127 := by
  unfold tailWord_8357374
  simp only [CollatzResearch.WordTrace]
  refine ⟨38102308953083599836136897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203212314416445865792730117 38102308953083599836136897)
  ·
    refine ⟨28576731714812699877102673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38102308953083599836136897 28576731714812699877102673)
    ·
      refine ⟨21432548786109524907827005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28576731714812699877102673 21432548786109524907827005)
      ·
        refine ⟨8037205794791071840435127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21432548786109524907827005 8037205794791071840435127)
        ·
          refine ⟨12055808692186607760652691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037205794791071840435127 12055808692186607760652691)
          ·
            refine ⟨18083713038279911640979037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12055808692186607760652691 18083713038279911640979037)
            ·
              refine ⟨6781392389354966865367139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18083713038279911640979037 6781392389354966865367139)
              ·
                refine ⟨10172088584032450298050709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6781392389354966865367139 10172088584032450298050709)
                ·
                  refine ⟨476816652376521107721127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10172088584032450298050709 476816652376521107721127)
                  ·
                    rfl

theorem cell23_8357374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_8357374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357374 prefixEnd_8357374 := by exact prefixLift 8357374
  have htrace : WordTrace (prefixWord ++ tailWord_8357374) baseStart_8357374 baseEnd_8357374 := by
    simpa [prefixWord, tailWord_8357374, baseEnd_8357374] using wordTrace_append hprefix tailTrace_8357374
  have hstable : (prefixWord ++ tailWord_8357374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357374).length < 2 ^ (prefixWord ++ tailWord_8357374).sum := by decide
  have hdescent : baseEnd_8357374 < baseStart_8357374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357473 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 2, 6]
def baseStart_8357473 : Nat := 118140960795 + 8357473 * 2 ^ 59
def prefixEnd_8357473 : Nat := 4983230072969 + 3 ^ 40 * 8357473 * 2
def baseEnd_8357473 : Nat := 1430466901991161694050729

theorem tailTrace_8357473 : CollatzResearch.WordTrace tailWord_8357473 prefixEnd_8357473 1430466901991161694050729 := by
  unfold tailWord_8357473
  simp only [CollatzResearch.WordTrace]
  refine ⟨304822082451310138596949073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203214721634206759064632715 304822082451310138596949073)
  ·
    refine ⟨228616561838482603947711805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304822082451310138596949073 228616561838482603947711805)
    ·
      refine ⟨85731210689430976480391927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228616561838482603947711805 85731210689430976480391927)
      ·
        refine ⟨128596816034146464720587891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85731210689430976480391927 128596816034146464720587891)
        ·
          refine ⟨192895224051219697080881837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128596816034146464720587891 192895224051219697080881837)
          ·
            refine ⟨72335709019207386405330689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192895224051219697080881837 72335709019207386405330689)
            ·
              refine ⟨54251781764405539803998017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72335709019207386405330689 54251781764405539803998017)
              ·
                refine ⟨40688836323304154852998513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54251781764405539803998017 40688836323304154852998513)
                ·
                  refine ⟨30516627242478116139748885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40688836323304154852998513 30516627242478116139748885)
                  ·
                    refine ⟨1430466901991161694050729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30516627242478116139748885 1430466901991161694050729)
                    ·
                      rfl

theorem cell23_8357473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_8357473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357473 prefixEnd_8357473 := by exact prefixLift 8357473
  have htrace : WordTrace (prefixWord ++ tailWord_8357473) baseStart_8357473 baseEnd_8357473 := by
    simpa [prefixWord, tailWord_8357473, baseEnd_8357473] using wordTrace_append hprefix tailTrace_8357473
  have hstable : (prefixWord ++ tailWord_8357473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357473).length < 2 ^ (prefixWord ++ tailWord_8357473).sum := by decide
  have hdescent : baseEnd_8357473 < baseStart_8357473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357480 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_8357480 : Nat := 118140960795 + 8357480 * 2 ^ 59
def prefixEnd_8357480 : Nat := 4983230072969 + 3 ^ 40 * 8357480 * 2
def baseEnd_8357480 : Nat := 4291404300338066554764655

theorem tailTrace_8357480 : CollatzResearch.WordTrace tailWord_8357480 prefixEnd_8357480 4291404300338066554764655 := by
  unfold tailWord_8357480
  simp only [CollatzResearch.WordTrace]
  refine ⟨152411168881142389396226947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203214891841523185861635929 152411168881142389396226947)
  ·
    refine ⟨228616753321713584094340421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152411168881142389396226947 228616753321713584094340421)
    ·
      refine ⟨42865641247821297017688829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228616753321713584094340421 42865641247821297017688829)
      ·
        refine ⟨16074615467932986381633311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42865641247821297017688829 16074615467932986381633311)
        ·
          refine ⟨24111923201899479572449967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16074615467932986381633311 24111923201899479572449967)
          ·
            refine ⟨36167884802849219358674951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24111923201899479572449967 36167884802849219358674951)
            ·
              refine ⟨54251827204273829038012427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36167884802849219358674951 54251827204273829038012427)
              ·
                refine ⟨81377740806410743557018641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54251827204273829038012427 81377740806410743557018641)
                ·
                  refine ⟨61033305604808057667763981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81377740806410743557018641 61033305604808057667763981)
                  ·
                    refine ⟨22887489601803021625411493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61033305604808057667763981 22887489601803021625411493)
                    ·
                      refine ⟨4291404300338066554764655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22887489601803021625411493 4291404300338066554764655)
                      ·
                        rfl

theorem cell23_8357480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_8357480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357480 prefixEnd_8357480 := by exact prefixLift 8357480
  have htrace : WordTrace (prefixWord ++ tailWord_8357480) baseStart_8357480 baseEnd_8357480 := by
    simpa [prefixWord, tailWord_8357480, baseEnd_8357480] using wordTrace_append hprefix tailTrace_8357480
  have hstable : (prefixWord ++ tailWord_8357480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357480).length < 2 ^ (prefixWord ++ tailWord_8357480).sum := by decide
  have hdescent : baseEnd_8357480 < baseStart_8357480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357490 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_8357490 : Nat := 118140960795 + 8357490 * 2 ^ 59
def prefixEnd_8357490 : Nat := 4983230072969 + 3 ^ 40 * 8357490 * 2
def baseEnd_8357490 : Nat := 1430469811714870505213203

theorem tailTrace_8357490 : CollatzResearch.WordTrace tailWord_8357490 prefixEnd_8357490 1430469811714870505213203 := by
  unfold tailWord_8357490
  simp only [CollatzResearch.WordTrace]
  refine ⟨76205675623062137625079481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203215134994832367000211949 76205675623062137625079481)
  ·
    refine ⟨57154256717296603218809611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76205675623062137625079481 57154256717296603218809611)
    ·
      refine ⟨85731385075944904828214417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57154256717296603218809611 85731385075944904828214417)
      ·
        refine ⟨64298538806958678621160813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85731385075944904828214417 64298538806958678621160813)
        ·
          refine ⟨24111952052609504482935305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64298538806958678621160813 24111952052609504482935305)
          ·
            refine ⟨18083964039457128362201479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24111952052609504482935305 18083964039457128362201479)
            ·
              refine ⟨27125946059185692543302219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18083964039457128362201479 27125946059185692543302219)
              ·
                refine ⟨40688919088778538814953329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27125946059185692543302219 40688919088778538814953329)
                ·
                  refine ⟨30516689316583904111214997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40688919088778538814953329 30516689316583904111214997)
                  ·
                    refine ⟨1430469811714870505213203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30516689316583904111214997 1430469811714870505213203)
                    ·
                      rfl

theorem cell23_8357490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_8357490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357490 prefixEnd_8357490 := by exact prefixLift 8357490
  have htrace : WordTrace (prefixWord ++ tailWord_8357490) baseStart_8357490 baseEnd_8357490 := by
    simpa [prefixWord, tailWord_8357490, baseEnd_8357490] using wordTrace_append hprefix tailTrace_8357490
  have hstable : (prefixWord ++ tailWord_8357490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357490).length < 2 ^ (prefixWord ++ tailWord_8357490).sum := by decide
  have hdescent : baseEnd_8357490 < baseStart_8357490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357497 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 1, 4, 2]
def baseStart_8357497 : Nat := 118140960795 + 8357497 * 2 ^ 59
def prefixEnd_8357497 : Nat := 4983230072969 + 3 ^ 40 * 8357497 * 2
def baseEnd_8357497 : Nat := 4291413029509192988252077

theorem tailTrace_8357497 : CollatzResearch.WordTrace tailWord_8357497 prefixEnd_8357497 4291413029509192988252077 := by
  unfold tailWord_8357497
  simp only [CollatzResearch.WordTrace]
  refine ⟨304822957803223190695822745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203215305202148793797215163 304822957803223190695822745)
  ·
    refine ⟨228617218352417393021867059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304822957803223190695822745 228617218352417393021867059)
    ·
      refine ⟨342925827528626089532800589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228617218352417393021867059 342925827528626089532800589)
      ·
        refine ⟨128597185323234783574800221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342925827528626089532800589 128597185323234783574800221)
        ·
          refine ⟨48223944496213043840550083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128597185323234783574800221 48223944496213043840550083)
          ·
            refine ⟨72335916744319565760825125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48223944496213043840550083 72335916744319565760825125)
            ·
              refine ⟨13562984389559918580154711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72335916744319565760825125 13562984389559918580154711)
              ·
                refine ⟨20344476584339877870232067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13562984389559918580154711 20344476584339877870232067)
                ·
                  refine ⟨30516714876509816805348101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20344476584339877870232067 30516714876509816805348101)
                  ·
                    refine ⟨5721884039345590651002769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30516714876509816805348101 5721884039345590651002769)
                    ·
                      refine ⟨4291413029509192988252077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5721884039345590651002769 4291413029509192988252077)
                      ·
                        rfl

theorem cell23_8357497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_8357497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357497 prefixEnd_8357497 := by exact prefixLift 8357497
  have htrace : WordTrace (prefixWord ++ tailWord_8357497) baseStart_8357497 baseEnd_8357497 := by
    simpa [prefixWord, tailWord_8357497, baseEnd_8357497] using wordTrace_append hprefix tailTrace_8357497
  have hstable : (prefixWord ++ tailWord_8357497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357497).length < 2 ^ (prefixWord ++ tailWord_8357497).sum := by decide
  have hdescent : baseEnd_8357497 < baseStart_8357497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357537 : List Nat := [1, 2, 3, 3, 2, 1, 2, 4, 5]
def baseStart_8357537 : Nat := 118140960795 + 8357537 * 2 ^ 59
def prefixEnd_8357537 : Nat := 4983230072969 + 3 ^ 40 * 8357537 * 2
def baseEnd_8357537 : Nat := 476825952081708092416877

theorem tailTrace_8357537 : CollatzResearch.WordTrace tailWord_8357537 prefixEnd_8357537 476825952081708092416877 := by
  unfold tailWord_8357537
  simp only [CollatzResearch.WordTrace]
  refine ⟨304824416723078277527278865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203216277815385518351519243 304824416723078277527278865)
  ·
    refine ⟨228618312542308708145459149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304824416723078277527278865 228618312542308708145459149)
    ·
      refine ⟨85731867203365765554547181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228618312542308708145459149 85731867203365765554547181)
      ·
        refine ⟨32149450201262162082955193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85731867203365765554547181 32149450201262162082955193)
        ·
          refine ⟨24112087650946621562216395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32149450201262162082955193 24112087650946621562216395)
          ·
            refine ⟨36168131476419932343324593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24112087650946621562216395 36168131476419932343324593)
            ·
              refine ⟨27126098607314949257493445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36168131476419932343324593 27126098607314949257493445)
              ·
                refine ⟨5086143488871552985780021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27126098607314949257493445 5086143488871552985780021)
                ·
                  refine ⟨476825952081708092416877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5086143488871552985780021 476825952081708092416877)
                  ·
                    rfl

theorem cell23_8357537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 5].length) (baseStart_8357537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357537 prefixEnd_8357537 := by exact prefixLift 8357537
  have htrace : WordTrace (prefixWord ++ tailWord_8357537) baseStart_8357537 baseEnd_8357537 := by
    simpa [prefixWord, tailWord_8357537, baseEnd_8357537] using wordTrace_append hprefix tailTrace_8357537
  have hstable : (prefixWord ++ tailWord_8357537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357537).length < 2 ^ (prefixWord ++ tailWord_8357537).sum := by decide
  have hdescent : baseEnd_8357537 < baseStart_8357537 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357583 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 6]
def baseStart_8357583 : Nat := 118140960795 + 8357583 * 2 ^ 59
def prefixEnd_8357583 : Nat := 4983230072969 + 3 ^ 40 * 8357583 * 2
def baseEnd_8357583 : Nat := 4291457188845479651776681

theorem tailTrace_8357583 : CollatzResearch.WordTrace tailWord_8357583 prefixEnd_8357583 4291457188845479651776681 := by
  unfold tailWord_8357583
  simp only [CollatzResearch.WordTrace]
  refine ⟨304826094480911627383453403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203217396320607751588968935 304826094480911627383453403)
  ·
    refine ⟨457239141721367441075180105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304826094480911627383453403 457239141721367441075180105)
    ·
      refine ⟨342929356291025580806385079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457239141721367441075180105 342929356291025580806385079)
      ·
        refine ⟨514394034436538371209577619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342929356291025580806385079 514394034436538371209577619)
        ·
          refine ⟨771591051654807556814366429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514394034436538371209577619 771591051654807556814366429)
          ·
            refine ⟨289346644370552833805387411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 771591051654807556814366429 289346644370552833805387411)
            ·
              refine ⟨434019966555829250708081117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289346644370552833805387411 434019966555829250708081117)
              ·
                refine ⟨162757487458435969015530419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434019966555829250708081117 162757487458435969015530419)
                ·
                  refine ⟨244136231187653953523295629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162757487458435969015530419 244136231187653953523295629)
                  ·
                    refine ⟨91551086695370232571235861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244136231187653953523295629 91551086695370232571235861)
                    ·
                      refine ⟨4291457188845479651776681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91551086695370232571235861 4291457188845479651776681)
                      ·
                        rfl

theorem cell23_8357583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_8357583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357583 prefixEnd_8357583 := by exact prefixLift 8357583
  have htrace : WordTrace (prefixWord ++ tailWord_8357583) baseStart_8357583 baseEnd_8357583 := by
    simpa [prefixWord, tailWord_8357583, baseEnd_8357583] using wordTrace_append hprefix tailTrace_8357583
  have hstable : (prefixWord ++ tailWord_8357583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357583).length < 2 ^ (prefixWord ++ tailWord_8357583).sum := by decide
  have hdescent : baseEnd_8357583 < baseStart_8357583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357647 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 4, 3, 2]
def baseStart_8357647 : Nat := 118140960795 + 8357647 * 2 ^ 59
def prefixEnd_8357647 : Nat := 4983230072969 + 3 ^ 40 * 8357647 * 2
def baseEnd_8357647 : Nat := 4291490051607367401376387

theorem tailTrace_8357647 : CollatzResearch.WordTrace tailWord_8357647 prefixEnd_8357647 4291490051607367401376387 := by
  unfold tailWord_8357647
  simp only [CollatzResearch.WordTrace]
  refine ⟨304828428752679766313783195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203218952501786510875855463 304828428752679766313783195)
  ·
    refine ⟨457242643129019649470674793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304828428752679766313783195 457242643129019649470674793)
    ·
      refine ⟨342931982346764737103006095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457242643129019649470674793 342931982346764737103006095)
      ·
        refine ⟨514397973520147105654509143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342931982346764737103006095 514397973520147105654509143)
        ·
          refine ⟨771596960280220658481763715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514397973520147105654509143 771596960280220658481763715)
          ·
            refine ⟨1157395440420330987722645573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771596960280220658481763715 1157395440420330987722645573)
            ·
              refine ⟨217011645078812060197996045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1157395440420330987722645573 217011645078812060197996045)
              ·
                refine ⟨81379366904554522574248517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217011645078812060197996045 81379366904554522574248517)
                ·
                  refine ⟨15258631294603972982671597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81379366904554522574248517 15258631294603972982671597)
                  ·
                    refine ⟨5721986735476489868501849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15258631294603972982671597 5721986735476489868501849)
                    ·
                      refine ⟨4291490051607367401376387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5721986735476489868501849 4291490051607367401376387)
                      ·
                        rfl

theorem cell23_8357647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 3, 2].length) (baseStart_8357647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357647 prefixEnd_8357647 := by exact prefixLift 8357647
  have htrace : WordTrace (prefixWord ++ tailWord_8357647) baseStart_8357647 baseEnd_8357647 := by
    simpa [prefixWord, tailWord_8357647, baseEnd_8357647] using wordTrace_append hprefix tailTrace_8357647
  have hstable : (prefixWord ++ tailWord_8357647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357647).length < 2 ^ (prefixWord ++ tailWord_8357647).sum := by decide
  have hdescent : baseEnd_8357647 < baseStart_8357647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357681 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 2, 3, 2]
def baseStart_8357681 : Nat := 118140960795 + 8357681 * 2 ^ 59
def prefixEnd_8357681 : Nat := 4983230072969 + 3 ^ 40 * 8357681 * 2
def baseEnd_8357681 : Nat := 4291507509949620268351231

theorem tailTrace_8357681 : CollatzResearch.WordTrace tailWord_8357681 prefixEnd_8357681 4291507509949620268351231 := by
  unfold tailWord_8357681
  simp only [CollatzResearch.WordTrace]
  refine ⟨304829668834556590120520897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203219779223037726747013931 304829668834556590120520897)
  ·
    refine ⟨228622251625917442590390673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304829668834556590120520897 228622251625917442590390673)
    ·
      refine ⟨171466688719438081942793005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228622251625917442590390673 171466688719438081942793005)
      ·
        refine ⟨64300008269789280728547377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171466688719438081942793005 64300008269789280728547377)
        ·
          refine ⟨48225006202341960546410533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64300008269789280728547377 48225006202341960546410533)
          ·
            refine ⟨9042188662939117602451975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48225006202341960546410533 9042188662939117602451975)
            ·
              refine ⟨13563282994408676403677963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042188662939117602451975 13563282994408676403677963)
              ·
                refine ⟨20344924491613014605516945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13563282994408676403677963 20344924491613014605516945)
                ·
                  refine ⟨15258693368709760954137709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20344924491613014605516945 15258693368709760954137709)
                  ·
                    refine ⟨5722010013266160357801641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15258693368709760954137709 5722010013266160357801641)
                    ·
                      refine ⟨4291507509949620268351231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5722010013266160357801641 4291507509949620268351231)
                      ·
                        rfl

theorem cell23_8357681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_8357681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357681 prefixEnd_8357681 := by exact prefixLift 8357681
  have htrace : WordTrace (prefixWord ++ tailWord_8357681) baseStart_8357681 baseEnd_8357681 := by
    simpa [prefixWord, tailWord_8357681, baseEnd_8357681] using wordTrace_append hprefix tailTrace_8357681
  have hstable : (prefixWord ++ tailWord_8357681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357681).length < 2 ^ (prefixWord ++ tailWord_8357681).sum := by decide
  have hdescent : baseEnd_8357681 < baseStart_8357681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357704 : List Nat := [2, 1, 3, 1, 1, 4, 3, 2, 2, 4]
def baseStart_8357704 : Nat := 118140960795 + 8357704 * 2 ^ 59
def prefixEnd_8357704 : Nat := 4983230072969 + 3 ^ 40 * 8357704 * 2
def baseEnd_8357704 : Nat := 1430506440001557892787875

theorem tailTrace_8357704 : CollatzResearch.WordTrace tailWord_8357704 prefixEnd_8357704 1430506440001557892787875 := by
  unfold tailWord_8357704
  simp only [CollatzResearch.WordTrace]
  refine ⟨152415253856736632524304083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203220338475648843365738777 152415253856736632524304083)
  ·
    refine ⟨228622880785104948786456125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152415253856736632524304083 228622880785104948786456125)
    ·
      refine ⟨85733580294414355794921047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228622880785104948786456125 85733580294414355794921047)
      ·
        refine ⟨128600370441621533692381571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85733580294414355794921047 128600370441621533692381571)
        ·
          refine ⟨192900555662432300538572357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128600370441621533692381571 192900555662432300538572357)
          ·
            refine ⟨36168854186706056350982317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192900555662432300538572357 36168854186706056350982317)
            ·
              refine ⟨13563320320014771131618369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36168854186706056350982317 13563320320014771131618369)
              ·
                refine ⟨10172490240011078348713777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13563320320014771131618369 10172490240011078348713777)
                ·
                  refine ⟨7629367680008308761535333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10172490240011078348713777 7629367680008308761535333)
                  ·
                    refine ⟨1430506440001557892787875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7629367680008308761535333 1430506440001557892787875)
                    ·
                      rfl

theorem cell23_8357704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_8357704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357704 prefixEnd_8357704 := by exact prefixLift 8357704
  have htrace : WordTrace (prefixWord ++ tailWord_8357704) baseStart_8357704 baseEnd_8357704 := by
    simpa [prefixWord, tailWord_8357704, baseEnd_8357704] using wordTrace_append hprefix tailTrace_8357704
  have hstable : (prefixWord ++ tailWord_8357704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357704).length < 2 ^ (prefixWord ++ tailWord_8357704).sum := by decide
  have hdescent : baseEnd_8357704 < baseStart_8357704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357710 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_8357710 : Nat := 118140960795 + 8357710 * 2 ^ 59
def prefixEnd_8357710 : Nat := 4983230072969 + 3 ^ 40 * 8357710 * 2
def baseEnd_8357710 : Nat := 4291522400888600654888597

theorem tailTrace_8357710 : CollatzResearch.WordTrace tailWord_8357710 prefixEnd_8357710 4291522400888600654888597 := by
  unfold tailWord_8357710
  simp only [CollatzResearch.WordTrace]
  refine ⟨38103840818931441009165823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203220484367634352048884389 38103840818931441009165823)
  ·
    refine ⟨57155761228397161513748735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38103840818931441009165823 57155761228397161513748735)
    ·
      refine ⟨85733641842595742270623103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57155761228397161513748735 85733641842595742270623103)
      ·
        refine ⟨128600462763893613405934655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85733641842595742270623103 128600462763893613405934655)
        ·
          refine ⟨192900694145840420108901983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128600462763893613405934655 192900694145840420108901983)
          ·
            refine ⟨289351041218760630163352975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192900694145840420108901983 289351041218760630163352975)
            ·
              refine ⟨434026561828140945245029463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289351041218760630163352975 434026561828140945245029463)
              ·
                refine ⟨651039842742211417867544195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434026561828140945245029463 651039842742211417867544195)
                ·
                  refine ⟨976559764113317126801316293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651039842742211417867544195 976559764113317126801316293)
                  ·
                    refine ⟨183104955771246961275246805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 976559764113317126801316293 183104955771246961275246805)
                    ·
                      refine ⟨4291522400888600654888597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183104955771246961275246805 4291522400888600654888597)
                      ·
                        rfl

theorem cell23_8357710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_8357710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357710 prefixEnd_8357710 := by exact prefixLift 8357710
  have htrace : WordTrace (prefixWord ++ tailWord_8357710) baseStart_8357710 baseEnd_8357710 := by
    simpa [prefixWord, tailWord_8357710, baseEnd_8357710] using wordTrace_append hprefix tailTrace_8357710
  have hstable : (prefixWord ++ tailWord_8357710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357710).length < 2 ^ (prefixWord ++ tailWord_8357710).sum := by decide
  have hdescent : baseEnd_8357710 < baseStart_8357710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357724 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_8357724 : Nat := 118140960795 + 8357724 * 2 ^ 59
def prefixEnd_8357724 : Nat := 4983230072969 + 3 ^ 40 * 8357724 * 2
def baseEnd_8357724 : Nat := 4291529589617763600113533

theorem tailTrace_8357724 : CollatzResearch.WordTrace tailWord_8357724 prefixEnd_8357724 4291529589617763600113533 := by
  unfold tailWord_8357724
  simp only [CollatzResearch.WordTrace]
  refine ⟨152415618586700404232168113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203220824782267205642890817 152415618586700404232168113)
  ·
    refine ⟨114311713940025303174126085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152415618586700404232168113 114311713940025303174126085)
    ·
      refine ⟨21433446363754744345148641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114311713940025303174126085 21433446363754744345148641)
      ·
        refine ⟨16075084772816058258861481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21433446363754744345148641 16075084772816058258861481)
        ·
          refine ⟨12056313579612043694146111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16075084772816058258861481 12056313579612043694146111)
          ·
            refine ⟨18084470369418065541219167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12056313579612043694146111 18084470369418065541219167)
            ·
              refine ⟨27126705554127098311828751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18084470369418065541219167 27126705554127098311828751)
              ·
                refine ⟨40690058331190647467743127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27126705554127098311828751 40690058331190647467743127)
                ·
                  refine ⟨61035087496785971201614691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40690058331190647467743127 61035087496785971201614691)
                  ·
                    refine ⟨91552631245178956802422037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61035087496785971201614691 91552631245178956802422037)
                    ·
                      refine ⟨4291529589617763600113533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91552631245178956802422037 4291529589617763600113533)
                      ·
                        rfl

theorem cell23_8357724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_8357724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357724 prefixEnd_8357724 := by exact prefixLift 8357724
  have htrace : WordTrace (prefixWord ++ tailWord_8357724) baseStart_8357724 baseEnd_8357724 := by
    simpa [prefixWord, tailWord_8357724, baseEnd_8357724] using wordTrace_append hprefix tailTrace_8357724
  have hstable : (prefixWord ++ tailWord_8357724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357724).length < 2 ^ (prefixWord ++ tailWord_8357724).sum := by decide
  have hdescent : baseEnd_8357724 < baseStart_8357724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357731 : List Nat := [1, 1, 1, 5, 4, 1, 2, 2, 1, 2, 3]
def baseStart_8357731 : Nat := 118140960795 + 8357731 * 2 ^ 59
def prefixEnd_8357731 : Nat := 4983230072969 + 3 ^ 40 * 8357731 * 2
def baseEnd_8357731 : Nat := 4291533183982345072726001

theorem tailTrace_8357731 : CollatzResearch.WordTrace tailWord_8357731 prefixEnd_8357731 4291533183982345072726001 := by
  unfold tailWord_8357731
  simp only [CollatzResearch.WordTrace]
  refine ⟨304831492484375448659841047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203220994989583632439894031 304831492484375448659841047)
  ·
    refine ⟨457247238726563172989761571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304831492484375448659841047 457247238726563172989761571)
    ·
      refine ⟨685870858089844759484642357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457247238726563172989761571 685870858089844759484642357)
      ·
        refine ⟨64300392945922946201685221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 685870858089844759484642357 64300392945922946201685221)
        ·
          refine ⟨12056323677360552412815979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64300392945922946201685221 12056323677360552412815979)
          ·
            refine ⟨18084485516040828619223969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12056323677360552412815979 18084485516040828619223969)
            ·
              refine ⟨13563364137030621464417977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18084485516040828619223969 13563364137030621464417977)
              ·
                refine ⟨10172523102772966098313483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13563364137030621464417977 10172523102772966098313483)
                ·
                  refine ⟨15258784654159449147470225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10172523102772966098313483 15258784654159449147470225)
                  ·
                    refine ⟨11444088490619586860602669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15258784654159449147470225 11444088490619586860602669)
                    ·
                      refine ⟨4291533183982345072726001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11444088490619586860602669 4291533183982345072726001)
                      ·
                        rfl

theorem cell23_8357731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_8357731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357731 prefixEnd_8357731 := by exact prefixLift 8357731
  have htrace : WordTrace (prefixWord ++ tailWord_8357731) baseStart_8357731 baseEnd_8357731 := by
    simpa [prefixWord, tailWord_8357731, baseEnd_8357731] using wordTrace_append hprefix tailTrace_8357731
  have hstable : (prefixWord ++ tailWord_8357731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357731).length < 2 ^ (prefixWord ++ tailWord_8357731).sum := by decide
  have hdescent : baseEnd_8357731 < baseStart_8357731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357737 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 2, 7, 2]
def baseStart_8357737 : Nat := 118140960795 + 8357737 * 2 ^ 59
def prefixEnd_8357737 : Nat := 4983230072969 + 3 ^ 40 * 8357737 * 2
def baseEnd_8357737 : Nat := 4291536264866272049250973

theorem tailTrace_8357737 : CollatzResearch.WordTrace tailWord_8357737 prefixEnd_8357737 4291536264866272049250973 := by
  unfold tailWord_8357737
  simp only [CollatzResearch.WordTrace]
  refine ⟨304831711322353711684559465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203221140881569141123039643 304831711322353711684559465)
  ·
    refine ⟨228623783491765283763419599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304831711322353711684559465 228623783491765283763419599)
    ·
      refine ⟨342935675237647925645129399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228623783491765283763419599 342935675237647925645129399)
      ·
        refine ⟨514403512856471888467694099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342935675237647925645129399 514403512856471888467694099)
        ·
          refine ⟨771605269284707832701541149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514403512856471888467694099 771605269284707832701541149)
          ·
            refine ⟨289351975981765437263077931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 771605269284707832701541149 289351975981765437263077931)
            ·
              refine ⟨434027963972648155894616897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289351975981765437263077931 434027963972648155894616897)
              ·
                refine ⟨325520972979486116920962673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434027963972648155894616897 325520972979486116920962673)
                ·
                  refine ⟨244140729734614587690722005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325520972979486116920962673 244140729734614587690722005)
                  ·
                    refine ⟨5722048353155029399001297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 244140729734614587690722005 5722048353155029399001297)
                    ·
                      refine ⟨4291536264866272049250973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5722048353155029399001297 4291536264866272049250973)
                      ·
                        rfl

theorem cell23_8357737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 7, 2].length) (baseStart_8357737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357737 prefixEnd_8357737 := by exact prefixLift 8357737
  have htrace : WordTrace (prefixWord ++ tailWord_8357737) baseStart_8357737 baseEnd_8357737 := by
    simpa [prefixWord, tailWord_8357737, baseEnd_8357737] using wordTrace_append hprefix tailTrace_8357737
  have hstable : (prefixWord ++ tailWord_8357737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357737).length < 2 ^ (prefixWord ++ tailWord_8357737).sum := by decide
  have hdescent : baseEnd_8357737 < baseStart_8357737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357778 : List Nat := [3, 2, 3, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_8357778 : Nat := 118140960795 + 8357778 * 2 ^ 59
def prefixEnd_8357778 : Nat := 4983230072969 + 3 ^ 40 * 8357778 * 2
def baseEnd_8357778 : Nat := 4291557317573106388838285

theorem tailTrace_8357778 : CollatzResearch.WordTrace tailWord_8357778 prefixEnd_8357778 4291557317573106388838285 := by
  unfold tailWord_8357778
  simp only [CollatzResearch.WordTrace]
  refine ⟨76208301678801293921700497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203222137810136783791201325 76208301678801293921700497)
  ·
    refine ⟨57156226259100970441275373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76208301678801293921700497 57156226259100970441275373)
    ·
      refine ⟨21433584847162863915478265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57156226259100970441275373 21433584847162863915478265)
      ·
        refine ⟨16075188635372147936608699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21433584847162863915478265 16075188635372147936608699)
        ·
          refine ⟨24112782953058221904913049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16075188635372147936608699 24112782953058221904913049)
          ·
            refine ⟨18084587214793666428684787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24112782953058221904913049 18084587214793666428684787)
            ·
              refine ⟨27126880822190499643027181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18084587214793666428684787 27126880822190499643027181)
              ·
                refine ⟨10172580308321437366135193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27126880822190499643027181 10172580308321437366135193)
                ·
                  refine ⟨7629435231241078024601395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10172580308321437366135193 7629435231241078024601395)
                  ·
                    refine ⟨11444152846861617036902093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7629435231241078024601395 11444152846861617036902093)
                    ·
                      refine ⟨4291557317573106388838285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11444152846861617036902093 4291557317573106388838285)
                      ·
                        rfl

theorem cell23_8357778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_8357778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357778 prefixEnd_8357778 := by exact prefixLift 8357778
  have htrace : WordTrace (prefixWord ++ tailWord_8357778) baseStart_8357778 baseEnd_8357778 := by
    simpa [prefixWord, tailWord_8357778, baseEnd_8357778] using wordTrace_append hprefix tailTrace_8357778
  have hstable : (prefixWord ++ tailWord_8357778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357778).length < 2 ^ (prefixWord ++ tailWord_8357778).sum := by decide
  have hdescent : baseEnd_8357778 < baseStart_8357778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357782 : List Nat := [5, 3, 1, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_8357782 : Nat := 118140960795 + 8357782 * 2 ^ 59
def prefixEnd_8357782 : Nat := 4983230072969 + 3 ^ 40 * 8357782 * 2
def baseEnd_8357782 : Nat := 4291559371495724373188267

theorem tailTrace_8357782 : CollatzResearch.WordTrace tailWord_8357782 prefixEnd_8357782 4291559371495724373188267 := by
  unfold tailWord_8357782
  simp only [CollatzResearch.WordTrace]
  refine ⟨19052084537949417773121725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203222235071460456246631733 19052084537949417773121725)
  ·
    refine ⟨7144531701731031664920647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19052084537949417773121725 7144531701731031664920647)
    ·
      refine ⟨10716797552596547497380971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7144531701731031664920647 10716797552596547497380971)
      ·
        refine ⟨16075196328894821246071457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10716797552596547497380971 16075196328894821246071457)
        ·
          refine ⟨12056397246671115934553593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16075196328894821246071457 12056397246671115934553593)
          ·
            refine ⟨9042297935003336950915195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12056397246671115934553593 9042297935003336950915195)
            ·
              refine ⟨13563446902505005426372793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042297935003336950915195 13563446902505005426372793)
              ·
                refine ⟨10172585176878754069779595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13563446902505005426372793 10172585176878754069779595)
                ·
                  refine ⟨15258877765318131104669393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10172585176878754069779595 15258877765318131104669393)
                  ·
                    refine ⟨11444158323988598328502045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15258877765318131104669393 11444158323988598328502045)
                    ·
                      refine ⟨4291559371495724373188267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11444158323988598328502045 4291559371495724373188267)
                      ·
                        rfl

theorem cell23_8357782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_8357782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357782 prefixEnd_8357782 := by exact prefixLift 8357782
  have htrace : WordTrace (prefixWord ++ tailWord_8357782) baseStart_8357782 baseEnd_8357782 := by
    simpa [prefixWord, tailWord_8357782, baseEnd_8357782] using wordTrace_append hprefix tailTrace_8357782
  have hstable : (prefixWord ++ tailWord_8357782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357782).length < 2 ^ (prefixWord ++ tailWord_8357782).sum := by decide
  have hdescent : baseEnd_8357782 < baseStart_8357782 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357788 : List Nat := [2, 2, 3, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_8357788 : Nat := 118140960795 + 8357788 * 2 ^ 59
def prefixEnd_8357788 : Nat := 4983230072969 + 3 ^ 40 * 8357788 * 2
def baseEnd_8357788 : Nat := 4291562452379651349713239

theorem tailTrace_8357788 : CollatzResearch.WordTrace tailWord_8357788 prefixEnd_8357788 4291562452379651349713239 := by
  unfold tailWord_8357788
  simp only [CollatzResearch.WordTrace]
  refine ⟨152416785722584473697333009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203222380963445964929777345 152416785722584473697333009)
  ·
    refine ⟨114312589291938355272999757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152416785722584473697333009 114312589291938355272999757)
    ·
      refine ⟨42867220984476883227374909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114312589291938355272999757 42867220984476883227374909)
      ·
        refine ⟨16075207869178831210265591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42867220984476883227374909 16075207869178831210265591)
        ·
          refine ⟨24112811803768246815398387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16075207869178831210265591 24112811803768246815398387)
          ·
            refine ⟨36169217705652370223097581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24112811803768246815398387 36169217705652370223097581)
            ·
              refine ⟨13563456639619638833661593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36169217705652370223097581 13563456639619638833661593)
              ·
                refine ⟨10172592479714729125246195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13563456639619638833661593 10172592479714729125246195)
                ·
                  refine ⟨15258888719572093687869293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10172592479714729125246195 15258888719572093687869293)
                  ·
                    refine ⟨5722083269839535132950985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15258888719572093687869293 5722083269839535132950985)
                    ·
                      refine ⟨4291562452379651349713239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5722083269839535132950985 4291562452379651349713239)
                      ·
                        rfl

theorem cell23_8357788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_8357788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357788 prefixEnd_8357788 := by exact prefixLift 8357788
  have htrace : WordTrace (prefixWord ++ tailWord_8357788) baseStart_8357788 baseEnd_8357788 := by
    simpa [prefixWord, tailWord_8357788, baseEnd_8357788] using wordTrace_append hprefix tailTrace_8357788
  have hstable : (prefixWord ++ tailWord_8357788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357788).length < 2 ^ (prefixWord ++ tailWord_8357788).sum := by decide
  have hdescent : baseEnd_8357788 < baseStart_8357788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357824 : List Nat := [2, 1, 1, 2, 3, 2, 3, 4, 5]
def baseStart_8357824 : Nat := 118140960795 + 8357824 * 2 ^ 59
def prefixEnd_8357824 : Nat := 4983230072969 + 3 ^ 40 * 8357824 * 2
def baseEnd_8357824 : Nat := 476842326409245912095897

theorem tailTrace_8357824 : CollatzResearch.WordTrace tailWord_8357824 prefixEnd_8357824 476842326409245912095897 := by
  unfold tailWord_8357824
  simp only [CollatzResearch.WordTrace]
  refine ⟨152417442236519262771488263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203223256315359017028651017 152417442236519262771488263)
  ·
    refine ⟨228626163354778894157232395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152417442236519262771488263 228626163354778894157232395)
    ·
      refine ⟨342939245032168341235848593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228626163354778894157232395 342939245032168341235848593)
      ·
        refine ⟨257204433774126255926886445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342939245032168341235848593 257204433774126255926886445)
        ·
          refine ⟨96451662665297345972582417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257204433774126255926886445 96451662665297345972582417)
          ·
            refine ⟨72338746998973009479436813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96451662665297345972582417 72338746998973009479436813)
            ·
              refine ⟨27127030124614878554788805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72338746998973009479436813 27127030124614878554788805)
              ·
                refine ⟨5086318148365289729022901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27127030124614878554788805 5086318148365289729022901)
                ·
                  refine ⟨476842326409245912095897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5086318148365289729022901 476842326409245912095897)
                  ·
                    rfl

theorem cell23_8357824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 5].length) (baseStart_8357824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357824 prefixEnd_8357824 := by exact prefixLift 8357824
  have htrace : WordTrace (prefixWord ++ tailWord_8357824) baseStart_8357824 baseEnd_8357824 := by
    simpa [prefixWord, tailWord_8357824, baseEnd_8357824] using wordTrace_append hprefix tailTrace_8357824
  have hstable : (prefixWord ++ tailWord_8357824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357824).length < 2 ^ (prefixWord ++ tailWord_8357824).sum := by decide
  have hdescent : baseEnd_8357824 < baseStart_8357824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8357869 : List Nat := [1, 5, 1, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_8357869 : Nat := 118140960795 + 8357869 * 2 ^ 59
def prefixEnd_8357869 : Nat := 4983230072969 + 3 ^ 40 * 8357869 * 2
def baseEnd_8357869 : Nat := 4291604044312665532800367

theorem tailTrace_8357869 : CollatzResearch.WordTrace tailWord_8357869 prefixEnd_8357869 4291604044312665532800367 := by
  unfold tailWord_8357869
  simp only [CollatzResearch.WordTrace]
  refine ⟨304836525757875498228364661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203224350505250332152243107 304836525757875498228364661)
  ·
    refine ⟨28578424289800827958909187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304836525757875498228364661 28578424289800827958909187)
    ·
      refine ⟨42867636434701241938363781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28578424289800827958909187 42867636434701241938363781)
      ·
        refine ⟨8037681831506482863443209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42867636434701241938363781 8037681831506482863443209)
        ·
          refine ⟨6028261373629862147582407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8037681831506482863443209 6028261373629862147582407)
          ·
            refine ⟨9042392060444793221373611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028261373629862147582407 9042392060444793221373611)
            ·
              refine ⟨13563588090667189832060417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042392060444793221373611 13563588090667189832060417)
              ·
                refine ⟨10172691068000392374045313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13563588090667189832060417 10172691068000392374045313)
                ·
                  refine ⟨7629518301000294280533985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10172691068000392374045313 7629518301000294280533985)
                  ·
                    refine ⟨5722138725750220710400489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7629518301000294280533985 5722138725750220710400489)
                    ·
                      refine ⟨4291604044312665532800367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5722138725750220710400489 4291604044312665532800367)
                      ·
                        rfl

theorem cell23_8357869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_8357869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8357869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8357869 prefixEnd_8357869 := by exact prefixLift 8357869
  have htrace : WordTrace (prefixWord ++ tailWord_8357869) baseStart_8357869 baseEnd_8357869 := by
    simpa [prefixWord, tailWord_8357869, baseEnd_8357869] using wordTrace_append hprefix tailTrace_8357869
  have hstable : (prefixWord ++ tailWord_8357869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8357869).length < 2 ^ (prefixWord ++ tailWord_8357869).sum := by decide
  have hdescent : baseEnd_8357869 < baseStart_8357869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8357869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358021 : List Nat := [1, 3, 1, 1, 5, 2, 3, 7]
def baseStart_8358021 : Nat := 118140960795 + 8358021 * 2 ^ 59
def prefixEnd_8358021 : Nat := 4983230072969 + 3 ^ 40 * 8358021 * 2
def baseEnd_8358021 : Nat := 158951188643412923633321

theorem tailTrace_8358021 : CollatzResearch.WordTrace tailWord_8358021 prefixEnd_8358021 158951188643412923633321 := by
  unfold tailWord_8358021
  simp only [CollatzResearch.WordTrace]
  refine ⟨304842069653324828187897917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203228046435549885458598611 304842069653324828187897917)
  ·
    refine ⟨114315776119996810570461719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304842069653324828187897917 114315776119996810570461719)
    ·
      refine ⟨171473664179995215855692579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114315776119996810570461719 171473664179995215855692579)
      ·
        refine ⟨257210496269992823783538869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171473664179995215855692579 257210496269992823783538869)
        ·
          refine ⟨24113484025311827229706769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257210496269992823783538869 24113484025311827229706769)
          ·
            refine ⟨18085113018983870422280077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24113484025311827229706769 18085113018983870422280077)
            ·
              refine ⟨6781917382118951408355029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18085113018983870422280077 6781917382118951408355029)
              ·
                refine ⟨158951188643412923633321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6781917382118951408355029 158951188643412923633321)
                ·
                  rfl

theorem cell23_8358021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 7].length) (baseStart_8358021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358021 prefixEnd_8358021 := by exact prefixLift 8358021
  have htrace : WordTrace (prefixWord ++ tailWord_8358021) baseStart_8358021 baseEnd_8358021 := by
    simpa [prefixWord, tailWord_8358021, baseEnd_8358021] using wordTrace_append hprefix tailTrace_8358021
  have hstable : (prefixWord ++ tailWord_8358021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358021).length < 2 ^ (prefixWord ++ tailWord_8358021).sum := by decide
  have hdescent : baseEnd_8358021 < baseStart_8358021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358042 : List Nat := [3, 1, 1, 5, 3, 1, 1, 2, 2, 4]
def baseStart_8358042 : Nat := 118140960795 + 8358042 * 2 ^ 59
def prefixEnd_8358042 : Nat := 4983230072969 + 3 ^ 40 * 8358042 * 2
def baseEnd_8358042 : Nat := 1430564292155297785312357

theorem tailTrace_8358042 : CollatzResearch.WordTrace tailWord_8358042 prefixEnd_8358042 1430564292155297785312357 := by
  unfold tailWord_8358042
  simp only [CollatzResearch.WordTrace]
  refine ⟨76210708896562187193603095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203228557057499165849608253 76210708896562187193603095)
  ·
    refine ⟨114316063344843280790404643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76210708896562187193603095 114316063344843280790404643)
    ·
      refine ⟨171474095017264921185606965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114316063344843280790404643 171474095017264921185606965)
      ·
        refine ⟨16075696407868586361150653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171474095017264921185606965 16075696407868586361150653)
        ·
          refine ⟨6028386152950719885431495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16075696407868586361150653 6028386152950719885431495)
          ·
            refine ⟨9042579229426079828147243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6028386152950719885431495 9042579229426079828147243)
            ·
              refine ⟨13563868844139119742220865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042579229426079828147243 13563868844139119742220865)
              ·
                refine ⟨10172901633104339806665649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13563868844139119742220865 10172901633104339806665649)
                ·
                  refine ⟨7629676224828254854999237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10172901633104339806665649 7629676224828254854999237)
                  ·
                    refine ⟨1430564292155297785312357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7629676224828254854999237 1430564292155297785312357)
                    ·
                      rfl

theorem cell23_8358042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_8358042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358042 prefixEnd_8358042 := by exact prefixLift 8358042
  have htrace : WordTrace (prefixWord ++ tailWord_8358042) baseStart_8358042 baseEnd_8358042 := by
    simpa [prefixWord, tailWord_8358042, baseEnd_8358042] using wordTrace_append hprefix tailTrace_8358042
  have hstable : (prefixWord ++ tailWord_8358042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358042).length < 2 ^ (prefixWord ++ tailWord_8358042).sum := by decide
  have hdescent : baseEnd_8358042 < baseStart_8358042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358048 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 4, 1, 3]
def baseStart_8358048 : Nat := 118140960795 + 8358048 * 2 ^ 59
def prefixEnd_8358048 : Nat := 4983230072969 + 3 ^ 40 * 8358048 * 2
def baseEnd_8358048 : Nat := 4291695957349820332462043

theorem tailTrace_8358048 : CollatzResearch.WordTrace tailWord_8358048 prefixEnd_8358048 4291695957349820332462043 := by
  unfold tailWord_8358048
  simp only [CollatzResearch.WordTrace]
  refine ⟨152421527212113505899565399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203228702949484674532753865 152421527212113505899565399)
  ·
    refine ⟨228632290818170258849348099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152421527212113505899565399 228632290818170258849348099)
    ·
      refine ⟨342948436227255388274022149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228632290818170258849348099 342948436227255388274022149)
      ·
        refine ⟨64302831792610385301379153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342948436227255388274022149 64302831792610385301379153)
        ·
          refine ⟨48227123844457788976034365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64302831792610385301379153 48227123844457788976034365)
          ·
            refine ⟨18085171441671670866012887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48227123844457788976034365 18085171441671670866012887)
            ·
              refine ⟨27127757162507506299019331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18085171441671670866012887 27127757162507506299019331)
              ·
                refine ⟨40691635743761259448528997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27127757162507506299019331 40691635743761259448528997)
                ·
                  refine ⟨7629681701955236146599187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40691635743761259448528997 7629681701955236146599187)
                  ·
                    refine ⟨11444522552932854219898781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7629681701955236146599187 11444522552932854219898781)
                    ·
                      refine ⟨4291695957349820332462043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11444522552932854219898781 4291695957349820332462043)
                      ·
                        rfl

theorem cell23_8358048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_8358048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358048 prefixEnd_8358048 := by exact prefixLift 8358048
  have htrace : WordTrace (prefixWord ++ tailWord_8358048) baseStart_8358048 baseEnd_8358048 := by
    simpa [prefixWord, tailWord_8358048, baseEnd_8358048] using wordTrace_append hprefix tailTrace_8358048
  have hstable : (prefixWord ++ tailWord_8358048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358048).length < 2 ^ (prefixWord ++ tailWord_8358048).sum := by decide
  have hdescent : baseEnd_8358048 < baseStart_8358048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358062 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_8358062 : Nat := 118140960795 + 8358062 * 2 ^ 59
def prefixEnd_8358062 : Nat := 4983230072969 + 3 ^ 40 * 8358062 * 2
def baseEnd_8358062 : Nat := 4291703146078983277686979

theorem tailTrace_8358062 : CollatzResearch.WordTrace tailWord_8358062 prefixEnd_8358062 4291703146078983277686979 := by
  unfold tailWord_8358062
  simp only [CollatzResearch.WordTrace]
  refine ⟨38105445630772036523767555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203229043364117528126760293 38105445630772036523767555)
  ·
    refine ⟨57158168446158054785651333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38105445630772036523767555 57158168446158054785651333)
    ·
      refine ⟨10717156583654635272309625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57158168446158054785651333 10717156583654635272309625)
      ·
        refine ⟨8037867437740976454232219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10717156583654635272309625 8037867437740976454232219)
        ·
          refine ⟨12056801156611464681348329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037867437740976454232219 12056801156611464681348329)
          ·
            refine ⟨9042600867458598511011247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12056801156611464681348329 9042600867458598511011247)
            ·
              refine ⟨13563901301187897766516871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042600867458598511011247 13563901301187897766516871)
              ·
                refine ⟨20345851951781846649775307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13563901301187897766516871 20345851951781846649775307)
                ·
                  refine ⟨30518777927672769974662961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20345851951781846649775307 30518777927672769974662961)
                  ·
                    refine ⟨22889083445754577480997221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30518777927672769974662961 22889083445754577480997221)
                    ·
                      refine ⟨4291703146078983277686979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22889083445754577480997221 4291703146078983277686979)
                      ·
                        rfl

theorem cell23_8358062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_8358062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358062 prefixEnd_8358062 := by exact prefixLift 8358062
  have htrace : WordTrace (prefixWord ++ tailWord_8358062) baseStart_8358062 baseEnd_8358062 := by
    simpa [prefixWord, tailWord_8358062, baseEnd_8358062] using wordTrace_append hprefix tailTrace_8358062
  have hstable : (prefixWord ++ tailWord_8358062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358062).length < 2 ^ (prefixWord ++ tailWord_8358062).sum := by decide
  have hdescent : baseEnd_8358062 < baseStart_8358062 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358065 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 1, 3, 3]
def baseStart_8358065 : Nat := 118140960795 + 8358065 * 2 ^ 59
def prefixEnd_8358065 : Nat := 4983230072969 + 3 ^ 40 * 8358065 * 2
def baseEnd_8358065 : Nat := 4291704686520946765949465

theorem tailTrace_8358065 : CollatzResearch.WordTrace tailWord_8358065 prefixEnd_8358065 4291704686520946765949465 := by
  unfold tailWord_8358065
  simp only [CollatzResearch.WordTrace]
  refine ⟨304843674465165423702499649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203229116310110282468333099 304843674465165423702499649)
  ·
    refine ⟨228632755848874067776874737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304843674465165423702499649 228632755848874067776874737)
    ·
      refine ⟨171474566886655550832656053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228632755848874067776874737 171474566886655550832656053)
      ·
        refine ⟨16075740645623957890561505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171474566886655550832656053 16075740645623957890561505)
        ·
          refine ⟨12056805484217968417921129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16075740645623957890561505 12056805484217968417921129)
          ·
            refine ⟨9042604113163476313440847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12056805484217968417921129 9042604113163476313440847)
            ·
              refine ⟨13563906169745214470161271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9042604113163476313440847 13563906169745214470161271)
              ·
                refine ⟨20345859254617821705241907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13563906169745214470161271 20345859254617821705241907)
                ·
                  refine ⟨30518788881926732557862861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20345859254617821705241907 30518788881926732557862861)
                  ·
                    refine ⟨11444545830722524709198573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30518788881926732557862861 11444545830722524709198573)
                    ·
                      refine ⟨4291704686520946765949465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11444545830722524709198573 4291704686520946765949465)
                      ·
                        rfl

theorem cell23_8358065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_8358065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358065 prefixEnd_8358065 := by exact prefixLift 8358065
  have htrace : WordTrace (prefixWord ++ tailWord_8358065) baseStart_8358065 baseEnd_8358065 := by
    simpa [prefixWord, tailWord_8358065, baseEnd_8358065] using wordTrace_append hprefix tailTrace_8358065
  have hstable : (prefixWord ++ tailWord_8358065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358065).length < 2 ^ (prefixWord ++ tailWord_8358065).sum := by decide
  have hdescent : baseEnd_8358065 < baseStart_8358065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358082 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_8358082 : Nat := 118140960795 + 8358082 * 2 ^ 59
def prefixEnd_8358082 : Nat := 4983230072969 + 3 ^ 40 * 8358082 * 2
def baseEnd_8358082 : Nat := 4291713415692073199436887

theorem tailTrace_8358082 : CollatzResearch.WordTrace tailWord_8358082 prefixEnd_8358082 4291713415692073199436887 := by
  unfold tailWord_8358082
  simp only [CollatzResearch.WordTrace]
  refine ⟨76211073626525958901467125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203229529670735890403912333 76211073626525958901467125)
  ·
    refine ⟨7144788152486808647012543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76211073626525958901467125 7144788152486808647012543)
    ·
      refine ⟨10717182228730212970518815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7144788152486808647012543 10717182228730212970518815)
      ·
        refine ⟨16075773343095319455778223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10717182228730212970518815 16075773343095319455778223)
        ·
          refine ⟨24113660014642979183667335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16075773343095319455778223 24113660014642979183667335)
          ·
            refine ⟨36170490021964468775501003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24113660014642979183667335 36170490021964468775501003)
            ·
              refine ⟨54255735032946703163251505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36170490021964468775501003 54255735032946703163251505)
              ·
                refine ⟨40691801274710027372438629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54255735032946703163251505 40691801274710027372438629)
                ·
                  refine ⟨7629712739008130132332243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40691801274710027372438629 7629712739008130132332243)
                  ·
                    refine ⟨11444569108512195198498365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7629712739008130132332243 11444569108512195198498365)
                    ·
                      refine ⟨4291713415692073199436887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11444569108512195198498365 4291713415692073199436887)
                      ·
                        rfl

theorem cell23_8358082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_8358082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358082 prefixEnd_8358082 := by exact prefixLift 8358082
  have htrace : WordTrace (prefixWord ++ tailWord_8358082) baseStart_8358082 baseEnd_8358082 := by
    simpa [prefixWord, tailWord_8358082, baseEnd_8358082] using wordTrace_append hprefix tailTrace_8358082
  have hstable : (prefixWord ++ tailWord_8358082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358082).length < 2 ^ (prefixWord ++ tailWord_8358082).sum := by decide
  have hdescent : baseEnd_8358082 < baseStart_8358082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358245 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 3, 1, 3]
def baseStart_8358245 : Nat := 118140960795 + 8358245 * 2 ^ 59
def prefixEnd_8358245 : Nat := 4983230072969 + 3 ^ 40 * 8358245 * 2
def baseEnd_8358245 : Nat := 4291797113038756061698637

theorem tailTrace_8358245 : CollatzResearch.WordTrace tailWord_8358245 prefixEnd_8358245 4291797113038756061698637 := by
  unfold tailWord_8358245
  simp only [CollatzResearch.WordTrace]
  refine ⟨304850239604513314444052189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203233493069675542962701459 304850239604513314444052189)
  ·
    refine ⟨114318839851692492916519571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304850239604513314444052189 114318839851692492916519571)
    ·
      refine ⟨171478259777538739374779357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114318839851692492916519571 171478259777538739374779357)
      ·
        refine ⟨64304347416577027265542259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171478259777538739374779357 64304347416577027265542259)
        ·
          refine ⟨96456521124865540898313389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64304347416577027265542259 96456521124865540898313389)
          ·
            refine ⟨36171195421824577836867521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96456521124865540898313389 36171195421824577836867521)
            ·
              refine ⟨27128396566368433377650641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36171195421824577836867521 27128396566368433377650641)
              ·
                refine ⟨20346297424776325033237981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27128396566368433377650641 20346297424776325033237981)
                ·
                  refine ⟨7629861534291121887464243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20346297424776325033237981 7629861534291121887464243)
                  ·
                    refine ⟨11444792301436682831196365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7629861534291121887464243 11444792301436682831196365)
                    ·
                      refine ⟨4291797113038756061698637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11444792301436682831196365 4291797113038756061698637)
                      ·
                        rfl

theorem cell23_8358245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_8358245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358245 prefixEnd_8358245 := by exact prefixLift 8358245
  have htrace : WordTrace (prefixWord ++ tailWord_8358245) baseStart_8358245 baseEnd_8358245 := by
    simpa [prefixWord, tailWord_8358245, baseEnd_8358245] using wordTrace_append hprefix tailTrace_8358245
  have hstable : (prefixWord ++ tailWord_8358245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358245).length < 2 ^ (prefixWord ++ tailWord_8358245).sum := by decide
  have hdescent : baseEnd_8358245 < baseStart_8358245 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358271 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 5]
def baseStart_8358271 : Nat := 118140960795 + 8358271 * 2 ^ 59
def prefixEnd_8358271 : Nat := 4983230072969 + 3 ^ 40 * 8358271 * 2
def baseEnd_8358271 : Nat := 4291810463535772959973517

theorem tailTrace_8358271 : CollatzResearch.WordTrace tailWord_8358271 prefixEnd_8358271 4291810463535772959973517 := by
  unfold tailWord_8358271
  simp only [CollatzResearch.WordTrace]
  refine ⟨304851187902419120884498667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203234125268279413922999111 304851187902419120884498667)
  ·
    refine ⟨457276781853628681326748001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304851187902419120884498667 457276781853628681326748001)
    ·
      refine ⟨342957586390221510995061001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457276781853628681326748001 342957586390221510995061001)
      ·
        refine ⟨257218189792666133246295751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342957586390221510995061001 257218189792666133246295751)
        ·
          refine ⟨385827284688999199869443627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257218189792666133246295751 385827284688999199869443627)
          ·
            refine ⟨578740927033498799804165441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385827284688999199869443627 578740927033498799804165441)
            ·
              refine ⟨434055695275124099853124081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578740927033498799804165441 434055695275124099853124081)
              ·
                refine ⟨325541771456343074889843061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434055695275124099853124081 325541771456343074889843061)
                ·
                  refine ⟨30519541074032163270922787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 325541771456343074889843061 30519541074032163270922787)
                  ·
                    refine ⟨45779311611048244906384181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30519541074032163270922787 45779311611048244906384181)
                    ·
                      refine ⟨4291810463535772959973517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45779311611048244906384181 4291810463535772959973517)
                      ·
                        rfl

theorem cell23_8358271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_8358271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358271 prefixEnd_8358271 := by exact prefixLift 8358271
  have htrace : WordTrace (prefixWord ++ tailWord_8358271) baseStart_8358271 baseEnd_8358271 := by
    simpa [prefixWord, tailWord_8358271, baseEnd_8358271] using wordTrace_append hprefix tailTrace_8358271
  have hstable : (prefixWord ++ tailWord_8358271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358271).length < 2 ^ (prefixWord ++ tailWord_8358271).sum := by decide
  have hdescent : baseEnd_8358271 < baseStart_8358271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358279 : List Nat := [1, 1, 4, 2, 2, 1, 5, 2, 1, 1, 3]
def baseStart_8358279 : Nat := 118140960795 + 8358279 * 2 ^ 59
def prefixEnd_8358279 : Nat := 4983230072969 + 3 ^ 40 * 8358279 * 2
def baseEnd_8358279 : Nat := 4291814571381008928673481

theorem tailTrace_8358279 : CollatzResearch.WordTrace tailWord_8358279 prefixEnd_8358279 4291814571381008928673481 := by
  unfold tailWord_8358279
  simp only [CollatzResearch.WordTrace]
  refine ⟨304851479686390138250789891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203234319790926758833859927 304851479686390138250789891)
  ·
    refine ⟨457277219529585207376184837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304851479686390138250789891 457277219529585207376184837)
    ·
      refine ⟨85739478661797226383034657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457277219529585207376184837 85739478661797226383034657)
      ·
        refine ⟨64304608996347919787275993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85739478661797226383034657 64304608996347919787275993)
        ·
          refine ⟨48228456747260939840456995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64304608996347919787275993 48228456747260939840456995)
          ·
            refine ⟨72342685120891409760685493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48228456747260939840456995 72342685120891409760685493)
            ·
              refine ⟨6782126730083569665064265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72342685120891409760685493 6782126730083569665064265)
              ·
                refine ⟨5086595047562677248798199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6782126730083569665064265 5086595047562677248798199)
                ·
                  refine ⟨7629892571344015873197299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5086595047562677248798199 7629892571344015873197299)
                  ·
                    refine ⟨11444838857016023809795949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7629892571344015873197299 11444838857016023809795949)
                    ·
                      refine ⟨4291814571381008928673481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11444838857016023809795949 4291814571381008928673481)
                      ·
                        rfl

theorem cell23_8358279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_8358279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358279 prefixEnd_8358279 := by exact prefixLift 8358279
  have htrace : WordTrace (prefixWord ++ tailWord_8358279) baseStart_8358279 baseEnd_8358279 := by
    simpa [prefixWord, tailWord_8358279, baseEnd_8358279] using wordTrace_append hprefix tailTrace_8358279
  have hstable : (prefixWord ++ tailWord_8358279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358279).length < 2 ^ (prefixWord ++ tailWord_8358279).sum := by decide
  have hdescent : baseEnd_8358279 < baseStart_8358279 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358298 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_8358298 : Nat := 118140960795 + 8358298 * 2 ^ 59
def prefixEnd_8358298 : Nat := 4983230072969 + 3 ^ 40 * 8358298 * 2
def baseEnd_8358298 : Nat := 4291824327513444354335893

theorem tailTrace_8358298 : CollatzResearch.WordTrace tailWord_8358298 prefixEnd_8358298 4291824327513444354335893 := by
  unfold tailWord_8358298
  simp only [CollatzResearch.WordTrace]
  refine ⟨76213043168330326123932887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203234781782214202997154365 76213043168330326123932887)
  ·
    refine ⟨114319564752495489185899331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76213043168330326123932887 114319564752495489185899331)
    ·
      refine ⟨171479347128743233778848997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114319564752495489185899331 171479347128743233778848997)
      ·
        refine ⟨32152377586639356333534187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171479347128743233778848997 32152377586639356333534187)
        ·
          refine ⟨48228566379959034500301281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32152377586639356333534187 48228566379959034500301281)
          ·
            refine ⟨36171424784969275875225961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48228566379959034500301281 36171424784969275875225961)
            ·
              refine ⟨27128568588726956906419471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36171424784969275875225961 27128568588726956906419471)
              ·
                refine ⟨40692852883090435359629207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27128568588726956906419471 40692852883090435359629207)
                ·
                  refine ⟨61039279324635653039443811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40692852883090435359629207 61039279324635653039443811)
                  ·
                    refine ⟨91558918986953479559165717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61039279324635653039443811 91558918986953479559165717)
                    ·
                      refine ⟨4291824327513444354335893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91558918986953479559165717 4291824327513444354335893)
                      ·
                        rfl

theorem cell23_8358298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_8358298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358298 prefixEnd_8358298 := by exact prefixLift 8358298
  have htrace : WordTrace (prefixWord ++ tailWord_8358298) baseStart_8358298 baseEnd_8358298 := by
    simpa [prefixWord, tailWord_8358298, baseEnd_8358298] using wordTrace_append hprefix tailTrace_8358298
  have hstable : (prefixWord ++ tailWord_8358298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358298).length < 2 ^ (prefixWord ++ tailWord_8358298).sum := by decide
  have hdescent : baseEnd_8358298 < baseStart_8358298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358302 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_8358302 : Nat := 118140960795 + 8358302 * 2 ^ 59
def prefixEnd_8358302 : Nat := 4983230072969 + 3 ^ 40 * 8358302 * 2
def baseEnd_8358302 : Nat := 4291826381436062338685875

theorem tailTrace_8358302 : CollatzResearch.WordTrace tailWord_8358302 prefixEnd_8358302 4291826381436062338685875 := by
  unfold tailWord_8358302
  simp only [CollatzResearch.WordTrace]
  refine ⟨38106539820663351647359645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203234879043537875452584773 38106539820663351647359645)
  ·
    refine ⟨14289952432748756867759867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38106539820663351647359645 14289952432748756867759867)
    ·
      refine ⟨21434928649123135301639801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14289952432748756867759867 21434928649123135301639801)
      ·
        refine ⟨16076196486842351476229851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21434928649123135301639801 16076196486842351476229851)
        ·
          refine ⟨24114294730263527214344777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16076196486842351476229851 24114294730263527214344777)
          ·
            refine ⟨18085721047697645410758583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24114294730263527214344777 18085721047697645410758583)
            ·
              refine ⟨27128581571546468116137875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18085721047697645410758583 27128581571546468116137875)
              ·
                refine ⟨40692872357319702174206813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27128581571546468116137875 40692872357319702174206813)
                ·
                  refine ⟨15259827133994888315327555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40692872357319702174206813 15259827133994888315327555)
                  ·
                    refine ⟨22889740700992332472991333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15259827133994888315327555 22889740700992332472991333)
                    ·
                      refine ⟨4291826381436062338685875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22889740700992332472991333 4291826381436062338685875)
                      ·
                        rfl

theorem cell23_8358302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_8358302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358302 prefixEnd_8358302 := by exact prefixLift 8358302
  have htrace : WordTrace (prefixWord ++ tailWord_8358302) baseStart_8358302 baseEnd_8358302 := by
    simpa [prefixWord, tailWord_8358302, baseEnd_8358302] using wordTrace_append hprefix tailTrace_8358302
  have hstable : (prefixWord ++ tailWord_8358302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358302).length < 2 ^ (prefixWord ++ tailWord_8358302).sum := by decide
  have hdescent : baseEnd_8358302 < baseStart_8358302 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358322 : List Nat := [3, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3]
def baseStart_8358322 : Nat := 118140960795 + 8358322 * 2 ^ 59
def prefixEnd_8358322 : Nat := 4983230072969 + 3 ^ 40 * 8358322 * 2
def baseEnd_8358322 : Nat := 4291836651049152260435783

theorem tailTrace_8358322 : CollatzResearch.WordTrace tailWord_8358322 prefixEnd_8358322 4291836651049152260435783 := by
  unfold tailWord_8358322
  simp only [CollatzResearch.WordTrace]
  refine ⟨76213262006308589148651305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203235365350156237729736813 76213262006308589148651305)
  ·
    refine ⟨57159946504731441861488479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76213262006308589148651305 57159946504731441861488479)
    ·
      refine ⟨85739919757097162792232719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57159946504731441861488479 85739919757097162792232719)
      ·
        refine ⟨128609879635645744188349079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85739919757097162792232719 128609879635645744188349079)
        ·
          refine ⟨192914819453468616282523619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128609879635645744188349079 192914819453468616282523619)
          ·
            refine ⟨289372229180202924423785429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192914819453468616282523619 289372229180202924423785429)
            ·
              refine ⟨6782161621411006041182471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 289372229180202924423785429 6782161621411006041182471)
              ·
                refine ⟨10173242432116509061773707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6782161621411006041182471 10173242432116509061773707)
                ·
                  refine ⟨15259863648174763592660561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10173242432116509061773707 15259863648174763592660561)
                  ·
                    refine ⟨11444897736131072694495421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15259863648174763592660561 11444897736131072694495421)
                    ·
                      refine ⟨4291836651049152260435783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11444897736131072694495421 4291836651049152260435783)
                      ·
                        rfl

theorem cell23_8358322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_8358322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358322 prefixEnd_8358322 := by exact prefixLift 8358322
  have htrace : WordTrace (prefixWord ++ tailWord_8358322) baseStart_8358322 baseEnd_8358322 := by
    simpa [prefixWord, tailWord_8358322, baseEnd_8358322] using wordTrace_append hprefix tailTrace_8358322
  have hstable : (prefixWord ++ tailWord_8358322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358322).length < 2 ^ (prefixWord ++ tailWord_8358322).sum := by decide
  have hdescent : baseEnd_8358322 < baseStart_8358322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358345 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 3, 3, 2]
def baseStart_8358345 : Nat := 118140960795 + 8358345 * 2 ^ 59
def prefixEnd_8358345 : Nat := 4983230072969 + 3 ^ 40 * 8358345 * 2
def baseEnd_8358345 : Nat := 4291848461104205670448177

theorem tailTrace_8358345 : CollatzResearch.WordTrace tailWord_8358345 prefixEnd_8358345 4291848461104205670448177 := by
  unfold tailWord_8358345
  simp only [CollatzResearch.WordTrace]
  refine ⟨304853886904151031522692489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203235924602767354348461659 304853886904151031522692489)
  ·
    refine ⟨228640415178113273642019367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304853886904151031522692489 228640415178113273642019367)
    ·
      refine ⟨342960622767169910463029051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228640415178113273642019367 342960622767169910463029051)
      ·
        refine ⟨514440934150754865694543577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342960622767169910463029051 514440934150754865694543577)
        ·
          refine ⟨385830700613066149270907683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514440934150754865694543577 385830700613066149270907683)
          ·
            refine ⟨578746050919599223906361525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385830700613066149270907683 578746050919599223906361525)
            ·
              refine ⟨54257442273712427241221393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 578746050919599223906361525 54257442273712427241221393)
              ·
                refine ⟨40693081705284320430916045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54257442273712427241221393 40693081705284320430916045)
                ·
                  refine ⟨15259905639481620161593517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40693081705284320430916045 15259905639481620161593517)
                  ·
                    refine ⟨5722464614805607560597569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15259905639481620161593517 5722464614805607560597569)
                    ·
                      refine ⟨4291848461104205670448177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5722464614805607560597569 4291848461104205670448177)
                      ·
                        rfl

theorem cell23_8358345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 3, 2].length) (baseStart_8358345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358345 prefixEnd_8358345 := by exact prefixLift 8358345
  have htrace : WordTrace (prefixWord ++ tailWord_8358345) baseStart_8358345 baseEnd_8358345 := by
    simpa [prefixWord, tailWord_8358345, baseEnd_8358345] using wordTrace_append hprefix tailTrace_8358345
  have hstable : (prefixWord ++ tailWord_8358345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358345).length < 2 ^ (prefixWord ++ tailWord_8358345).sum := by decide
  have hdescent : baseEnd_8358345 < baseStart_8358345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358362 : List Nat := [3, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2]
def baseStart_8358362 : Nat := 118140960795 + 8358362 * 2 ^ 59
def prefixEnd_8358362 : Nat := 4983230072969 + 3 ^ 40 * 8358362 * 2
def baseEnd_8358362 : Nat := 4291857190275332103935599

theorem tailTrace_8358362 : CollatzResearch.WordTrace tailWord_8358362 prefixEnd_8358362 4291857190275332103935599 := by
  unfold tailWord_8358362
  simp only [CollatzResearch.WordTrace]
  refine ⟨76213626736272360856515335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203236337963392962284040893 76213626736272360856515335)
  ·
    refine ⟨114320440104408541284773003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76213626736272360856515335 114320440104408541284773003)
    ·
      refine ⟨171480660156612811927159505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114320440104408541284773003 171480660156612811927159505)
      ·
        refine ⟨128610495117459608945369629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171480660156612811927159505 128610495117459608945369629)
        ·
          refine ⟨48228935669047353354513611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128610495117459608945369629 48228935669047353354513611)
          ·
            refine ⟨72343403503571030031770417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48228935669047353354513611 72343403503571030031770417)
            ·
              refine ⟨54257552627678272523827813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72343403503571030031770417 54257552627678272523827813)
              ·
                refine ⟨10173291117689676098217715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54257552627678272523827813 10173291117689676098217715)
                ·
                  refine ⟨15259936676534514147326573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10173291117689676098217715 15259936676534514147326573)
                  ·
                    refine ⟨5722476253700442805247465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15259936676534514147326573 5722476253700442805247465)
                    ·
                      refine ⟨4291857190275332103935599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5722476253700442805247465 4291857190275332103935599)
                      ·
                        rfl

theorem cell23_8358362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_8358362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358362 prefixEnd_8358362 := by exact prefixLift 8358362
  have htrace : WordTrace (prefixWord ++ tailWord_8358362) baseStart_8358362 baseEnd_8358362 := by
    simpa [prefixWord, tailWord_8358362, baseEnd_8358362] using wordTrace_append hprefix tailTrace_8358362
  have hstable : (prefixWord ++ tailWord_8358362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358362).length < 2 ^ (prefixWord ++ tailWord_8358362).sum := by decide
  have hdescent : baseEnd_8358362 < baseStart_8358362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8358370 : List Nat := [3, 3, 3, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_8358370 : Nat := 118140960795 + 8358370 * 2 ^ 59
def prefixEnd_8358370 : Nat := 4983230072969 + 3 ^ 40 * 8358370 * 2
def baseEnd_8358370 : Nat := 4291861298120568072635563

theorem tailTrace_8358370 : CollatzResearch.WordTrace tailWord_8358370 prefixEnd_8358370 4291861298120568072635563 := by
  unfold tailWord_8358370
  simp only [CollatzResearch.WordTrace]
  refine ⟨76213699682265115198088141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203236532486040307194901709 76213699682265115198088141)
  ·
    refine ⟨28580137380849418199283053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76213699682265115198088141 28580137380849418199283053)
    ·
      refine ⟨10717551517818531824731145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28580137380849418199283053 10717551517818531824731145)
      ·
        refine ⟨8038163638363898868548359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10717551517818531824731145 8038163638363898868548359)
        ·
          refine ⟨12057245457545848302822539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8038163638363898868548359 12057245457545848302822539)
          ·
            refine ⟨18085868186318772454233809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12057245457545848302822539 18085868186318772454233809)
            ·
              refine ⟨13564401139739079340675357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18085868186318772454233809 13564401139739079340675357)
              ·
                refine ⟨5086650427402154752753259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13564401139739079340675357 5086650427402154752753259)
                ·
                  refine ⟨7629975641103232129129889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5086650427402154752753259 7629975641103232129129889)
                  ·
                    refine ⟨5722481730827424096847417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7629975641103232129129889 5722481730827424096847417)
                    ·
                      refine ⟨4291861298120568072635563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5722481730827424096847417 4291861298120568072635563)
                      ·
                        rfl

theorem cell23_8358370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_8358370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8358370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8358370 prefixEnd_8358370 := by exact prefixLift 8358370
  have htrace : WordTrace (prefixWord ++ tailWord_8358370) baseStart_8358370 baseEnd_8358370 := by
    simpa [prefixWord, tailWord_8358370, baseEnd_8358370] using wordTrace_append hprefix tailTrace_8358370
  have hstable : (prefixWord ++ tailWord_8358370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8358370).length < 2 ^ (prefixWord ++ tailWord_8358370).sum := by decide
  have hdescent : baseEnd_8358370 < baseStart_8358370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8358370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
