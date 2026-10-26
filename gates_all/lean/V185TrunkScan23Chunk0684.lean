import V185TrunkScan23Chunk0683

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4044594 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2]
def baseStart_4044594 : Nat := 118140960795 + 4044594 * 2 ^ 59
def prefixEnd_4044594 : Nat := 4983230072969 + 3 ^ 40 * 4044594 * 2
def baseEnd_4044594 : Nat := 2076820774291053741074257

theorem tailTrace_4044594 : CollatzResearch.WordTrace tailWord_4044594 prefixEnd_4044594 2076820774291053741074257 := by
  unfold tailWord_4044594
  simp only [CollatzResearch.WordTrace]
  refine ⟨36879615577283543626491209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98345641539422783003976557 36879615577283543626491209)
  ·
    refine ⟨27659711682962657719868407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36879615577283543626491209 27659711682962657719868407)
    ·
      refine ⟨41489567524443986579802611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27659711682962657719868407 41489567524443986579802611)
      ·
        refine ⟨62234351286665979869703917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41489567524443986579802611 62234351286665979869703917)
        ·
          refine ⟨23337881732499742451138969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62234351286665979869703917 23337881732499742451138969)
          ·
            refine ⟨17503411299374806838354227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23337881732499742451138969 17503411299374806838354227)
            ·
              refine ⟨26255116949062210257531341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17503411299374806838354227 26255116949062210257531341)
              ·
                refine ⟨9845668855898328846574253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26255116949062210257531341 9845668855898328846574253)
                ·
                  refine ⟨3692125820961873317465345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9845668855898328846574253 3692125820961873317465345)
                  ·
                    refine ⟨2769094365721404988099009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3692125820961873317465345 2769094365721404988099009)
                    ·
                      refine ⟨2076820774291053741074257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769094365721404988099009 2076820774291053741074257)
                      ·
                        rfl

theorem cell23_4044594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_4044594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044594 prefixEnd_4044594 := by exact prefixLift 4044594
  have htrace : WordTrace (prefixWord ++ tailWord_4044594) baseStart_4044594 baseEnd_4044594 := by
    simpa [prefixWord, tailWord_4044594, baseEnd_4044594] using wordTrace_append hprefix tailTrace_4044594
  have hstable : (prefixWord ++ tailWord_4044594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044594).length < 2 ^ (prefixWord ++ tailWord_4044594).sum := by decide
  have hdescent : baseEnd_4044594 < baseStart_4044594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044597 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_4044597 : Nat := 118140960795 + 4044597 * 2 ^ 59
def prefixEnd_4044597 : Nat := 4983230072969 + 3 ^ 40 * 4044597 * 2
def baseEnd_4044597 : Nat := 2076822314733017229336743

theorem tailTrace_4044597 : CollatzResearch.WordTrace tailWord_4044597 prefixEnd_4044597 2076822314733017229336743 := by
  unfold tailWord_4044597
  simp only [CollatzResearch.WordTrace]
  refine ⟨147518571728123306018324045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98345714485415537345549363 147518571728123306018324045)
  ·
    refine ⟨55319464398046239756871517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147518571728123306018324045 55319464398046239756871517)
    ·
      refine ⟨20744799149267339908826819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55319464398046239756871517 20744799149267339908826819)
      ·
        refine ⟨31117198723901009863240229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20744799149267339908826819 31117198723901009863240229)
        ·
          refine ⟨5834474760731439349357543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31117198723901009863240229 5834474760731439349357543)
          ·
            refine ⟨8751712141097159024036315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5834474760731439349357543 8751712141097159024036315)
            ·
              refine ⟨13127568211645738536054473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8751712141097159024036315 13127568211645738536054473)
              ·
                refine ⟨9845676158734303902040855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13127568211645738536054473 9845676158734303902040855)
                ·
                  refine ⟨14768514238101455853061283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9845676158734303902040855 14768514238101455853061283)
                  ·
                    refine ⟨22152771357152183779591925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14768514238101455853061283 22152771357152183779591925)
                    ·
                      refine ⟨2076822314733017229336743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22152771357152183779591925 2076822314733017229336743)
                      ·
                        rfl

theorem cell23_4044597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_4044597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044597 prefixEnd_4044597 := by exact prefixLift 4044597
  have htrace : WordTrace (prefixWord ++ tailWord_4044597) baseStart_4044597 baseEnd_4044597 := by
    simpa [prefixWord, tailWord_4044597, baseEnd_4044597] using wordTrace_append hprefix tailTrace_4044597
  have hstable : (prefixWord ++ tailWord_4044597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044597).length < 2 ^ (prefixWord ++ tailWord_4044597).sum := by decide
  have hdescent : baseEnd_4044597 < baseStart_4044597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044628 : List Nat := [2, 4, 1, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_4044628 : Nat := 118140960795 + 4044628 * 2 ^ 59
def prefixEnd_4044628 : Nat := 4983230072969 + 3 ^ 40 * 4044628 * 2
def baseEnd_4044628 : Nat := 2076838232633306608049101

theorem tailTrace_4044628 : CollatzResearch.WordTrace tailWord_4044628 prefixEnd_4044628 2076838232633306608049101 := by
  unfold tailWord_4044628
  simp only [CollatzResearch.WordTrace]
  refine ⟨73759851195505499156351269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98346468260673998875135025 73759851195505499156351269)
  ·
    refine ⟨13829972099157281091815863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73759851195505499156351269 13829972099157281091815863)
    ·
      refine ⟨20744958148735921637723795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13829972099157281091815863 20744958148735921637723795)
      ·
        refine ⟨31117437223103882456585693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20744958148735921637723795 31117437223103882456585693)
        ·
          refine ⟨11669038958663955921219635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31117437223103882456585693 11669038958663955921219635)
          ·
            refine ⟨17503558437995933881829453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11669038958663955921219635 17503558437995933881829453)
            ·
              refine ⟨6563834414248475205686045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17503558437995933881829453 6563834414248475205686045)
              ·
                refine ⟨2461437905343178202132267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6563834414248475205686045 2461437905343178202132267)
                ·
                  refine ⟨3692156858014767303198401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461437905343178202132267 3692156858014767303198401)
                  ·
                    refine ⟨2769117643511075477398801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3692156858014767303198401 2769117643511075477398801)
                    ·
                      refine ⟨2076838232633306608049101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769117643511075477398801 2076838232633306608049101)
                      ·
                        rfl

theorem cell23_4044628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_4044628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044628 prefixEnd_4044628 := by exact prefixLift 4044628
  have htrace : WordTrace (prefixWord ++ tailWord_4044628) baseStart_4044628 baseEnd_4044628 := by
    simpa [prefixWord, tailWord_4044628, baseEnd_4044628] using wordTrace_append hprefix tailTrace_4044628
  have hstable : (prefixWord ++ tailWord_4044628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044628).length < 2 ^ (prefixWord ++ tailWord_4044628).sum := by decide
  have hdescent : baseEnd_4044628 < baseStart_4044628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044667 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 1, 4, 2]
def baseStart_4044667 : Nat := 118140960795 + 4044667 * 2 ^ 59
def prefixEnd_4044667 : Nat := 4983230072969 + 3 ^ 40 * 4044667 * 2
def baseEnd_4044667 : Nat := 2076858258378831955461421

theorem tailTrace_4044667 : CollatzResearch.WordTrace tailWord_4044667 prefixEnd_4044667 2076858258378831955461421 := by
  unfold tailWord_4044667
  simp only [CollatzResearch.WordTrace]
  refine ⟨147521124837869707973372255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98347416558579805315581503 147521124837869707973372255)
  ·
    refine ⟨221281687256804561960058383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147521124837869707973372255 221281687256804561960058383)
    ·
      refine ⟨331922530885206842940087575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221281687256804561960058383 331922530885206842940087575)
      ·
        refine ⟨497883796327810264410131363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331922530885206842940087575 497883796327810264410131363)
        ·
          refine ⟨746825694491715396615197045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497883796327810264410131363 746825694491715396615197045)
          ·
            refine ⟨70014908858598318432674723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 746825694491715396615197045 70014908858598318432674723)
            ·
              refine ⟨105022363287897477649012085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70014908858598318432674723 105022363287897477649012085)
              ·
                refine ⟨9845846558240388529594883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105022363287897477649012085 9845846558240388529594883)
                ·
                  refine ⟨14768769837360582794392325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9845846558240388529594883 14768769837360582794392325)
                  ·
                    refine ⟨2769144344505109273948561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14768769837360582794392325 2769144344505109273948561)
                    ·
                      refine ⟨2076858258378831955461421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769144344505109273948561 2076858258378831955461421)
                      ·
                        rfl

theorem cell23_4044667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 4, 2].length) (baseStart_4044667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044667 prefixEnd_4044667 := by exact prefixLift 4044667
  have htrace : WordTrace (prefixWord ++ tailWord_4044667) baseStart_4044667 baseEnd_4044667 := by
    simpa [prefixWord, tailWord_4044667, baseEnd_4044667] using wordTrace_append hprefix tailTrace_4044667
  have hstable : (prefixWord ++ tailWord_4044667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044667).length < 2 ^ (prefixWord ++ tailWord_4044667).sum := by decide
  have hdescent : baseEnd_4044667 < baseStart_4044667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044701 : List Nat := [1, 4, 2, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_4044701 : Nat := 118140960795 + 4044701 * 2 ^ 59
def prefixEnd_4044701 : Nat := 4983230072969 + 3 ^ 40 * 4044701 * 2
def baseEnd_4044701 : Nat := 2076875716721084822436265

theorem tailTrace_4044701 : CollatzResearch.WordTrace tailWord_4044701 prefixEnd_4044701 2076875716721084822436265 := by
  unfold tailWord_4044701
  simp only [CollatzResearch.WordTrace]
  refine ⟨147522364919746531780109957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98348243279831021186739971 147522364919746531780109957)
  ·
    refine ⟨27660443422452474708770617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147522364919746531780109957 27660443422452474708770617)
    ·
      refine ⟨20745332566839356031577963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27660443422452474708770617 20745332566839356031577963)
      ·
        refine ⟨31117998850259034047366945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20745332566839356031577963 31117998850259034047366945)
        ·
          refine ⟨23338499137694275535525209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31117998850259034047366945 23338499137694275535525209)
          ·
            refine ⟨17503874353270706651643907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23338499137694275535525209 17503874353270706651643907)
            ·
              refine ⟨26255811529906059977465861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17503874353270706651643907 26255811529906059977465861)
              ·
                refine ⟨4922964661857386245774849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26255811529906059977465861 4922964661857386245774849)
                ·
                  refine ⟨3692223496393039684331137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4922964661857386245774849 3692223496393039684331137)
                  ·
                    refine ⟨2769167622294779763248353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3692223496393039684331137 2769167622294779763248353)
                    ·
                      refine ⟨2076875716721084822436265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769167622294779763248353 2076875716721084822436265)
                      ·
                        rfl

theorem cell23_4044701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_4044701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044701 prefixEnd_4044701 := by exact prefixLift 4044701
  have htrace : WordTrace (prefixWord ++ tailWord_4044701) baseStart_4044701 baseEnd_4044701 := by
    simpa [prefixWord, tailWord_4044701, baseEnd_4044701] using wordTrace_append hprefix tailTrace_4044701
  have hstable : (prefixWord ++ tailWord_4044701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044701).length < 2 ^ (prefixWord ++ tailWord_4044701).sum := by decide
  have hdescent : baseEnd_4044701 < baseStart_4044701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044727 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 4, 5, 2]
def baseStart_4044727 : Nat := 118140960795 + 4044727 * 2 ^ 59
def prefixEnd_4044727 : Nat := 4983230072969 + 3 ^ 40 * 4044727 * 2
def baseEnd_4044727 : Nat := 2076889067218101720711145

theorem tailTrace_4044727 : CollatzResearch.WordTrace tailWord_4044727 prefixEnd_4044727 2076889067218101720711145 := by
  unfold tailWord_4044727
  simp only [CollatzResearch.WordTrace]
  refine ⟨147523313217652338220556435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98348875478434892147037623 147523313217652338220556435)
  ·
    refine ⟨221284969826478507330834653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147523313217652338220556435 221284969826478507330834653)
    ·
      refine ⟨82981863684929440249062995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221284969826478507330834653 82981863684929440249062995)
      ·
        refine ⟨124472795527394160373594493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82981863684929440249062995 124472795527394160373594493)
        ·
          refine ⟨46677298322772810140097935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124472795527394160373594493 46677298322772810140097935)
          ·
            refine ⟨70015947484159215210146903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46677298322772810140097935 70015947484159215210146903)
            ·
              refine ⟨105023921226238822815220355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70015947484159215210146903 105023921226238822815220355)
              ·
                refine ⟨157535881839358234222830533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105023921226238822815220355 157535881839358234222830533)
                ·
                  refine ⟨29537977844879668916780725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157535881839358234222830533 29537977844879668916780725)
                  ·
                    refine ⟨2769185422957468960948193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29537977844879668916780725 2769185422957468960948193)
                    ·
                      refine ⟨2076889067218101720711145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769185422957468960948193 2076889067218101720711145)
                      ·
                        rfl

theorem cell23_4044727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 5, 2].length) (baseStart_4044727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044727 prefixEnd_4044727 := by exact prefixLift 4044727
  have htrace : WordTrace (prefixWord ++ tailWord_4044727) baseStart_4044727 baseEnd_4044727 := by
    simpa [prefixWord, tailWord_4044727, baseEnd_4044727] using wordTrace_append hprefix tailTrace_4044727
  have hstable : (prefixWord ++ tailWord_4044727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044727).length < 2 ^ (prefixWord ++ tailWord_4044727).sum := by decide
  have hdescent : baseEnd_4044727 < baseStart_4044727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044730 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_4044730 : Nat := 118140960795 + 4044730 * 2 ^ 59
def prefixEnd_4044730 : Nat := 4983230072969 + 3 ^ 40 * 4044730 * 2
def baseEnd_4044730 : Nat := 2076890607660065208973631

theorem tailTrace_4044730 : CollatzResearch.WordTrace tailWord_4044730 prefixEnd_4044730 2076890607660065208973631 := by
  unfold tailWord_4044730
  simp only [CollatzResearch.WordTrace]
  refine ⟨36880855659160367433228911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98348948424427646488610429 36880855659160367433228911)
  ·
    refine ⟨55321283488740551149843367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36880855659160367433228911 55321283488740551149843367)
    ·
      refine ⟨82981925233110826724765051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55321283488740551149843367 82981925233110826724765051)
      ·
        refine ⟨124472887849666240087147577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82981925233110826724765051 124472887849666240087147577)
        ·
          refine ⟨93354665887249680065360683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124472887849666240087147577 93354665887249680065360683)
          ·
            refine ⟨140031998830874520098041025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93354665887249680065360683 140031998830874520098041025)
            ·
              refine ⟨105023999123155890073530769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140031998830874520098041025 105023999123155890073530769)
              ·
                refine ⟨78767999342366917555148077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105023999123155890073530769 78767999342366917555148077)
                ·
                  refine ⟨29537999753387594083180529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78767999342366917555148077 29537999753387594083180529)
                  ·
                    refine ⟨22153499815040695562385397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29537999753387594083180529 22153499815040695562385397)
                    ·
                      refine ⟨2076890607660065208973631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22153499815040695562385397 2076890607660065208973631)
                      ·
                        rfl

theorem cell23_4044730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_4044730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044730 prefixEnd_4044730 := by exact prefixLift 4044730
  have htrace : WordTrace (prefixWord ++ tailWord_4044730) baseStart_4044730 baseEnd_4044730 := by
    simpa [prefixWord, tailWord_4044730, baseEnd_4044730] using wordTrace_append hprefix tailTrace_4044730
  have hstable : (prefixWord ++ tailWord_4044730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044730).length < 2 ^ (prefixWord ++ tailWord_4044730).sum := by decide
  have hdescent : baseEnd_4044730 < baseStart_4044730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044800 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 8]
def baseStart_4044800 : Nat := 118140960795 + 4044800 * 2 ^ 59
def prefixEnd_4044800 : Nat := 4983230072969 + 3 ^ 40 * 4044800 * 2
def baseEnd_4044800 : Nat := 2076926551305879935098309

theorem tailTrace_4044800 : CollatzResearch.WordTrace tailWord_4044800 prefixEnd_4044800 2076926551305879935098309 := by
  unfold tailWord_4044800
  simp only [CollatzResearch.WordTrace]
  refine ⟨73762987873193935843981927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98350650497591914458642569 73762987873193935843981927)
  ·
    refine ⟨110644481809790903765972891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73762987873193935843981927 110644481809790903765972891)
    ·
      refine ⟨165966722714686355648959337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110644481809790903765972891 165966722714686355648959337)
      ·
        refine ⟨124475042036014766736719503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165966722714686355648959337 124475042036014766736719503)
        ·
          refine ⟨186712563054022150105079255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124475042036014766736719503 186712563054022150105079255)
          ·
            refine ⟨280068844581033225157618883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186712563054022150105079255 280068844581033225157618883)
            ·
              refine ⟨420103266871549837736428325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280068844581033225157618883 420103266871549837736428325)
              ·
                refine ⟨78769362538415594575580311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420103266871549837736428325 78769362538415594575580311)
                ·
                  refine ⟨118154043807623391863370467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78769362538415594575580311 118154043807623391863370467)
                  ·
                    refine ⟨177231065711435087795055701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118154043807623391863370467 177231065711435087795055701)
                    ·
                      refine ⟨2076926551305879935098309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 177231065711435087795055701 2076926551305879935098309)
                      ·
                        rfl

theorem cell23_4044800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_4044800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044800 prefixEnd_4044800 := by exact prefixLift 4044800
  have htrace : WordTrace (prefixWord ++ tailWord_4044800) baseStart_4044800 baseEnd_4044800 := by
    simpa [prefixWord, tailWord_4044800, baseEnd_4044800] using wordTrace_append hprefix tailTrace_4044800
  have hstable : (prefixWord ++ tailWord_4044800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044800).length < 2 ^ (prefixWord ++ tailWord_4044800).sum := by decide
  have hdescent : baseEnd_4044800 < baseStart_4044800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044861 : List Nat := [1, 4, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_4044861 : Nat := 118140960795 + 4044861 * 2 ^ 59
def prefixEnd_4044861 : Nat := 4983230072969 + 3 ^ 40 * 4044861 * 2
def baseEnd_4044861 : Nat := 692319291208601398811843

theorem tailTrace_4044861 : CollatzResearch.WordTrace tailWord_4044861 prefixEnd_4044861 692319291208601398811843 := by
  unfold tailWord_4044861
  simp only [CollatzResearch.WordTrace]
  refine ⟨147528200599166879105934437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98352133732777919403956291 147528200599166879105934437)
  ·
    refine ⟨27661537612343789832362707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147528200599166879105934437 27661537612343789832362707)
    ·
      refine ⟨41492306418515684748544061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27661537612343789832362707 41492306418515684748544061)
      ·
        refine ⟨15559614906943381780704023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41492306418515684748544061 15559614906943381780704023)
        ·
          refine ⟨23339422360415072671056035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15559614906943381780704023 23339422360415072671056035)
          ·
            refine ⟨35009133540622609006584053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23339422360415072671056035 35009133540622609006584053)
            ·
              refine ⟨3282106269433369594367255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35009133540622609006584053 3282106269433369594367255)
              ·
                refine ⟨4923159404150054391550883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3282106269433369594367255 4923159404150054391550883)
                ·
                  refine ⟨7384739106225081587326325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4923159404150054391550883 7384739106225081587326325)
                  ·
                    refine ⟨692319291208601398811843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7384739106225081587326325 692319291208601398811843)
                    ·
                      rfl

theorem cell23_4044861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_4044861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044861 prefixEnd_4044861 := by exact prefixLift 4044861
  have htrace : WordTrace (prefixWord ++ tailWord_4044861) baseStart_4044861 baseEnd_4044861 := by
    simpa [prefixWord, tailWord_4044861, baseEnd_4044861] using wordTrace_append hprefix tailTrace_4044861
  have hstable : (prefixWord ++ tailWord_4044861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044861).length < 2 ^ (prefixWord ++ tailWord_4044861).sum := by decide
  have hdescent : baseEnd_4044861 < baseStart_4044861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044867 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 5]
def baseStart_4044867 : Nat := 118140960795 + 4044867 * 2 ^ 59
def prefixEnd_4044867 : Nat := 4983230072969 + 3 ^ 40 * 4044867 * 2
def baseEnd_4044867 : Nat := 2076960954509731172960501

theorem tailTrace_4044867 : CollatzResearch.WordTrace tailWord_4044867 prefixEnd_4044867 2076960954509731172960501 := by
  unfold tailWord_4044867
  simp only [CollatzResearch.WordTrace]
  refine ⟨147528419437145142130652855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98352279624763428087101903 147528419437145142130652855)
  ·
    refine ⟨221292629155717713195979283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147528419437145142130652855 221292629155717713195979283)
    ·
      refine ⟨331938943733576569793968925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221292629155717713195979283 331938943733576569793968925)
      ·
        refine ⟨124477103900091213672738347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331938943733576569793968925 124477103900091213672738347)
        ·
          refine ⟨186715655850136820509107521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124477103900091213672738347 186715655850136820509107521)
          ·
            refine ⟨140036741887602615381830641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186715655850136820509107521 140036741887602615381830641)
            ·
              refine ⟨105027556415701961536372981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140036741887602615381830641 105027556415701961536372981)
              ·
                refine ⟨9846333413972058894034967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105027556415701961536372981 9846333413972058894034967)
                ·
                  refine ⟨14769500120958088341052451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9846333413972058894034967 14769500120958088341052451)
                  ·
                    refine ⟨22154250181437132511578677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14769500120958088341052451 22154250181437132511578677)
                    ·
                      refine ⟨2076960954509731172960501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22154250181437132511578677 2076960954509731172960501)
                      ·
                        rfl

theorem cell23_4044867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_4044867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044867 prefixEnd_4044867 := by exact prefixLift 4044867
  have htrace : WordTrace (prefixWord ++ tailWord_4044867) baseStart_4044867 baseEnd_4044867 := by
    simpa [prefixWord, tailWord_4044867, baseEnd_4044867] using wordTrace_append hprefix tailTrace_4044867
  have hstable : (prefixWord ++ tailWord_4044867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044867).length < 2 ^ (prefixWord ++ tailWord_4044867).sum := by decide
  have hdescent : baseEnd_4044867 < baseStart_4044867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044881 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 3, 2, 2]
def baseStart_4044881 : Nat := 118140960795 + 4044881 * 2 ^ 59
def prefixEnd_4044881 : Nat := 4983230072969 + 3 ^ 40 * 4044881 * 2
def baseEnd_4044881 : Nat := 2076968143238894118185437

theorem tailTrace_4044881 : CollatzResearch.WordTrace tailWord_4044881 prefixEnd_4044881 2076968143238894118185437 := by
  unfold tailWord_4044881
  simp only [CollatzResearch.WordTrace]
  refine ⟨147528930059094422521662497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98352620039396281681108331 147528930059094422521662497)
  ·
    refine ⟨110646697544320816891246873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147528930059094422521662497 110646697544320816891246873)
    ·
      refine ⟨82985023158240612668435155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110646697544320816891246873 82985023158240612668435155)
      ·
        refine ⟨124477534737360919002652733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82985023158240612668435155 124477534737360919002652733)
        ·
          refine ⟨46679075526510344625994775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124477534737360919002652733 46679075526510344625994775)
          ·
            refine ⟨70018613289765516938992163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46679075526510344625994775 70018613289765516938992163)
            ·
              refine ⟨105027919934648275408488245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70018613289765516938992163 105027919934648275408488245)
              ·
                refine ⟨9846367493873275819545773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105027919934648275408488245 9846367493873275819545773)
                ·
                  refine ⟨3692387810202478432329665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9846367493873275819545773 3692387810202478432329665)
                  ·
                    refine ⟨2769290857651858824247249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3692387810202478432329665 2769290857651858824247249)
                    ·
                      refine ⟨2076968143238894118185437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769290857651858824247249 2076968143238894118185437)
                      ·
                        rfl

theorem cell23_4044881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 2, 2].length) (baseStart_4044881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044881 prefixEnd_4044881 := by exact prefixLift 4044881
  have htrace : WordTrace (prefixWord ++ tailWord_4044881) baseStart_4044881 baseEnd_4044881 := by
    simpa [prefixWord, tailWord_4044881, baseEnd_4044881] using wordTrace_append hprefix tailTrace_4044881
  have hstable : (prefixWord ++ tailWord_4044881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044881).length < 2 ^ (prefixWord ++ tailWord_4044881).sum := by decide
  have hdescent : baseEnd_4044881 < baseStart_4044881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044887 : List Nat := [1, 1, 3, 2, 2, 1, 5, 8]
def baseStart_4044887 : Nat := 118140960795 + 4044887 * 2 ^ 59
def prefixEnd_4044887 : Nat := 4983230072969 + 3 ^ 40 * 4044887 * 2
def baseEnd_4044887 : Nat := 76924860152697077581867

theorem tailTrace_4044887 : CollatzResearch.WordTrace tailWord_4044887 prefixEnd_4044887 76924860152697077581867 := by
  unfold tailWord_4044887
  simp only [CollatzResearch.WordTrace]
  refine ⟨147529148897072685546380915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98352765931381790364253943 147529148897072685546380915)
  ·
    refine ⟨221293723345609028319571373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147529148897072685546380915 221293723345609028319571373)
    ·
      refine ⟨82985146254603385619839265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221293723345609028319571373 82985146254603385619839265)
      ·
        refine ⟨62238859690952539214879449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82985146254603385619839265 62238859690952539214879449)
        ·
          refine ⟨46679144768214404411159587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62238859690952539214879449 46679144768214404411159587)
          ·
            refine ⟨70018717152321606616739381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46679144768214404411159587 70018717152321606616739381)
            ·
              refine ⟨6564254733030150620319317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70018717152321606616739381 6564254733030150620319317)
              ·
                refine ⟨76924860152697077581867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6564254733030150620319317 76924860152697077581867)
                ·
                  rfl

theorem cell23_4044887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 8].length) (baseStart_4044887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044887 prefixEnd_4044887 := by exact prefixLift 4044887
  have htrace : WordTrace (prefixWord ++ tailWord_4044887) baseStart_4044887 baseEnd_4044887 := by
    simpa [prefixWord, tailWord_4044887, baseEnd_4044887] using wordTrace_append hprefix tailTrace_4044887
  have hstable : (prefixWord ++ tailWord_4044887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044887).length < 2 ^ (prefixWord ++ tailWord_4044887).sum := by decide
  have hdescent : baseEnd_4044887 < baseStart_4044887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044918 : List Nat := [5, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_4044918 : Nat := 118140960795 + 4044918 * 2 ^ 59
def prefixEnd_4044918 : Nat := 4983230072969 + 3 ^ 40 * 4044918 * 2
def baseEnd_4044918 : Nat := 2076987142023110473422767

theorem tailTrace_4044918 : CollatzResearch.WordTrace tailWord_4044918 prefixEnd_4044918 2076987142023110473422767 := by
  unfold tailWord_4044918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9220642472497523615047463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98353519706640251893839605 9220642472497523615047463)
  ·
    refine ⟨13830963708746285422571195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9220642472497523615047463 13830963708746285422571195)
    ·
      refine ⟨20746445563119428133856793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13830963708746285422571195 20746445563119428133856793)
      ·
        refine ⟨15559834172339571100392595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20746445563119428133856793 15559834172339571100392595)
        ·
          refine ⟨23339751258509356650588893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15559834172339571100392595 23339751258509356650588893)
          ·
            refine ⟨8752406721941008743970835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23339751258509356650588893 8752406721941008743970835)
            ·
              refine ⟨13128610082911513115956253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8752406721941008743970835 13128610082911513115956253)
              ·
                refine ⟨4923228781091817418483595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13128610082911513115956253 4923228781091817418483595)
                ·
                  refine ⟨7384843171637726127725393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4923228781091817418483595 7384843171637726127725393)
                  ·
                    refine ⟨5538632378728294595794045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7384843171637726127725393 5538632378728294595794045)
                    ·
                      refine ⟨2076987142023110473422767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5538632378728294595794045 2076987142023110473422767)
                      ·
                        rfl

theorem cell23_4044918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_4044918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044918 prefixEnd_4044918 := by exact prefixLift 4044918
  have htrace : WordTrace (prefixWord ++ tailWord_4044918) baseStart_4044918 baseEnd_4044918 := by
    simpa [prefixWord, tailWord_4044918, baseEnd_4044918] using wordTrace_append hprefix tailTrace_4044918
  have hstable : (prefixWord ++ tailWord_4044918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044918).length < 2 ^ (prefixWord ++ tailWord_4044918).sum := by decide
  have hdescent : baseEnd_4044918 < baseStart_4044918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044931 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 4, 1, 3]
def baseStart_4044931 : Nat := 118140960795 + 4044931 * 2 ^ 59
def prefixEnd_4044931 : Nat := 4983230072969 + 3 ^ 40 * 4044931 * 2
def baseEnd_4044931 : Nat := 2076993817271618922560207

theorem tailTrace_4044931 : CollatzResearch.WordTrace tailWord_4044931 prefixEnd_4044931 2076993817271618922560207 := by
  unfold tailWord_4044931
  simp only [CollatzResearch.WordTrace]
  refine ⟨147530753708913281060982647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98353835805942187373988431 147530753708913281060982647)
  ·
    refine ⟨221296130563369921591473971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147530753708913281060982647 221296130563369921591473971)
    ·
      refine ⟨331944195845054882387210957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221296130563369921591473971 331944195845054882387210957)
      ·
        refine ⟨124479073441895580895204109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331944195845054882387210957 124479073441895580895204109)
        ·
          refine ⟨46679652540710842835701541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124479073441895580895204109 46679652540710842835701541)
          ·
            refine ⟨8752434851383283031694039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46679652540710842835701541 8752434851383283031694039)
            ·
              refine ⟨13128652277074924547541059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8752434851383283031694039 13128652277074924547541059)
              ·
                refine ⟨19692978415612386821311589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13128652277074924547541059 19692978415612386821311589)
                ·
                  refine ⟨3692433452927322528995923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19692978415612386821311589 3692433452927322528995923)
                  ·
                    refine ⟨5538650179390983793493885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3692433452927322528995923 5538650179390983793493885)
                    ·
                      refine ⟨2076993817271618922560207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5538650179390983793493885 2076993817271618922560207)
                      ·
                        rfl

theorem cell23_4044931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_4044931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044931 prefixEnd_4044931 := by exact prefixLift 4044931
  have htrace : WordTrace (prefixWord ++ tailWord_4044931) baseStart_4044931 baseEnd_4044931 := by
    simpa [prefixWord, tailWord_4044931, baseEnd_4044931] using wordTrace_append hprefix tailTrace_4044931
  have hstable : (prefixWord ++ tailWord_4044931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044931).length < 2 ^ (prefixWord ++ tailWord_4044931).sum := by decide
  have hdescent : baseEnd_4044931 < baseStart_4044931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4044987 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 7]
def baseStart_4044987 : Nat := 118140960795 + 4044987 * 2 ^ 59
def prefixEnd_4044987 : Nat := 4983230072969 + 3 ^ 40 * 4044987 * 2
def baseEnd_4044987 : Nat := 2077022572188270703459949

theorem tailTrace_4044987 : CollatzResearch.WordTrace tailWord_4044987 prefixEnd_4044987 2077022572188270703459949 := by
  unfold tailWord_4044987
  simp only [CollatzResearch.WordTrace]
  refine ⟨147532796196710402625021215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98355197464473601750014143 147532796196710402625021215)
  ·
    refine ⟨221299194295065603937531823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147532796196710402625021215 221299194295065603937531823)
    ·
      refine ⟨331948791442598405906297735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221299194295065603937531823 331948791442598405906297735)
      ·
        refine ⟨497923187163897608859446603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331948791442598405906297735 497923187163897608859446603)
        ·
          refine ⟨746884780745846413289169905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497923187163897608859446603 746884780745846413289169905)
          ·
            refine ⟨560163585559384809966877429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 746884780745846413289169905 560163585559384809966877429)
            ·
              refine ⟨52515336146192325934394759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 560163585559384809966877429 52515336146192325934394759)
              ·
                refine ⟨78773004219288488901592139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52515336146192325934394759 78773004219288488901592139)
                ·
                  refine ⟨118159506328932733352388209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78773004219288488901592139 118159506328932733352388209)
                  ·
                    refine ⟨88619629746699550014291157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118159506328932733352388209 88619629746699550014291157)
                    ·
                      refine ⟨2077022572188270703459949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88619629746699550014291157 2077022572188270703459949)
                      ·
                        rfl

theorem cell23_4044987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_4044987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4044987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4044987 prefixEnd_4044987 := by exact prefixLift 4044987
  have htrace : WordTrace (prefixWord ++ tailWord_4044987) baseStart_4044987 baseEnd_4044987 := by
    simpa [prefixWord, tailWord_4044987, baseEnd_4044987] using wordTrace_append hprefix tailTrace_4044987
  have hstable : (prefixWord ++ tailWord_4044987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4044987).length < 2 ^ (prefixWord ++ tailWord_4044987).sum := by decide
  have hdescent : baseEnd_4044987 < baseStart_4044987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4044987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045026 : List Nat := [3, 3, 4, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4045026 : Nat := 118140960795 + 4045026 * 2 ^ 59
def prefixEnd_4045026 : Nat := 4983230072969 + 3 ^ 40 * 4045026 * 2
def baseEnd_4045026 : Nat := 2077042597933796050872271

theorem tailTrace_4045026 : CollatzResearch.WordTrace tailWord_4045026 prefixEnd_4045026 2077042597933796050872271 := by
  unfold tailWord_4045026
  simp only [CollatzResearch.WordTrace]
  refine ⟨36883554660892278071422733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98356145762379408190460621 36883554660892278071422733)
  ·
    refine ⟨13831332997834604276783525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36883554660892278071422733 13831332997834604276783525)
    ·
      refine ⟨2593374937093988301896911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13831332997834604276783525 2593374937093988301896911)
      ·
        refine ⟨3890062405640982452845367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2593374937093988301896911 3890062405640982452845367)
        ·
          refine ⟨5835093608461473679268051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3890062405640982452845367 5835093608461473679268051)
          ·
            refine ⟨8752640412692210518902077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5835093608461473679268051 8752640412692210518902077)
            ·
              refine ⟨3282240154759578944588279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8752640412692210518902077 3282240154759578944588279)
              ·
                refine ⟨4923360232139368416882419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3282240154759578944588279 4923360232139368416882419)
                ·
                  refine ⟨7385040348209052625323629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4923360232139368416882419 7385040348209052625323629)
                  ·
                    refine ⟨2769390130578394734496361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7385040348209052625323629 2769390130578394734496361)
                    ·
                      refine ⟨2077042597933796050872271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769390130578394734496361 2077042597933796050872271)
                      ·
                        rfl

theorem cell23_4045026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4045026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045026 prefixEnd_4045026 := by exact prefixLift 4045026
  have htrace : WordTrace (prefixWord ++ tailWord_4045026) baseStart_4045026 baseEnd_4045026 := by
    simpa [prefixWord, tailWord_4045026, baseEnd_4045026] using wordTrace_append hprefix tailTrace_4045026
  have hstable : (prefixWord ++ tailWord_4045026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045026).length < 2 ^ (prefixWord ++ tailWord_4045026).sum := by decide
  have hdescent : baseEnd_4045026 < baseStart_4045026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045034 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_4045034 : Nat := 118140960795 + 4045034 * 2 ^ 59
def prefixEnd_4045034 : Nat := 4983230072969 + 3 ^ 40 * 4045034 * 2
def baseEnd_4045034 : Nat := 2077046705779032019572233

theorem tailTrace_4045034 : CollatzResearch.WordTrace tailWord_4045034 prefixEnd_4045034 2077046705779032019572233 := by
  unfold tailWord_4045034
  simp only [CollatzResearch.WordTrace]
  refine ⟨36883627606885032412995539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98356340285026753101321437 36883627606885032412995539)
  ·
    refine ⟨55325441410327548619493309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36883627606885032412995539 55325441410327548619493309)
    ·
      refine ⟨20747040528872830732309991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55325441410327548619493309 20747040528872830732309991)
      ·
        refine ⟨31120560793309246098464987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20747040528872830732309991 31120560793309246098464987)
        ·
          refine ⟨46680841189963869147697481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31120560793309246098464987 46680841189963869147697481)
          ·
            refine ⟨35010630892472901860773111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46680841189963869147697481 35010630892472901860773111)
            ·
              refine ⟨52515946338709352791159667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35010630892472901860773111 52515946338709352791159667)
              ·
                refine ⟨78773919508064029186739501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52515946338709352791159667 78773919508064029186739501)
                ·
                  refine ⟨29540219815524010945027313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78773919508064029186739501 29540219815524010945027313)
                  ·
                    refine ⟨22155164861643008208770485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29540219815524010945027313 22155164861643008208770485)
                    ·
                      refine ⟨2077046705779032019572233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22155164861643008208770485 2077046705779032019572233)
                      ·
                        rfl

theorem cell23_4045034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_4045034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045034 prefixEnd_4045034 := by exact prefixLift 4045034
  have htrace : WordTrace (prefixWord ++ tailWord_4045034) baseStart_4045034 baseEnd_4045034 := by
    simpa [prefixWord, tailWord_4045034, baseEnd_4045034] using wordTrace_append hprefix tailTrace_4045034
  have hstable : (prefixWord ++ tailWord_4045034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045034).length < 2 ^ (prefixWord ++ tailWord_4045034).sum := by decide
  have hdescent : baseEnd_4045034 < baseStart_4045034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045084 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 8]
def baseStart_4045084 : Nat := 118140960795 + 4045084 * 2 ^ 59
def prefixEnd_4045084 : Nat := 4983230072969 + 3 ^ 40 * 4045084 * 2
def baseEnd_4045084 : Nat := 230785819979084091549667

theorem tailTrace_4045084 : CollatzResearch.WordTrace tailWord_4045084 prefixEnd_4045084 230785819979084091549667 := by
  unfold tailWord_4045084
  simp only [CollatzResearch.WordTrace]
  refine ⟨73768167038679494095651153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98357556051572658794201537 73768167038679494095651153)
  ·
    refine ⟨55326125279009620571738365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73768167038679494095651153 55326125279009620571738365)
    ·
      refine ⟨20747296979628607714401887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55326125279009620571738365 20747296979628607714401887)
      ·
        refine ⟨31120945469442911571602831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20747296979628607714401887 31120945469442911571602831)
        ·
          refine ⟨46681418204164367357404247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31120945469442911571602831 46681418204164367357404247)
          ·
            refine ⟨70022127306246551036106371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46681418204164367357404247 70022127306246551036106371)
            ·
              refine ⟨105033190959369826554159557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70022127306246551036106371 105033190959369826554159557)
              ·
                refine ⟨19693723304881842478904917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105033190959369826554159557 19693723304881842478904917)
                ·
                  refine ⟨230785819979084091549667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19693723304881842478904917 230785819979084091549667)
                  ·
                    rfl

theorem cell23_4045084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_4045084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045084 prefixEnd_4045084 := by exact prefixLift 4045084
  have htrace : WordTrace (prefixWord ++ tailWord_4045084) baseStart_4045084 baseEnd_4045084 := by
    simpa [prefixWord, tailWord_4045084, baseEnd_4045084] using wordTrace_append hprefix tailTrace_4045084
  have hstable : (prefixWord ++ tailWord_4045084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045084).length < 2 ^ (prefixWord ++ tailWord_4045084).sum := by decide
  have hdescent : baseEnd_4045084 < baseStart_4045084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045128 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_4045128 : Nat := 118140960795 + 4045128 * 2 ^ 59
def prefixEnd_4045128 : Nat := 4983230072969 + 3 ^ 40 * 4045128 * 2
def baseEnd_4045128 : Nat := 2077094972960554651796801

theorem tailTrace_4045128 : CollatzResearch.WordTrace tailWord_4045128 prefixEnd_4045128 2077094972960554651796801 := by
  unfold tailWord_4045128
  simp only [CollatzResearch.WordTrace]
  refine ⟨73768969444599791852952019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98358625926133055803936025 73768969444599791852952019)
  ·
    refine ⟨110653454166899687779428029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73768969444599791852952019 110653454166899687779428029)
    ·
      refine ⟨41495045312587382917285511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110653454166899687779428029 41495045312587382917285511)
      ·
        refine ⟨62242567968881074375928267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41495045312587382917285511 62242567968881074375928267)
        ·
          refine ⟨93363851953321611563892401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62242567968881074375928267 93363851953321611563892401)
          ·
            refine ⟨70022888964991208672919301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93363851953321611563892401 70022888964991208672919301)
            ·
              refine ⟨13129291680935851626172369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70022888964991208672919301 13129291680935851626172369)
              ·
                refine ⟨9846968760701888719629277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13129291680935851626172369 9846968760701888719629277)
                ·
                  refine ⟨3692613285263208269860979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9846968760701888719629277 3692613285263208269860979)
                  ·
                    refine ⟨5538919927894812404791469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3692613285263208269860979 5538919927894812404791469)
                    ·
                      refine ⟨2077094972960554651796801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5538919927894812404791469 2077094972960554651796801)
                      ·
                        rfl

theorem cell23_4045128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_4045128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045128 prefixEnd_4045128 := by exact prefixLift 4045128
  have htrace : WordTrace (prefixWord ++ tailWord_4045128) baseStart_4045128 baseEnd_4045128 := by
    simpa [prefixWord, tailWord_4045128, baseEnd_4045128] using wordTrace_append hprefix tailTrace_4045128
  have hstable : (prefixWord ++ tailWord_4045128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045128).length < 2 ^ (prefixWord ++ tailWord_4045128).sum := by decide
  have hdescent : baseEnd_4045128 < baseStart_4045128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045138 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_4045138 : Nat := 118140960795 + 4045138 * 2 ^ 59
def prefixEnd_4045138 : Nat := 4983230072969 + 3 ^ 40 * 4045138 * 2
def baseEnd_4045138 : Nat := 2077100107767099612671755

theorem tailTrace_4045138 : CollatzResearch.WordTrace tailWord_4045138 prefixEnd_4045138 2077100107767099612671755 := by
  unfold tailWord_4045138
  simp only [CollatzResearch.WordTrace]
  refine ⟨36884575904790838853442017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98358869079442236942512045 36884575904790838853442017)
  ·
    refine ⟨27663431928593129140081513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36884575904790838853442017 27663431928593129140081513)
    ·
      refine ⟨20747573946444846855061135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27663431928593129140081513 20747573946444846855061135)
      ·
        refine ⟨31121360919667270282591703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20747573946444846855061135 31121360919667270282591703)
        ·
          refine ⟨46682041379500905423887555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31121360919667270282591703 46682041379500905423887555)
          ·
            refine ⟨70023062069251358135831333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46682041379500905423887555 70023062069251358135831333)
            ·
              refine ⟨13129324137984629650468375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70023062069251358135831333 13129324137984629650468375)
              ·
                refine ⟨19693986206976944475702563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13129324137984629650468375 19693986206976944475702563)
                ·
                  refine ⟨29540979310465416713553845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19693986206976944475702563 29540979310465416713553845)
                  ·
                    refine ⟨2769466810356132816895673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29540979310465416713553845 2769466810356132816895673)
                    ·
                      refine ⟨2077100107767099612671755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769466810356132816895673 2077100107767099612671755)
                      ·
                        rfl

theorem cell23_4045138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_4045138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045138 prefixEnd_4045138 := by exact prefixLift 4045138
  have htrace : WordTrace (prefixWord ++ tailWord_4045138) baseStart_4045138 baseEnd_4045138 := by
    simpa [prefixWord, tailWord_4045138, baseEnd_4045138] using wordTrace_append hprefix tailTrace_4045138
  have hstable : (prefixWord ++ tailWord_4045138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045138).length < 2 ^ (prefixWord ++ tailWord_4045138).sum := by decide
  have hdescent : baseEnd_4045138 < baseStart_4045138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045161 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 4, 4]
def baseStart_4045161 : Nat := 118140960795 + 4045161 * 2 ^ 59
def prefixEnd_4045161 : Nat := 4983230072969 + 3 ^ 40 * 4045161 * 2
def baseEnd_4045161 : Nat := 692370639274051007561383

theorem tailTrace_4045161 : CollatzResearch.WordTrace tailWord_4045161 prefixEnd_4045161 692370639274051007561383 := by
  unfold tailWord_4045161
  simp only [CollatzResearch.WordTrace]
  refine ⟨147539142498080030341855337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98359428332053353561236891 147539142498080030341855337)
  ·
    refine ⟨110654356873560022756391503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147539142498080030341855337 110654356873560022756391503)
    ·
      refine ⟨165981535310340034134587255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110654356873560022756391503 165981535310340034134587255)
      ·
        refine ⟨248972302965510051201880883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165981535310340034134587255 248972302965510051201880883)
        ·
          refine ⟨373458454448265076802821325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248972302965510051201880883 373458454448265076802821325)
          ·
            refine ⟨140046920418099403801057997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373458454448265076802821325 140046920418099403801057997)
            ·
              refine ⟨52517595156787276425396749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140046920418099403801057997 52517595156787276425396749)
              ·
                refine ⟨19694098183795228659523781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52517595156787276425396749 19694098183795228659523781)
                ·
                  refine ⟨3692643409461605373660709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19694098183795228659523781 3692643409461605373660709)
                  ·
                    refine ⟨692370639274051007561383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3692643409461605373660709 692370639274051007561383)
                    ·
                      rfl

theorem cell23_4045161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 4].length) (baseStart_4045161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045161 prefixEnd_4045161 := by exact prefixLift 4045161
  have htrace : WordTrace (prefixWord ++ tailWord_4045161) baseStart_4045161 baseEnd_4045161 := by
    simpa [prefixWord, tailWord_4045161, baseEnd_4045161] using wordTrace_append hprefix tailTrace_4045161
  have hstable : (prefixWord ++ tailWord_4045161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045161).length < 2 ^ (prefixWord ++ tailWord_4045161).sum := by decide
  have hdescent : baseEnd_4045161 < baseStart_4045161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045162 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_4045162 : Nat := 118140960795 + 4045162 * 2 ^ 59
def prefixEnd_4045162 : Nat := 4983230072969 + 3 ^ 40 * 4045162 * 2
def baseEnd_4045162 : Nat := 2077112431302807518771645

theorem tailTrace_4045162 : CollatzResearch.WordTrace tailWord_4045162 prefixEnd_4045162 2077112431302807518771645 := by
  unfold tailWord_4045162
  simp only [CollatzResearch.WordTrace]
  refine ⟨36884794742769101878160435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98359452647384271675094493 36884794742769101878160435)
  ·
    refine ⟨55327192114153652817240653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36884794742769101878160435 55327192114153652817240653)
    ·
      refine ⟨20747697042807619806465245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55327192114153652817240653 20747697042807619806465245)
      ·
        refine ⟨7780386391052857427424467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20747697042807619806465245 7780386391052857427424467)
        ·
          refine ⟨11670579586579286141136701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7780386391052857427424467 11670579586579286141136701)
          ·
            refine ⟨4376467344967232302926263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11670579586579286141136701 4376467344967232302926263)
            ·
              refine ⟨6564701017450848454389395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4376467344967232302926263 6564701017450848454389395)
              ·
                refine ⟨9847051526176272681584093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6564701017450848454389395 9847051526176272681584093)
                ·
                  refine ⟨3692644322316102255594035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9847051526176272681584093 3692644322316102255594035)
                  ·
                    refine ⟨5538966483474153383391053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3692644322316102255594035 5538966483474153383391053)
                    ·
                      refine ⟨2077112431302807518771645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5538966483474153383391053 2077112431302807518771645)
                      ·
                        rfl

theorem cell23_4045162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_4045162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045162 prefixEnd_4045162 := by exact prefixLift 4045162
  have htrace : WordTrace (prefixWord ++ tailWord_4045162) baseStart_4045162 baseEnd_4045162 := by
    simpa [prefixWord, tailWord_4045162, baseEnd_4045162] using wordTrace_append hprefix tailTrace_4045162
  have hstable : (prefixWord ++ tailWord_4045162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045162).length < 2 ^ (prefixWord ++ tailWord_4045162).sum := by decide
  have hdescent : baseEnd_4045162 < baseStart_4045162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045171 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 3]
def baseStart_4045171 : Nat := 118140960795 + 4045171 * 2 ^ 59
def prefixEnd_4045171 : Nat := 4983230072969 + 3 ^ 40 * 4045171 * 2
def baseEnd_4045171 : Nat := 2077117052628697983559103

theorem tailTrace_4045171 : CollatzResearch.WordTrace tailWord_4045171 prefixEnd_4045171 2077117052628697983559103 := by
  unfold tailWord_4045171
  simp only [CollatzResearch.WordTrace]
  refine ⟨147539507228043802049719367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98359671485362534699812911 147539507228043802049719367)
  ·
    refine ⟨221309260842065703074579051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147539507228043802049719367 221309260842065703074579051)
    ·
      refine ⟨331963891263098554611868577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221309260842065703074579051 331963891263098554611868577)
      ·
        refine ⟨248972918447323915958901433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331963891263098554611868577 248972918447323915958901433)
        ·
          refine ⟨186729688835492936969176075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248972918447323915958901433 186729688835492936969176075)
          ·
            refine ⟨280094533253239405453764113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186729688835492936969176075 280094533253239405453764113)
            ·
              refine ⟨210070899939929554090323085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280094533253239405453764113 210070899939929554090323085)
              ·
                refine ⟨78776587477473582783871157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210070899939929554090323085 78776587477473582783871157)
                ·
                  refine ⟨7385305076013148385987921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78776587477473582783871157 7385305076013148385987921)
                  ·
                    refine ⟨5538978807009861289490941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7385305076013148385987921 5538978807009861289490941)
                    ·
                      refine ⟨2077117052628697983559103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5538978807009861289490941 2077117052628697983559103)
                      ·
                        rfl

theorem cell23_4045171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 3].length) (baseStart_4045171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045171 prefixEnd_4045171 := by exact prefixLift 4045171
  have htrace : WordTrace (prefixWord ++ tailWord_4045171) baseStart_4045171 baseEnd_4045171 := by
    simpa [prefixWord, tailWord_4045171, baseEnd_4045171] using wordTrace_append hprefix tailTrace_4045171
  have hstable : (prefixWord ++ tailWord_4045171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045171).length < 2 ^ (prefixWord ++ tailWord_4045171).sum := by decide
  have hdescent : baseEnd_4045171 < baseStart_4045171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045181 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_4045181 : Nat := 118140960795 + 4045181 * 2 ^ 59
def prefixEnd_4045181 : Nat := 4983230072969 + 3 ^ 40 * 4045181 * 2
def baseEnd_4045181 : Nat := 2077122187435242944434057

theorem tailTrace_4045181 : CollatzResearch.WordTrace tailWord_4045181 prefixEnd_4045181 2077122187435242944434057 := by
  unfold tailWord_4045181
  simp only [CollatzResearch.WordTrace]
  refine ⟨147539871958007573757583397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98359914638671715838388931 147539871958007573757583397)
  ·
    refine ⟨27663725992126420079546887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147539871958007573757583397 27663725992126420079546887)
    ·
      refine ⟨41495588988189630119320331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27663725992126420079546887 41495588988189630119320331)
      ·
        refine ⟨62243383482284445178980497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41495588988189630119320331 62243383482284445178980497)
        ·
          refine ⟨46682537611713333884235373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62243383482284445178980497 46682537611713333884235373)
          ·
            refine ⟨17505951604392500206588265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46682537611713333884235373 17505951604392500206588265)
            ·
              refine ⟨13129463703294375154941199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17505951604392500206588265 13129463703294375154941199)
              ·
                refine ⟨19694195554941562732411799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13129463703294375154941199 19694195554941562732411799)
                ·
                  refine ⟨29541293332412344098617699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19694195554941562732411799 29541293332412344098617699)
                  ·
                    refine ⟨44311939998618516147926549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29541293332412344098617699 44311939998618516147926549)
                    ·
                      refine ⟨2077122187435242944434057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44311939998618516147926549 2077122187435242944434057)
                      ·
                        rfl

theorem cell23_4045181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_4045181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045181 prefixEnd_4045181 := by exact prefixLift 4045181
  have htrace : WordTrace (prefixWord ++ tailWord_4045181) baseStart_4045181 baseEnd_4045181 := by
    simpa [prefixWord, tailWord_4045181, baseEnd_4045181] using wordTrace_append hprefix tailTrace_4045181
  have hstable : (prefixWord ++ tailWord_4045181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045181).length < 2 ^ (prefixWord ++ tailWord_4045181).sum := by decide
  have hdescent : baseEnd_4045181 < baseStart_4045181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045185 : List Nat := [1, 2, 4, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_4045185 : Nat := 118140960795 + 4045185 * 2 ^ 59
def prefixEnd_4045185 : Nat := 4983230072969 + 3 ^ 40 * 4045185 * 2
def baseEnd_4045185 : Nat := 2077124241357860928784039

theorem tailTrace_4045185 : CollatzResearch.WordTrace tailWord_4045185 prefixEnd_4045185 2077124241357860928784039 := by
  unfold tailWord_4045185
  simp only [CollatzResearch.WordTrace]
  refine ⟨147540017849993082440729009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98360011899995388293819339 147540017849993082440729009)
  ·
    refine ⟨110655013387494811830546757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147540017849993082440729009 110655013387494811830546757)
    ·
      refine ⟨20747815010155277218227517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110655013387494811830546757 20747815010155277218227517)
      ·
        refine ⟨7780430628808228956835319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20747815010155277218227517 7780430628808228956835319)
        ·
          refine ⟨11670645943212343435252979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7780430628808228956835319 11670645943212343435252979)
          ·
            refine ⟨17505968914818515152879469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11670645943212343435252979 17505968914818515152879469)
            ·
              refine ⟨6564738343056943182329801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17505968914818515152879469 6564738343056943182329801)
              ·
                refine ⟨4923553757292707386747351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6564738343056943182329801 4923553757292707386747351)
                ·
                  refine ⟨7385330635939061080121027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4923553757292707386747351 7385330635939061080121027)
                  ·
                    refine ⟨11077995953908591620181541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7385330635939061080121027 11077995953908591620181541)
                    ·
                      refine ⟨2077124241357860928784039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11077995953908591620181541 2077124241357860928784039)
                      ·
                        rfl

theorem cell23_4045185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_4045185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045185 prefixEnd_4045185 := by exact prefixLift 4045185
  have htrace : WordTrace (prefixWord ++ tailWord_4045185) baseStart_4045185 baseEnd_4045185 := by
    simpa [prefixWord, tailWord_4045185, baseEnd_4045185] using wordTrace_append hprefix tailTrace_4045185
  have hstable : (prefixWord ++ tailWord_4045185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045185).length < 2 ^ (prefixWord ++ tailWord_4045185).sum := by decide
  have hdescent : baseEnd_4045185 < baseStart_4045185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045188 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_4045188 : Nat := 118140960795 + 4045188 * 2 ^ 59
def prefixEnd_4045188 : Nat := 4983230072969 + 3 ^ 40 * 4045188 * 2
def baseEnd_4045188 : Nat := 2077125781799824417046525

theorem tailTrace_4045188 : CollatzResearch.WordTrace tailWord_4045188 prefixEnd_4045188 2077125781799824417046525 := by
  unfold tailWord_4045188
  simp only [CollatzResearch.WordTrace]
  refine ⟨73770063634491106976544109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98360084845988142635392145 73770063634491106976544109)
  ·
    refine ⟨27663773862934165116204041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73770063634491106976544109 27663773862934165116204041)
    ·
      refine ⟨20747830397200623837153031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27663773862934165116204041 20747830397200623837153031)
      ·
        refine ⟨31121745595800935755729547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20747830397200623837153031 31121745595800935755729547)
        ·
          refine ⟨46682618393701403633594321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31121745595800935755729547 46682618393701403633594321)
          ·
            refine ⟨35011963795276052725195741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46682618393701403633594321 35011963795276052725195741)
            ·
              refine ⟨13129486423228519771948403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35011963795276052725195741 13129486423228519771948403)
              ·
                refine ⟨19694229634842779657922605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13129486423228519771948403 19694229634842779657922605)
                ·
                  refine ⟨7385336113066042371720977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19694229634842779657922605 7385336113066042371720977)
                  ·
                    refine ⟨5539002084799531778790733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7385336113066042371720977 5539002084799531778790733)
                    ·
                      refine ⟨2077125781799824417046525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5539002084799531778790733 2077125781799824417046525)
                      ·
                        rfl

theorem cell23_4045188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_4045188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045188 prefixEnd_4045188 := by exact prefixLift 4045188
  have htrace : WordTrace (prefixWord ++ tailWord_4045188) baseStart_4045188 baseEnd_4045188 := by
    simpa [prefixWord, tailWord_4045188, baseEnd_4045188] using wordTrace_append hprefix tailTrace_4045188
  have hstable : (prefixWord ++ tailWord_4045188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045188).length < 2 ^ (prefixWord ++ tailWord_4045188).sum := by decide
  have hdescent : baseEnd_4045188 < baseStart_4045188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045198 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4045198 : Nat := 118140960795 + 4045198 * 2 ^ 59
def prefixEnd_4045198 : Nat := 4983230072969 + 3 ^ 40 * 4045198 * 2
def baseEnd_4045198 : Nat := 2077130916606369377921479

theorem tailTrace_4045198 : CollatzResearch.WordTrace tailWord_4045198 prefixEnd_4045198 2077130916606369377921479 := by
  unfold tailWord_4045198
  simp only [CollatzResearch.WordTrace]
  refine ⟨18442561499868248207619031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98360327999297323773968165 18442561499868248207619031)
  ·
    refine ⟨27663842249802372311428547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18442561499868248207619031 27663842249802372311428547)
    ·
      refine ⟨41495763374703558467142821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27663842249802372311428547 41495763374703558467142821)
      ·
        refine ⟨7780455632756917212589279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41495763374703558467142821 7780455632756917212589279)
        ·
          refine ⟨11670683449135375818883919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7780455632756917212589279 11670683449135375818883919)
          ·
            refine ⟨17506025173703063728325879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11670683449135375818883919 17506025173703063728325879)
            ·
              refine ⟨26259037760554595592488819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17506025173703063728325879 26259037760554595592488819)
              ·
                refine ⟨39388556640831893388733229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26259037760554595592488819 39388556640831893388733229)
                ·
                  refine ⟨14770708740311960020774961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39388556640831893388733229 14770708740311960020774961)
                  ·
                    refine ⟨11078031555233970015581221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14770708740311960020774961 11078031555233970015581221)
                    ·
                      refine ⟨2077130916606369377921479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11078031555233970015581221 2077130916606369377921479)
                      ·
                        rfl

theorem cell23_4045198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4045198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045198 prefixEnd_4045198 := by exact prefixLift 4045198
  have htrace : WordTrace (prefixWord ++ tailWord_4045198) baseStart_4045198 baseEnd_4045198 := by
    simpa [prefixWord, tailWord_4045198, baseEnd_4045198] using wordTrace_append hprefix tailTrace_4045198
  have hstable : (prefixWord ++ tailWord_4045198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045198).length < 2 ^ (prefixWord ++ tailWord_4045198).sum := by decide
  have hdescent : baseEnd_4045198 < baseStart_4045198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045218 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_4045218 : Nat := 118140960795 + 4045218 * 2 ^ 59
def prefixEnd_4045218 : Nat := 4983230072969 + 3 ^ 40 * 4045218 * 2
def baseEnd_4045218 : Nat := 2077141186219459299671387

theorem tailTrace_4045218 : CollatzResearch.WordTrace tailWord_4045218 prefixEnd_4045218 2077141186219459299671387 := by
  unfold tailWord_4045218
  simp only [CollatzResearch.WordTrace]
  refine ⟨36885305364718382269170077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98360814305915686051120205 36885305364718382269170077)
  ·
    refine ⟨13831989511769393350938779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36885305364718382269170077 13831989511769393350938779)
    ·
      refine ⟨20747984267654090026408169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13831989511769393350938779 20747984267654090026408169)
      ·
        refine ⟨15560988200740567519806127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20747984267654090026408169 15560988200740567519806127)
        ·
          refine ⟨23341482301110851279709191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15560988200740567519806127 23341482301110851279709191)
          ·
            refine ⟨35012223451666276919563787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23341482301110851279709191 35012223451666276919563787)
            ·
              refine ⟨52518335177499415379345681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35012223451666276919563787 52518335177499415379345681)
              ·
                refine ⟨39388751383124561534509261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52518335177499415379345681 39388751383124561534509261)
                ·
                  refine ⟨14770781768671710575440973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39388751383124561534509261 14770781768671710575440973)
                  ·
                    refine ⟨5539043163251891465790365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14770781768671710575440973 5539043163251891465790365)
                    ·
                      refine ⟨2077141186219459299671387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5539043163251891465790365 2077141186219459299671387)
                      ·
                        rfl

theorem cell23_4045218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_4045218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045218 prefixEnd_4045218 := by exact prefixLift 4045218
  have htrace : WordTrace (prefixWord ++ tailWord_4045218) baseStart_4045218 baseEnd_4045218 := by
    simpa [prefixWord, tailWord_4045218, baseEnd_4045218] using wordTrace_append hprefix tailTrace_4045218
  have hstable : (prefixWord ++ tailWord_4045218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045218).length < 2 ^ (prefixWord ++ tailWord_4045218).sum := by decide
  have hdescent : baseEnd_4045218 < baseStart_4045218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045219 : List Nat := [1, 1, 1, 4, 1, 4, 4, 2, 1, 2, 2]
def baseStart_4045219 : Nat := 118140960795 + 4045219 * 2 ^ 59
def prefixEnd_4045219 : Nat := 4983230072969 + 3 ^ 40 * 4045219 * 2
def baseEnd_4045219 : Nat := 2077141699700113795758883

theorem tailTrace_4045219 : CollatzResearch.WordTrace tailWord_4045219 prefixEnd_4045219 2077141699700113795758883 := by
  unfold tailWord_4045219
  simp only [CollatzResearch.WordTrace]
  refine ⟨147541257931869906247466711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98360838621246604164977807 147541257931869906247466711)
  ·
    refine ⟨221311886897804859371200067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147541257931869906247466711 221311886897804859371200067)
    ·
      refine ⟨331967830346707289056800101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221311886897804859371200067 331967830346707289056800101)
      ·
        refine ⟨62243968190007616698150019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331967830346707289056800101 62243968190007616698150019)
        ·
          refine ⟨93365952285011425047225029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62243968190007616698150019 93365952285011425047225029)
          ·
            refine ⟨17506116053439642196354693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93365952285011425047225029 17506116053439642196354693)
            ·
              refine ⟨3282396760019932911816505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17506116053439642196354693 3282396760019932911816505)
              ·
                refine ⟨2461797570014949683862379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3282396760019932911816505 2461797570014949683862379)
                ·
                  refine ⟨3692696355022424525793569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461797570014949683862379 3692696355022424525793569)
                  ·
                    refine ⟨2769522266266818394345177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3692696355022424525793569 2769522266266818394345177)
                    ·
                      refine ⟨2077141699700113795758883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769522266266818394345177 2077141699700113795758883)
                      ·
                        rfl

theorem cell23_4045219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_4045219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045219 prefixEnd_4045219 := by exact prefixLift 4045219
  have htrace : WordTrace (prefixWord ++ tailWord_4045219) baseStart_4045219 baseEnd_4045219 := by
    simpa [prefixWord, tailWord_4045219, baseEnd_4045219] using wordTrace_append hprefix tailTrace_4045219
  have hstable : (prefixWord ++ tailWord_4045219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045219).length < 2 ^ (prefixWord ++ tailWord_4045219).sum := by decide
  have hdescent : baseEnd_4045219 < baseStart_4045219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045236 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_4045236 : Nat := 118140960795 + 4045236 * 2 ^ 59
def prefixEnd_4045236 : Nat := 4983230072969 + 3 ^ 40 * 4045236 * 2
def baseEnd_4045236 : Nat := 2077150428871240229246305

theorem tailTrace_4045236 : CollatzResearch.WordTrace tailWord_4045236 prefixEnd_4045236 2077150428871240229246305 := by
  unfold tailWord_4045236
  simp only [CollatzResearch.WordTrace]
  refine ⟨73770938986404159075417781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98361251981872212100557041 73770938986404159075417781)
  ·
    refine ⟨6916025529975389913320417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73770938986404159075417781 6916025529975389913320417)
    ·
      refine ⟨5187019147481542434990313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6916025529975389913320417 5187019147481542434990313)
      ·
        refine ⟨3890264360611156826242735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5187019147481542434990313 3890264360611156826242735)
        ·
          refine ⟨5835396540916735239364103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3890264360611156826242735 5835396540916735239364103)
          ·
            refine ⟨8753094811375102859046155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5835396540916735239364103 8753094811375102859046155)
            ·
              refine ⟨13129642217062654288569233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8753094811375102859046155 13129642217062654288569233)
              ·
                refine ⟨9847231662796990716426925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13129642217062654288569233 9847231662796990716426925)
                ·
                  refine ⟨3692711873548871518660097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9847231662796990716426925 3692711873548871518660097)
                  ·
                    refine ⟨2769533905161653638995073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3692711873548871518660097 2769533905161653638995073)
                    ·
                      refine ⟨2077150428871240229246305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769533905161653638995073 2077150428871240229246305)
                      ·
                        rfl

theorem cell23_4045236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_4045236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045236 prefixEnd_4045236 := by exact prefixLift 4045236
  have htrace : WordTrace (prefixWord ++ tailWord_4045236) baseStart_4045236 baseEnd_4045236 := by
    simpa [prefixWord, tailWord_4045236, baseEnd_4045236] using wordTrace_append hprefix tailTrace_4045236
  have hstable : (prefixWord ++ tailWord_4045236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045236).length < 2 ^ (prefixWord ++ tailWord_4045236).sum := by decide
  have hdescent : baseEnd_4045236 < baseStart_4045236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045245 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 3, 3, 2]
def baseStart_4045245 : Nat := 118140960795 + 4045245 * 2 ^ 59
def prefixEnd_4045245 : Nat := 4983230072969 + 3 ^ 40 * 4045245 * 2
def baseEnd_4045245 : Nat := 2077155050197130694033763

theorem tailTrace_4045245 : CollatzResearch.WordTrace tailWord_4045245 prefixEnd_4045245 2077155050197130694033763 := by
  unfold tailWord_4045245
  simp only [CollatzResearch.WordTrace]
  refine ⟨147542206229775712687913189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98361470819850475125275459 147542206229775712687913189)
  ·
    refine ⟨27664163668082946128983723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147542206229775712687913189 27664163668082946128983723)
    ·
      refine ⟨41496245502124419193475585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27664163668082946128983723 41496245502124419193475585)
      ·
        refine ⟨31122184126593314395106689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41496245502124419193475585 31122184126593314395106689)
        ·
          refine ⟨23341638094944985796330017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31122184126593314395106689 23341638094944985796330017)
          ·
            refine ⟨17506228571208739347247513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23341638094944985796330017 17506228571208739347247513)
            ·
              refine ⟨13129671428406554510435635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17506228571208739347247513 13129671428406554510435635)
              ·
                refine ⟨19694507142609831765653453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13129671428406554510435635 19694507142609831765653453)
                ·
                  refine ⟨7385440178478686912120045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19694507142609831765653453 7385440178478686912120045)
                  ·
                    refine ⟨2769540066929507592045017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7385440178478686912120045 2769540066929507592045017)
                    ·
                      refine ⟨2077155050197130694033763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769540066929507592045017 2077155050197130694033763)
                      ·
                        rfl

theorem cell23_4045245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_4045245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045245 prefixEnd_4045245 := by exact prefixLift 4045245
  have htrace : WordTrace (prefixWord ++ tailWord_4045245) baseStart_4045245 baseEnd_4045245 := by
    simpa [prefixWord, tailWord_4045245, baseEnd_4045245] using wordTrace_append hprefix tailTrace_4045245
  have hstable : (prefixWord ++ tailWord_4045245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045245).length < 2 ^ (prefixWord ++ tailWord_4045245).sum := by decide
  have hdescent : baseEnd_4045245 < baseStart_4045245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045268 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_4045268 : Nat := 118140960795 + 4045268 * 2 ^ 59
def prefixEnd_4045268 : Nat := 4983230072969 + 3 ^ 40 * 4045268 * 2
def baseEnd_4045268 : Nat := 692388953417394701348719

theorem tailTrace_4045268 : CollatzResearch.WordTrace tailWord_4045268 prefixEnd_4045268 692388953417394701348719 := by
  unfold tailWord_4045268
  simp only [CollatzResearch.WordTrace]
  refine ⟨73771522554346193808000229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98362030072461591744000305 73771522554346193808000229)
  ·
    refine ⟨13832160478939911339000043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73771522554346193808000229 13832160478939911339000043)
    ·
      refine ⟨20748240718409867008500065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13832160478939911339000043 20748240718409867008500065)
      ·
        refine ⟨15561180538807400256375049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20748240718409867008500065 15561180538807400256375049)
        ·
          refine ⟨11670885404105550192281287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15561180538807400256375049 11670885404105550192281287)
          ·
            refine ⟨17506328106158325288421931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11670885404105550192281287 17506328106158325288421931)
            ·
              refine ⟨26259492159237487932632897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17506328106158325288421931 26259492159237487932632897)
              ·
                refine ⟨19694619119428115949474673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26259492159237487932632897 19694619119428115949474673)
                ·
                  refine ⟨14770964339571086962106005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19694619119428115949474673 14770964339571086962106005)
                  ·
                    refine ⟨692388953417394701348719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14770964339571086962106005 692388953417394701348719)
                    ·
                      rfl

theorem cell23_4045268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_4045268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045268 prefixEnd_4045268 := by exact prefixLift 4045268
  have htrace : WordTrace (prefixWord ++ tailWord_4045268) baseStart_4045268 baseEnd_4045268 := by
    simpa [prefixWord, tailWord_4045268, baseEnd_4045268] using wordTrace_append hprefix tailTrace_4045268
  have hstable : (prefixWord ++ tailWord_4045268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045268).length < 2 ^ (prefixWord ++ tailWord_4045268).sum := by decide
  have hdescent : baseEnd_4045268 < baseStart_4045268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045288 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_4045288 : Nat := 118140960795 + 4045288 * 2 ^ 59
def prefixEnd_4045288 : Nat := 4983230072969 + 3 ^ 40 * 4045288 * 2
def baseEnd_4045288 : Nat := 2077177129865274025796065

theorem tailTrace_4045288 : CollatzResearch.WordTrace tailWord_4045288 prefixEnd_4045288 2077177129865274025796065 := by
  unfold tailWord_4045288
  simp only [CollatzResearch.WordTrace]
  refine ⟨73771887284309965515864259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98362516379079954021152345 73771887284309965515864259)
  ·
    refine ⟨110657830926464948273796389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73771887284309965515864259 110657830926464948273796389)
    ·
      refine ⟨20748343298712177801336823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110657830926464948273796389 20748343298712177801336823)
      ·
        refine ⟨31122514948068266702005235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20748343298712177801336823 31122514948068266702005235)
        ·
          refine ⟨46683772422102400053007853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31122514948068266702005235 46683772422102400053007853)
          ·
            refine ⟨17506414658288400019877945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46683772422102400053007853 17506414658288400019877945)
            ·
              refine ⟨13129810993716300014908459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17506414658288400019877945 13129810993716300014908459)
              ·
                refine ⟨19694716490574450022362689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13129810993716300014908459 19694716490574450022362689)
                ·
                  refine ⟨14771037367930837516772017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19694716490574450022362689 14771037367930837516772017)
                  ·
                    refine ⟨11078278025948128137579013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14771037367930837516772017 11078278025948128137579013)
                    ·
                      refine ⟨2077177129865274025796065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11078278025948128137579013 2077177129865274025796065)
                      ·
                        rfl

theorem cell23_4045288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_4045288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045288 prefixEnd_4045288 := by exact prefixLift 4045288
  have htrace : WordTrace (prefixWord ++ tailWord_4045288) baseStart_4045288 baseEnd_4045288 := by
    simpa [prefixWord, tailWord_4045288, baseEnd_4045288] using wordTrace_append hprefix tailTrace_4045288
  have hstable : (prefixWord ++ tailWord_4045288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045288).length < 2 ^ (prefixWord ++ tailWord_4045288).sum := by decide
  have hdescent : baseEnd_4045288 < baseStart_4045288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045311 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 1, 7]
def baseStart_4045311 : Nat := 118140960795 + 4045311 * 2 ^ 59
def prefixEnd_4045311 : Nat := 4983230072969 + 3 ^ 40 * 4045311 * 2
def baseEnd_4045311 : Nat := 692396313306775811936153

theorem tailTrace_4045311 : CollatzResearch.WordTrace tailWord_4045311 prefixEnd_4045311 692396313306775811936153 := by
  unfold tailWord_4045311
  simp only [CollatzResearch.WordTrace]
  refine ⟨147544613447536605959815787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98363075631691070639877191 147544613447536605959815787)
  ·
    refine ⟨221316920171304908939723681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147544613447536605959815787 221316920171304908939723681)
    ·
      refine ⟨165987690128478681704792761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221316920171304908939723681 165987690128478681704792761)
      ·
        refine ⟨124490767596359011278594571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165987690128478681704792761 124490767596359011278594571)
        ·
          refine ⟨186736151394538516917891857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124490767596359011278594571 186736151394538516917891857)
          ·
            refine ⟨140052113545903887688418893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186736151394538516917891857 140052113545903887688418893)
            ·
              refine ⟨52519542579713957883157085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140052113545903887688418893 52519542579713957883157085)
              ·
                refine ⟨19694828467392734206183907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52519542579713957883157085 19694828467392734206183907)
                ·
                  refine ⟨29542242701089101309275861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19694828467392734206183907 29542242701089101309275861)
                  ·
                    refine ⟨692396313306775811936153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29542242701089101309275861 692396313306775811936153)
                    ·
                      rfl

theorem cell23_4045311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_4045311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045311 prefixEnd_4045311 := by exact prefixLift 4045311
  have htrace : WordTrace (prefixWord ++ tailWord_4045311) baseStart_4045311 baseEnd_4045311 := by
    simpa [prefixWord, tailWord_4045311, baseEnd_4045311] using wordTrace_append hprefix tailTrace_4045311
  have hstable : (prefixWord ++ tailWord_4045311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045311).length < 2 ^ (prefixWord ++ tailWord_4045311).sum := by decide
  have hdescent : baseEnd_4045311 < baseStart_4045311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045332 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 7]
def baseStart_4045332 : Nat := 118140960795 + 4045332 * 2 ^ 59
def prefixEnd_4045332 : Nat := 4983230072969 + 3 ^ 40 * 4045332 * 2
def baseEnd_4045332 : Nat := 230799969223785761516207

theorem tailTrace_4045332 : CollatzResearch.WordTrace tailWord_4045332 prefixEnd_4045332 230799969223785761516207 := by
  unfold tailWord_4045332
  simp only [CollatzResearch.WordTrace]
  refine ⟨73772689690230263273165125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98363586253640351030886833 73772689690230263273165125)
  ·
    refine ⟨13832379316918174363718461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73772689690230263273165125 13832379316918174363718461)
    ·
      refine ⟨5187142243844315386394423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13832379316918174363718461 5187142243844315386394423)
      ·
        refine ⟨7780713365766473079591635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5187142243844315386394423 7780713365766473079591635)
        ·
          refine ⟨11671070048649709619387453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7780713365766473079591635 11671070048649709619387453)
          ·
            refine ⟨4376651268243641107270295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11671070048649709619387453 4376651268243641107270295)
            ·
              refine ⟨6564976902365461660905443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4376651268243641107270295 6564976902365461660905443)
              ·
                refine ⟨9847465353548192491358165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6564976902365461660905443 9847465353548192491358165)
                ·
                  refine ⟨230799969223785761516207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9847465353548192491358165 230799969223785761516207)
                  ·
                    rfl

theorem cell23_4045332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_4045332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045332 prefixEnd_4045332 := by exact prefixLift 4045332
  have htrace : WordTrace (prefixWord ++ tailWord_4045332) baseStart_4045332 baseEnd_4045332 := by
    simpa [prefixWord, tailWord_4045332, baseEnd_4045332] using wordTrace_append hprefix tailTrace_4045332
  have hstable : (prefixWord ++ tailWord_4045332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045332).length < 2 ^ (prefixWord ++ tailWord_4045332).sum := by decide
  have hdescent : baseEnd_4045332 < baseStart_4045332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045365 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_4045365 : Nat := 118140960795 + 4045365 * 2 ^ 59
def prefixEnd_4045365 : Nat := 4983230072969 + 3 ^ 40 * 4045365 * 2
def baseEnd_4045365 : Nat := 2077216667875670224533211

theorem tailTrace_4045365 : CollatzResearch.WordTrace tailWord_4045365 prefixEnd_4045365 2077216667875670224533211 := by
  unfold tailWord_4045365
  simp only [CollatzResearch.WordTrace]
  refine ⟨147546582989340973182281549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98364388659560648788187699 147546582989340973182281549)
  ·
    refine ⟨55329968621002864943355581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147546582989340973182281549 55329968621002864943355581)
    ·
      refine ⟨20748738232876074353758343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55329968621002864943355581 20748738232876074353758343)
      ·
        refine ⟨31123107349314111530637515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20748738232876074353758343 31123107349314111530637515)
        ·
          refine ⟨46684661023971167295956273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31123107349314111530637515 46684661023971167295956273)
          ·
            refine ⟨35013495767978375471967205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46684661023971167295956273 35013495767978375471967205)
            ·
              refine ⟨6565030456495945400993851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35013495767978375471967205 6565030456495945400993851)
              ·
                refine ⟨9847545684743918101490777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6565030456495945400993851 9847545684743918101490777)
                ·
                  refine ⟨7385659263557938576118083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9847545684743918101490777 7385659263557938576118083)
                  ·
                    refine ⟨11078488895336907864177125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7385659263557938576118083 11078488895336907864177125)
                    ·
                      refine ⟨2077216667875670224533211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11078488895336907864177125 2077216667875670224533211)
                      ·
                        rfl

theorem cell23_4045365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_4045365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045365 prefixEnd_4045365 := by exact prefixLift 4045365
  have htrace : WordTrace (prefixWord ++ tailWord_4045365) baseStart_4045365 baseEnd_4045365 := by
    simpa [prefixWord, tailWord_4045365, baseEnd_4045365] using wordTrace_append hprefix tailTrace_4045365
  have hstable : (prefixWord ++ tailWord_4045365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045365).length < 2 ^ (prefixWord ++ tailWord_4045365).sum := by decide
  have hdescent : baseEnd_4045365 < baseStart_4045365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045495 : List Nat := [1, 1, 3, 1, 6, 2, 9]
def baseStart_4045495 : Nat := 118140960795 + 4045495 * 2 ^ 59
def prefixEnd_4045495 : Nat := 4983230072969 + 3 ^ 40 * 4045495 * 2
def baseEnd_4045495 : Nat := 25645474325441416245773

theorem tailTrace_4045495 : CollatzResearch.WordTrace tailWord_4045495 prefixEnd_4045495 25645474325441416245773 := by
  unfold tailWord_4045495
  simp only [CollatzResearch.WordTrace]
  refine ⟨147551324478870005384513939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98367549652580003589675959 147551324478870005384513939)
  ·
    refine ⟨221326986718305008076770909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147551324478870005384513939 221326986718305008076770909)
    ·
      refine ⟨82997620019364378028789091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221326986718305008076770909 82997620019364378028789091)
      ·
        refine ⟨124496430029046567043183637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82997620019364378028789091 124496430029046567043183637)
        ·
          refine ⟨5835770157611557830149233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124496430029046567043183637 5835770157611557830149233)
          ·
            refine ⟨4376827618208668372611925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5835770157611557830149233 4376827618208668372611925)
            ·
              refine ⟨25645474325441416245773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4376827618208668372611925 25645474325441416245773)
              ·
                rfl

theorem cell23_4045495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 9].length) (baseStart_4045495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045495 prefixEnd_4045495 := by exact prefixLift 4045495
  have htrace : WordTrace (prefixWord ++ tailWord_4045495) baseStart_4045495 baseEnd_4045495 := by
    simpa [prefixWord, tailWord_4045495, baseEnd_4045495] using wordTrace_append hprefix tailTrace_4045495
  have hstable : (prefixWord ++ tailWord_4045495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045495).length < 2 ^ (prefixWord ++ tailWord_4045495).sum := by decide
  have hdescent : baseEnd_4045495 < baseStart_4045495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045515 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 1, 9, 2]
def baseStart_4045515 : Nat := 118140960795 + 4045515 * 2 ^ 59
def prefixEnd_4045515 : Nat := 4983230072969 + 3 ^ 40 * 4045515 * 2
def baseEnd_4045515 : Nat := 2077293689973844637657521

theorem tailTrace_4045515 : CollatzResearch.WordTrace tailWord_4045515 prefixEnd_4045515 2077293689973844637657521 := by
  unfold tailWord_4045515
  simp only [CollatzResearch.WordTrace]
  refine ⟨147552053938797548800241999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98368035959198365866827999 147552053938797548800241999)
  ·
    refine ⟨221328080908196323200362999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147552053938797548800241999 221328080908196323200362999)
    ·
      refine ⟨331992121362294484800544499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221328080908196323200362999 331992121362294484800544499)
      ·
        refine ⟨497988182043441727200816749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331992121362294484800544499 497988182043441727200816749)
        ·
          refine ⟨186745568266290647700306281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497988182043441727200816749 186745568266290647700306281)
          ·
            refine ⟨140059176199717985775229711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186745568266290647700306281 140059176199717985775229711)
            ·
              refine ⟨210088764299576978662844567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140059176199717985775229711 210088764299576978662844567)
              ·
                refine ⟨315133146449365467994266851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210088764299576978662844567 315133146449365467994266851)
                ·
                  refine ⟨472699719674048201991400277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315133146449365467994266851 472699719674048201991400277)
                  ·
                    refine ⟨2769724919965126183543361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 472699719674048201991400277 2769724919965126183543361)
                    ·
                      refine ⟨2077293689973844637657521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769724919965126183543361 2077293689973844637657521)
                      ·
                        rfl

theorem cell23_4045515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 9, 2].length) (baseStart_4045515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045515 prefixEnd_4045515 := by exact prefixLift 4045515
  have htrace : WordTrace (prefixWord ++ tailWord_4045515) baseStart_4045515 baseEnd_4045515 := by
    simpa [prefixWord, tailWord_4045515, baseEnd_4045515] using wordTrace_append hprefix tailTrace_4045515
  have hstable : (prefixWord ++ tailWord_4045515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045515).length < 2 ^ (prefixWord ++ tailWord_4045515).sum := by decide
  have hdescent : baseEnd_4045515 < baseStart_4045515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045516 : List Nat := [2, 2, 1, 5, 1, 3, 2, 1, 2, 4]
def baseStart_4045516 : Nat := 118140960795 + 4045516 * 2 ^ 59
def prefixEnd_4045516 : Nat := 4983230072969 + 3 ^ 40 * 4045516 * 2
def baseEnd_4045516 : Nat := 692431401151499711248339

theorem tailTrace_4045516 : CollatzResearch.WordTrace tailWord_4045516 prefixEnd_4045516 692431401151499711248339 := by
  unfold tailWord_4045516
  simp only [CollatzResearch.WordTrace]
  refine ⟨73776045205896962985514201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98368060274529283980685601 73776045205896962985514201)
  ·
    refine ⟨55332033904422722239135651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73776045205896962985514201 55332033904422722239135651)
    ·
      refine ⟨82998050856634083358703477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55332033904422722239135651 82998050856634083358703477)
      ·
        refine ⟨7781067267809445314878451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82998050856634083358703477 7781067267809445314878451)
        ·
          refine ⟨11671600901714167972317677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781067267809445314878451 11671600901714167972317677)
          ·
            refine ⟨4376850338142812989619129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11671600901714167972317677 4376850338142812989619129)
            ·
              refine ⟨3282637753607109742214347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4376850338142812989619129 3282637753607109742214347)
              ·
                refine ⟨4923956630410664613321521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3282637753607109742214347 4923956630410664613321521)
                ·
                  refine ⟨3692967472807998459991141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4923956630410664613321521 3692967472807998459991141)
                  ·
                    refine ⟨692431401151499711248339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3692967472807998459991141 692431401151499711248339)
                    ·
                      rfl

theorem cell23_4045516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_4045516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045516 prefixEnd_4045516 := by exact prefixLift 4045516
  have htrace : WordTrace (prefixWord ++ tailWord_4045516) baseStart_4045516 baseEnd_4045516 := by
    simpa [prefixWord, tailWord_4045516, baseEnd_4045516] using wordTrace_append hprefix tailTrace_4045516
  have hstable : (prefixWord ++ tailWord_4045516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045516).length < 2 ^ (prefixWord ++ tailWord_4045516).sum := by decide
  have hdescent : baseEnd_4045516 < baseStart_4045516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045557 : List Nat := [1, 3, 6, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_4045557 : Nat := 118140960795 + 4045557 * 2 ^ 59
def prefixEnd_4045557 : Nat := 4983230072969 + 3 ^ 40 * 4045557 * 2
def baseEnd_4045557 : Nat := 2077315256161333473332329

theorem tailTrace_4045557 : CollatzResearch.WordTrace tailWord_4045557 prefixEnd_4045557 2077315256161333473332329 := by
  unfold tailWord_4045557
  simp only [CollatzResearch.WordTrace]
  refine ⟨147553585804645389973270925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98369057203096926648847283 147553585804645389973270925)
  ·
    refine ⟨55332594676742021239976597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147553585804645389973270925 55332594676742021239976597)
    ·
      refine ⟨2593715375472282245623903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55332594676742021239976597 2593715375472282245623903)
      ·
        refine ⟨3890573063208423368435855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2593715375472282245623903 3890573063208423368435855)
        ·
          refine ⟨5835859594812635052653783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3890573063208423368435855 5835859594812635052653783)
          ·
            refine ⟨8753789392218952578980675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5835859594812635052653783 8753789392218952578980675)
            ·
              refine ⟨13130684088328428868471013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8753789392218952578980675 13130684088328428868471013)
              ·
                refine ⟨2462003266561580412838315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13130684088328428868471013 2462003266561580412838315)
                ·
                  refine ⟨3693004899842370619257473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462003266561580412838315 3693004899842370619257473)
                  ·
                    refine ⟨2769753674881777964443105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3693004899842370619257473 2769753674881777964443105)
                    ·
                      refine ⟨2077315256161333473332329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769753674881777964443105 2077315256161333473332329)
                      ·
                        rfl

theorem cell23_4045557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_4045557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045557 prefixEnd_4045557 := by exact prefixLift 4045557
  have htrace : WordTrace (prefixWord ++ tailWord_4045557) baseStart_4045557 baseEnd_4045557 := by
    simpa [prefixWord, tailWord_4045557, baseEnd_4045557] using wordTrace_append hprefix tailTrace_4045557
  have hstable : (prefixWord ++ tailWord_4045557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045557).length < 2 ^ (prefixWord ++ tailWord_4045557).sum := by decide
  have hdescent : baseEnd_4045557 < baseStart_4045557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045565 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_4045565 : Nat := 118140960795 + 4045565 * 2 ^ 59
def prefixEnd_4045565 : Nat := 4983230072969 + 3 ^ 40 * 4045565 * 2
def baseEnd_4045565 : Nat := 2077319364006569442032291

theorem tailTrace_4045565 : CollatzResearch.WordTrace tailWord_4045565 prefixEnd_4045565 2077319364006569442032291 := by
  unfold tailWord_4045565
  simp only [CollatzResearch.WordTrace]
  refine ⟨147553877588616407339562149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98369251725744271559708099 147553877588616407339562149)
  ·
    refine ⟨27666352047865576376167903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147553877588616407339562149 27666352047865576376167903)
    ·
      refine ⟨41499528071798364564251855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27666352047865576376167903 41499528071798364564251855)
      ·
        refine ⟨62249292107697546846377783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41499528071798364564251855 62249292107697546846377783)
        ·
          refine ⟨93373938161546320269566675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62249292107697546846377783 93373938161546320269566675)
          ·
            refine ⟨140060907242319480404350013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93373938161546320269566675 140060907242319480404350013)
            ·
              refine ⟨52522840215869805151631255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140060907242319480404350013 52522840215869805151631255)
              ·
                refine ⟨78784260323804707727446883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52522840215869805151631255 78784260323804707727446883)
                ·
                  refine ⟨118176390485707061591170325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78784260323804707727446883 118176390485707061591170325)
                  ·
                    refine ⟨5539518304017518512086109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118176390485707061591170325 5539518304017518512086109)
                    ·
                      refine ⟨2077319364006569442032291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5539518304017518512086109 2077319364006569442032291)
                      ·
                        rfl

theorem cell23_4045565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_4045565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045565 prefixEnd_4045565 := by exact prefixLift 4045565
  have htrace : WordTrace (prefixWord ++ tailWord_4045565) baseStart_4045565 baseEnd_4045565 := by
    simpa [prefixWord, tailWord_4045565, baseEnd_4045565] using wordTrace_append hprefix tailTrace_4045565
  have hstable : (prefixWord ++ tailWord_4045565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045565).length < 2 ^ (prefixWord ++ tailWord_4045565).sum := by decide
  have hdescent : baseEnd_4045565 < baseStart_4045565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045595 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 3]
def baseStart_4045595 : Nat := 118140960795 + 4045595 * 2 ^ 59
def prefixEnd_4045595 : Nat := 4983230072969 + 3 ^ 40 * 4045595 * 2
def baseEnd_4045595 : Nat := 2077334768426204324657153

theorem tailTrace_4045595 : CollatzResearch.WordTrace tailWord_4045595 prefixEnd_4045595 2077334768426204324657153 := by
  unfold tailWord_4045595
  simp only [CollatzResearch.WordTrace]
  refine ⟨147554971778507722463154239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98369981185671814975436159 147554971778507722463154239)
  ·
    refine ⟨221332457667761583694731359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147554971778507722463154239 221332457667761583694731359)
    ·
      refine ⟨331998686501642375542097039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221332457667761583694731359 331998686501642375542097039)
      ·
        refine ⟨497998029752463563313145559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331998686501642375542097039 497998029752463563313145559)
        ·
          refine ⟨746997044628695344969718339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497998029752463563313145559 746997044628695344969718339)
          ·
            refine ⟨1120495566943043017454577509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746997044628695344969718339 1120495566943043017454577509)
            ·
              refine ⟨210092918801820565772733283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1120495566943043017454577509 210092918801820565772733283)
              ·
                refine ⟨315139378202730848659099925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210092918801820565772733283 315139378202730848659099925)
                ·
                  refine ⟨14772158353253008530895309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 315139378202730848659099925 14772158353253008530895309)
                  ·
                    refine ⟨5539559382469878199085741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14772158353253008530895309 5539559382469878199085741)
                    ·
                      refine ⟨2077334768426204324657153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5539559382469878199085741 2077334768426204324657153)
                      ·
                        rfl

theorem cell23_4045595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 3].length) (baseStart_4045595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045595 prefixEnd_4045595 := by exact prefixLift 4045595
  have htrace : WordTrace (prefixWord ++ tailWord_4045595) baseStart_4045595 baseEnd_4045595 := by
    simpa [prefixWord, tailWord_4045595, baseEnd_4045595] using wordTrace_append hprefix tailTrace_4045595
  have hstable : (prefixWord ++ tailWord_4045595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045595).length < 2 ^ (prefixWord ++ tailWord_4045595).sum := by decide
  have hdescent : baseEnd_4045595 < baseStart_4045595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045630 : List Nat := [4, 2, 1, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_4045630 : Nat := 118140960795 + 4045630 * 2 ^ 59
def prefixEnd_4045630 : Nat := 4983230072969 + 3 ^ 40 * 4045630 * 2
def baseEnd_4045630 : Nat := 2077352740249111687719493

theorem tailTrace_4045630 : CollatzResearch.WordTrace tailWord_4045630 prefixEnd_4045630 2077352740249111687719493 := by
  unfold tailWord_4045630
  simp only [CollatzResearch.WordTrace]
  refine ⟨18444531041672615430084793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98370832222253948960452229 18444531041672615430084793)
  ·
    refine ⟨13833398281254461572563595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18444531041672615430084793 13833398281254461572563595)
    ·
      refine ⟨20750097421881692358845393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13833398281254461572563595 20750097421881692358845393)
      ·
        refine ⟨15562573066411269269134045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20750097421881692358845393 15562573066411269269134045)
        ·
          refine ⟨5835964899904225975925267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15562573066411269269134045 5835964899904225975925267)
          ·
            refine ⟨8753947349856338963887901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5835964899904225975925267 8753947349856338963887901)
            ·
              refine ⟨3282730256196127111457963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8753947349856338963887901 3282730256196127111457963)
              ·
                refine ⟨4924095384294190667186945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3282730256196127111457963 4924095384294190667186945)
                ·
                  refine ⟨3693071538220643000390209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4924095384294190667186945 3693071538220643000390209)
                  ·
                    refine ⟨2769803653665482250292657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3693071538220643000390209 2769803653665482250292657)
                    ·
                      refine ⟨2077352740249111687719493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2769803653665482250292657 2077352740249111687719493)
                      ·
                        rfl

theorem cell23_4045630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_4045630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045630 prefixEnd_4045630 := by exact prefixLift 4045630
  have htrace : WordTrace (prefixWord ++ tailWord_4045630) baseStart_4045630 baseEnd_4045630 := by
    simpa [prefixWord, tailWord_4045630, baseEnd_4045630] using wordTrace_append hprefix tailTrace_4045630
  have hstable : (prefixWord ++ tailWord_4045630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045630).length < 2 ^ (prefixWord ++ tailWord_4045630).sum := by decide
  have hdescent : baseEnd_4045630 < baseStart_4045630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045635 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 4]
def baseStart_4045635 : Nat := 118140960795 + 4045635 * 2 ^ 59
def prefixEnd_4045635 : Nat := 4983230072969 + 3 ^ 40 * 4045635 * 2
def baseEnd_4045635 : Nat := 2077355307652384168156969

theorem tailTrace_4045635 : CollatzResearch.WordTrace tailWord_4045635 prefixEnd_4045635 2077355307652384168156969 := by
  unfold tailWord_4045635
  simp only [CollatzResearch.WordTrace]
  refine ⟨147556430698362809294610359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98370953798908539529740239 147556430698362809294610359)
  ·
    refine ⟨221334646047544213941915539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147556430698362809294610359 221334646047544213941915539)
    ·
      refine ⟨332001969071316320912873309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221334646047544213941915539 332001969071316320912873309)
      ·
        refine ⟨124500738401743620342327491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332001969071316320912873309 124500738401743620342327491)
        ·
          refine ⟨186751107602615430513491237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124500738401743620342327491 186751107602615430513491237)
          ·
            refine ⟨35015832675490393221279607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186751107602615430513491237 35015832675490393221279607)
            ·
              refine ⟨52523749013235589831919411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35015832675490393221279607 52523749013235589831919411)
              ·
                refine ⟨78785623519853384747879117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52523749013235589831919411 78785623519853384747879117)
                ·
                  refine ⟨29544608819945019280454669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78785623519853384747879117 29544608819945019280454669)
                  ·
                    refine ⟨11079228307479382230170501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29544608819945019280454669 11079228307479382230170501)
                    ·
                      refine ⟨2077355307652384168156969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11079228307479382230170501 2077355307652384168156969)
                      ·
                        rfl

theorem cell23_4045635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_4045635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045635 prefixEnd_4045635 := by exact prefixLift 4045635
  have htrace : WordTrace (prefixWord ++ tailWord_4045635) baseStart_4045635 baseEnd_4045635 := by
    simpa [prefixWord, tailWord_4045635, baseEnd_4045635] using wordTrace_append hprefix tailTrace_4045635
  have hstable : (prefixWord ++ tailWord_4045635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045635).length < 2 ^ (prefixWord ++ tailWord_4045635).sum := by decide
  have hdescent : baseEnd_4045635 < baseStart_4045635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045665 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_4045665 : Nat := 118140960795 + 4045665 * 2 ^ 59
def prefixEnd_4045665 : Nat := 4983230072969 + 3 ^ 40 * 4045665 * 2
def baseEnd_4045665 : Nat := 2077370712072019050781831

theorem tailTrace_4045665 : CollatzResearch.WordTrace tailWord_4045665 prefixEnd_4045665 2077370712072019050781831 := by
  unfold tailWord_4045665
  simp only [CollatzResearch.WordTrace]
  refine ⟨147557524888254124418202449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98371683258836082945468299 147557524888254124418202449)
  ·
    refine ⟨110668143666190593313651837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147557524888254124418202449 110668143666190593313651837)
    ·
      refine ⟨41500553874821472492619439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110668143666190593313651837 41500553874821472492619439)
      ·
        refine ⟨62250830812232208738929159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41500553874821472492619439 62250830812232208738929159)
        ·
          refine ⟨93376246218348313108393739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62250830812232208738929159 93376246218348313108393739)
          ·
            refine ⟨140064369327522469662590609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93376246218348313108393739 140064369327522469662590609)
            ·
              refine ⟨105048276995641852246942957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140064369327522469662590609 105048276995641852246942957)
              ·
                refine ⟨39393103873365694592603609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105048276995641852246942957 39393103873365694592603609)
                ·
                  refine ⟨29544827905024270944452707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39393103873365694592603609 29544827905024270944452707)
                  ·
                    refine ⟨44317241857536406416679061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29544827905024270944452707 44317241857536406416679061)
                    ·
                      refine ⟨2077370712072019050781831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44317241857536406416679061 2077370712072019050781831)
                      ·
                        rfl

theorem cell23_4045665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_4045665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045665 prefixEnd_4045665 := by exact prefixLift 4045665
  have htrace : WordTrace (prefixWord ++ tailWord_4045665) baseStart_4045665 baseEnd_4045665 := by
    simpa [prefixWord, tailWord_4045665, baseEnd_4045665] using wordTrace_append hprefix tailTrace_4045665
  have hstable : (prefixWord ++ tailWord_4045665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045665).length < 2 ^ (prefixWord ++ tailWord_4045665).sum := by decide
  have hdescent : baseEnd_4045665 < baseStart_4045665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045675 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 8]
def baseStart_4045675 : Nat := 118140960795 + 4045675 * 2 ^ 59
def prefixEnd_4045675 : Nat := 4983230072969 + 3 ^ 40 * 4045675 * 2
def baseEnd_4045675 : Nat := 230819538542062667961865

theorem tailTrace_4045675 : CollatzResearch.WordTrace tailWord_4045675 prefixEnd_4045675 230819538542062667961865 := by
  unfold tailWord_4045675
  simp only [CollatzResearch.WordTrace]
  refine ⟨147557889618217896126066479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98371926412145264084044319 147557889618217896126066479)
  ·
    refine ⟨221336834427326844189099719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147557889618217896126066479 221336834427326844189099719)
    ·
      refine ⟨332005251640990266283649579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221336834427326844189099719 332005251640990266283649579)
      ·
        refine ⟨498007877461485399425474369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332005251640990266283649579 498007877461485399425474369)
        ·
          refine ⟨373505908096114049569105777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498007877461485399425474369 373505908096114049569105777)
          ·
            refine ⟨280129431072085537176829333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373505908096114049569105777 280129431072085537176829333)
            ·
              refine ⟨13131067081504009555163875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 280129431072085537176829333 13131067081504009555163875)
              ·
                refine ⟨19696600622256014332745813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13131067081504009555163875 19696600622256014332745813)
                ·
                  refine ⟨230819538542062667961865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19696600622256014332745813 230819538542062667961865)
                  ·
                    rfl

theorem cell23_4045675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 8].length) (baseStart_4045675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045675 prefixEnd_4045675 := by exact prefixLift 4045675
  have htrace : WordTrace (prefixWord ++ tailWord_4045675) baseStart_4045675 baseEnd_4045675 := by
    simpa [prefixWord, tailWord_4045675, baseEnd_4045675] using wordTrace_append hprefix tailTrace_4045675
  have hstable : (prefixWord ++ tailWord_4045675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045675).length < 2 ^ (prefixWord ++ tailWord_4045675).sum := by decide
  have hdescent : baseEnd_4045675 < baseStart_4045675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045679 : List Nat := [1, 1, 2, 1, 3, 1, 1, 8, 1, 4]
def baseStart_4045679 : Nat := 118140960795 + 4045679 * 2 ^ 59
def prefixEnd_4045679 : Nat := 4983230072969 + 3 ^ 40 * 4045679 * 2
def baseEnd_4045679 : Nat := 692459300267060665335589

theorem tailTrace_4045679 : CollatzResearch.WordTrace tailWord_4045679 prefixEnd_4045679 692459300267060665335589 := by
  unfold tailWord_4045679
  simp only [CollatzResearch.WordTrace]
  refine ⟨147558035510203404809212091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98372023673468936539474727 147558035510203404809212091)
  ·
    refine ⟨221337053265305107213818137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147558035510203404809212091 221337053265305107213818137)
    ·
      refine ⟨166002789948978830410363603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221337053265305107213818137 166002789948978830410363603)
      ·
        refine ⟨249004184923468245615545405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166002789948978830410363603 249004184923468245615545405)
        ·
          refine ⟨93376569346300592105829527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249004184923468245615545405 93376569346300592105829527)
          ·
            refine ⟨140064854019450888158744291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93376569346300592105829527 140064854019450888158744291)
            ·
              refine ⟨210097281029176332238116437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140064854019450888158744291 210097281029176332238116437)
              ·
                refine ⟨2462077512060660143415427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 210097281029176332238116437 2462077512060660143415427)
                ·
                  refine ⟨3693116268090990215123141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462077512060660143415427 3693116268090990215123141)
                  ·
                    refine ⟨692459300267060665335589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3693116268090990215123141 692459300267060665335589)
                    ·
                      rfl

theorem cell23_4045679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 1, 4].length) (baseStart_4045679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045679 prefixEnd_4045679 := by exact prefixLift 4045679
  have htrace : WordTrace (prefixWord ++ tailWord_4045679) baseStart_4045679 baseEnd_4045679 := by
    simpa [prefixWord, tailWord_4045679, baseEnd_4045679] using wordTrace_append hprefix tailTrace_4045679
  have hstable : (prefixWord ++ tailWord_4045679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045679).length < 2 ^ (prefixWord ++ tailWord_4045679).sum := by decide
  have hdescent : baseEnd_4045679 < baseStart_4045679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045695 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 6]
def baseStart_4045695 : Nat := 118140960795 + 4045695 * 2 ^ 59
def prefixEnd_4045695 : Nat := 4983230072969 + 3 ^ 40 * 4045695 * 2
def baseEnd_4045695 : Nat := 2077386116491653933406693

theorem tailTrace_4045695 : CollatzResearch.WordTrace tailWord_4045695 prefixEnd_4045695 2077386116491653933406693 := by
  unfold tailWord_4045695
  simp only [CollatzResearch.WordTrace]
  refine ⟨147558619078145439541794539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98372412718763626361196359 147558619078145439541794539)
  ·
    refine ⟨221337928617218159312691809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147558619078145439541794539 221337928617218159312691809)
    ·
      refine ⟨166003446462913619484518857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221337928617218159312691809 166003446462913619484518857)
      ·
        refine ⟨124502584847185214613389143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166003446462913619484518857 124502584847185214613389143)
        ·
          refine ⟨186753877270777821920083715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124502584847185214613389143 186753877270777821920083715)
          ·
            refine ⟨280130815906166732880125573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186753877270777821920083715 280130815906166732880125573)
            ·
              refine ⟨52524527982406262415023545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280130815906166732880125573 52524527982406262415023545)
              ·
                refine ⟨39393395986804696811267659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52524527982406262415023545 39393395986804696811267659)
                ·
                  refine ⟨59090093980207045216901489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39393395986804696811267659 59090093980207045216901489)
                  ·
                    refine ⟨44317570485155283912676117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59090093980207045216901489 44317570485155283912676117)
                    ·
                      refine ⟨2077386116491653933406693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44317570485155283912676117 2077386116491653933406693)
                      ·
                        rfl

theorem cell23_4045695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_4045695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045695 prefixEnd_4045695 := by exact prefixLift 4045695
  have htrace : WordTrace (prefixWord ++ tailWord_4045695) baseStart_4045695 baseEnd_4045695 := by
    simpa [prefixWord, tailWord_4045695, baseEnd_4045695] using wordTrace_append hprefix tailTrace_4045695
  have hstable : (prefixWord ++ tailWord_4045695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045695).length < 2 ^ (prefixWord ++ tailWord_4045695).sum := by decide
  have hdescent : baseEnd_4045695 < baseStart_4045695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045706 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_4045706 : Nat := 118140960795 + 4045706 * 2 ^ 59
def prefixEnd_4045706 : Nat := 4983230072969 + 3 ^ 40 * 4045706 * 2
def baseEnd_4045706 : Nat := 2077391764778853390369143

theorem tailTrace_4045706 : CollatzResearch.WordTrace tailWord_4045706 prefixEnd_4045706 2077391764778853390369143 := by
  unfold tailWord_4045706
  simp only [CollatzResearch.WordTrace]
  refine ⟨36889755070276397105111243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98372680187403725613629981 36889755070276397105111243)
  ·
    refine ⟨55334632605414595657666865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36889755070276397105111243 55334632605414595657666865)
    ·
      refine ⟨41500974454060946743250149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55334632605414595657666865 41500974454060946743250149)
      ·
        refine ⟨7781432710136427514359403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41500974454060946743250149 7781432710136427514359403)
        ·
          refine ⟨11672149065204641271539105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781432710136427514359403 11672149065204641271539105)
          ·
            refine ⟨8754111798903480953654329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11672149065204641271539105 8754111798903480953654329)
            ·
              refine ⟨6565583849177610715240747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8754111798903480953654329 6565583849177610715240747)
              ·
                refine ⟨9848375773766416072861121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6565583849177610715240747 9848375773766416072861121)
                ·
                  refine ⟨7386281830324812054645841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9848375773766416072861121 7386281830324812054645841)
                  ·
                    refine ⟨5539711372743609040984381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7386281830324812054645841 5539711372743609040984381)
                    ·
                      refine ⟨2077391764778853390369143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5539711372743609040984381 2077391764778853390369143)
                      ·
                        rfl

theorem cell23_4045706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_4045706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045706 prefixEnd_4045706 := by exact prefixLift 4045706
  have htrace : WordTrace (prefixWord ++ tailWord_4045706) baseStart_4045706 baseEnd_4045706 := by
    simpa [prefixWord, tailWord_4045706, baseEnd_4045706] using wordTrace_append hprefix tailTrace_4045706
  have hstable : (prefixWord ++ tailWord_4045706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045706).length < 2 ^ (prefixWord ++ tailWord_4045706).sum := by decide
  have hdescent : baseEnd_4045706 < baseStart_4045706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045715 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 5]
def baseStart_4045715 : Nat := 118140960795 + 4045715 * 2 ^ 59
def prefixEnd_4045715 : Nat := 4983230072969 + 3 ^ 40 * 4045715 * 2
def baseEnd_4045715 : Nat := 2077396386104743855156601

theorem tailTrace_4045715 : CollatzResearch.WordTrace tailWord_4045715 prefixEnd_4045715 2077396386104743855156601 := by
  unfold tailWord_4045715
  simp only [CollatzResearch.WordTrace]
  refine ⟨147559348538072982957522599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98372899025381988638348399 147559348538072982957522599)
  ·
    refine ⟨221339022807109474436283899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147559348538072982957522599 221339022807109474436283899)
    ·
      refine ⟨332008534210664211654425849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221339022807109474436283899 332008534210664211654425849)
      ·
        refine ⟨249006400657998158740819387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332008534210664211654425849 249006400657998158740819387)
        ·
          refine ⟨373509600986997238111229081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249006400657998158740819387 373509600986997238111229081)
          ·
            refine ⟨280132200740247928583421811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373509600986997238111229081 280132200740247928583421811)
            ·
              refine ⟨420198301110371892875132717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280132200740247928583421811 420198301110371892875132717)
              ·
                refine ⟨157574362916389459828174769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420198301110371892875132717 157574362916389459828174769)
                ·
                  refine ⟨118180772187292094871131077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157574362916389459828174769 118180772187292094871131077)
                  ·
                    refine ⟨22158894785117267788337077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118180772187292094871131077 22158894785117267788337077)
                    ·
                      refine ⟨2077396386104743855156601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22158894785117267788337077 2077396386104743855156601)
                      ·
                        rfl

theorem cell23_4045715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_4045715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045715 prefixEnd_4045715 := by exact prefixLift 4045715
  have htrace : WordTrace (prefixWord ++ tailWord_4045715) baseStart_4045715 baseEnd_4045715 := by
    simpa [prefixWord, tailWord_4045715, baseEnd_4045715] using wordTrace_append hprefix tailTrace_4045715
  have hstable : (prefixWord ++ tailWord_4045715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045715).length < 2 ^ (prefixWord ++ tailWord_4045715).sum := by decide
  have hdescent : baseEnd_4045715 < baseStart_4045715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045730 : List Nat := [3, 3, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_4045730 : Nat := 118140960795 + 4045730 * 2 ^ 59
def prefixEnd_4045730 : Nat := 4983230072969 + 3 ^ 40 * 4045730 * 2
def baseEnd_4045730 : Nat := 692468029438187098823011

theorem tailTrace_4045730 : CollatzResearch.WordTrace tailWord_4045730 prefixEnd_4045730 692468029438187098823011 := by
  unfold tailWord_4045730
  simp only [CollatzResearch.WordTrace]
  refine ⟨36889973908254660129829661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98373263755345760346212429 36889973908254660129829661)
  ·
    refine ⟨13833740215595497548686123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36889973908254660129829661 13833740215595497548686123)
    ·
      refine ⟨20750610323393246323029185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13833740215595497548686123 20750610323393246323029185)
      ·
        refine ⟨15562957742544934742271889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20750610323393246323029185 15562957742544934742271889)
        ·
          refine ⟨11672218306908701056703917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15562957742544934742271889 11672218306908701056703917)
          ·
            refine ⟨4377081865090762896263969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11672218306908701056703917 4377081865090762896263969)
            ·
              refine ⟨3282811398818072172197977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4377081865090762896263969 3282811398818072172197977)
              ·
                refine ⟨2462108549113554129148483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3282811398818072172197977 2462108549113554129148483)
                ·
                  refine ⟨3693162823670331193722725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462108549113554129148483 3693162823670331193722725)
                  ·
                    refine ⟨692468029438187098823011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3693162823670331193722725 692468029438187098823011)
                    ·
                      rfl

theorem cell23_4045730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_4045730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045730 prefixEnd_4045730 := by exact prefixLift 4045730
  have htrace : WordTrace (prefixWord ++ tailWord_4045730) baseStart_4045730 baseEnd_4045730 := by
    simpa [prefixWord, tailWord_4045730, baseEnd_4045730] using wordTrace_append hprefix tailTrace_4045730
  have hstable : (prefixWord ++ tailWord_4045730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045730).length < 2 ^ (prefixWord ++ tailWord_4045730).sum := by decide
  have hdescent : baseEnd_4045730 < baseStart_4045730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045752 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 1, 6]
def baseStart_4045752 : Nat := 118140960795 + 4045752 * 2 ^ 59
def prefixEnd_4045752 : Nat := 4983230072969 + 3 ^ 40 * 4045752 * 2
def baseEnd_4045752 : Nat := 692471794962986736797977

theorem tailTrace_4045752 : CollatzResearch.WordTrace tailWord_4045752 prefixEnd_4045752 692471794962986736797977 := by
  unfold tailWord_4045752
  simp only [CollatzResearch.WordTrace]
  refine ⟨73780349019469469138309755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98373798692625958851079673 73780349019469469138309755)
  ·
    refine ⟨110670523529204203707464633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73780349019469469138309755 110670523529204203707464633)
    ·
      refine ⟨83002892646903152780598475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110670523529204203707464633 83002892646903152780598475)
      ·
        refine ⟨124504338970354729170897713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83002892646903152780598475 124504338970354729170897713)
        ·
          refine ⟨93378254227766046878173285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124504338970354729170897713 93378254227766046878173285)
          ·
            refine ⟨17508422667706133789657491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93378254227766046878173285 17508422667706133789657491)
            ·
              refine ⟨26262634001559200684486237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17508422667706133789657491 26262634001559200684486237)
              ·
                refine ⟨9848487750584700256682339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26262634001559200684486237 9848487750584700256682339)
                ·
                  refine ⟨14772731625877050385023509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9848487750584700256682339 14772731625877050385023509)
                  ·
                    refine ⟨692471794962986736797977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14772731625877050385023509 692471794962986736797977)
                    ·
                      rfl

theorem cell23_4045752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_4045752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045752 prefixEnd_4045752 := by exact prefixLift 4045752
  have htrace : WordTrace (prefixWord ++ tailWord_4045752) baseStart_4045752 baseEnd_4045752 := by
    simpa [prefixWord, tailWord_4045752, baseEnd_4045752] using wordTrace_append hprefix tailTrace_4045752
  have hstable : (prefixWord ++ tailWord_4045752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045752).length < 2 ^ (prefixWord ++ tailWord_4045752).sum := by decide
  have hdescent : baseEnd_4045752 < baseStart_4045752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045786 : List Nat := [3, 1, 1, 2, 4, 1, 3, 2, 2, 4]
def baseStart_4045786 : Nat := 118140960795 + 4045786 * 2 ^ 59
def prefixEnd_4045786 : Nat := 4983230072969 + 3 ^ 40 * 4045786 * 2
def baseEnd_4045786 : Nat := 692477614410404359122925

theorem tailTrace_4045786 : CollatzResearch.WordTrace tailWord_4045786 prefixEnd_4045786 692477614410404359122925 := by
  unfold tailWord_4045786
  simp only [CollatzResearch.WordTrace]
  refine ⟨36890484530203940520839303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98374625413877174722238141 36890484530203940520839303)
  ·
    refine ⟨55335726795305910781258955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36890484530203940520839303 55335726795305910781258955)
    ·
      refine ⟨83003590192958866171888433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55335726795305910781258955 83003590192958866171888433)
      ·
        refine ⟨62252692644719149628916325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83003590192958866171888433 62252692644719149628916325)
        ·
          refine ⟨11672379870884840555421811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62252692644719149628916325 11672379870884840555421811)
          ·
            refine ⟨17508569806327260833132717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11672379870884840555421811 17508569806327260833132717)
            ·
              refine ⟨6565713677372722812424769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17508569806327260833132717 6565713677372722812424769)
              ·
                refine ⟨4924285258029542109318577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6565713677372722812424769 4924285258029542109318577)
                ·
                  refine ⟨3693213943522156581988933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4924285258029542109318577 3693213943522156581988933)
                  ·
                    refine ⟨692477614410404359122925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3693213943522156581988933 692477614410404359122925)
                    ·
                      rfl

theorem cell23_4045786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_4045786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045786 prefixEnd_4045786 := by exact prefixLift 4045786
  have htrace : WordTrace (prefixWord ++ tailWord_4045786) baseStart_4045786 baseEnd_4045786 := by
    simpa [prefixWord, tailWord_4045786, baseEnd_4045786] using wordTrace_append hprefix tailTrace_4045786
  have hstable : (prefixWord ++ tailWord_4045786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045786).length < 2 ^ (prefixWord ++ tailWord_4045786).sum := by decide
  have hdescent : baseEnd_4045786 < baseStart_4045786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045792 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 3]
def baseStart_4045792 : Nat := 118140960795 + 4045792 * 2 ^ 59
def prefixEnd_4045792 : Nat := 4983230072969 + 3 ^ 40 * 4045792 * 2
def baseEnd_4045792 : Nat := 2077435924115140053893747

theorem tailTrace_4045792 : CollatzResearch.WordTrace tailWord_4045792 prefixEnd_4045792 2077435924115140053893747 := by
  unfold tailWord_4045792
  simp only [CollatzResearch.WordTrace]
  refine ⟨73781078479397012554037815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98374771305862683405383753 73781078479397012554037815)
  ·
    refine ⟨110671617719095518831056723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73781078479397012554037815 110671617719095518831056723)
    ·
      refine ⟨166007426578643278246585085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110671617719095518831056723 166007426578643278246585085)
      ·
        refine ⟨62252784966991229342469407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166007426578643278246585085 62252784966991229342469407)
        ·
          refine ⟨93379177450486844013704111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62252784966991229342469407 93379177450486844013704111)
          ·
            refine ⟨140068766175730266020556167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93379177450486844013704111 140068766175730266020556167)
            ·
              refine ⟨210103149263595399030834251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140068766175730266020556167 210103149263595399030834251)
              ·
                refine ⟨315154723895393098546251377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210103149263595399030834251 315154723895393098546251377)
                ·
                  refine ⟨236366042921544823909688533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315154723895393098546251377 236366042921544823909688533)
                  ·
                    refine ⟨5539829130973706810383325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 236366042921544823909688533 5539829130973706810383325)
                    ·
                      refine ⟨2077435924115140053893747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5539829130973706810383325 2077435924115140053893747)
                      ·
                        rfl

theorem cell23_4045792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_4045792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045792 prefixEnd_4045792 := by exact prefixLift 4045792
  have htrace : WordTrace (prefixWord ++ tailWord_4045792) baseStart_4045792 baseEnd_4045792 := by
    simpa [prefixWord, tailWord_4045792, baseEnd_4045792] using wordTrace_append hprefix tailTrace_4045792
  have hstable : (prefixWord ++ tailWord_4045792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045792).length < 2 ^ (prefixWord ++ tailWord_4045792).sum := by decide
  have hdescent : baseEnd_4045792 < baseStart_4045792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045860 : List Nat := [2, 3, 1, 4, 1, 1, 4, 1, 2, 1, 3]
def baseStart_4045860 : Nat := 118140960795 + 4045860 * 2 ^ 59
def prefixEnd_4045860 : Nat := 4983230072969 + 3 ^ 40 * 4045860 * 2
def baseEnd_4045860 : Nat := 2077470840799645787843435

theorem tailTrace_4045860 : CollatzResearch.WordTrace tailWord_4045860 prefixEnd_4045860 2077470840799645787843435 := by
  unfold tailWord_4045860
  simp only [CollatzResearch.WordTrace]
  refine ⟨73782318561273836360775517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98376424748365115147700689 73782318561273836360775517)
  ·
    refine ⟨27668369460477688635290819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73782318561273836360775517 27668369460477688635290819)
    ·
      refine ⟨41502554190716532952936229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27668369460477688635290819 41502554190716532952936229)
      ·
        refine ⟨7781728910759349928675543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41502554190716532952936229 7781728910759349928675543)
        ·
          refine ⟨11672593366139024893013315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781728910759349928675543 11672593366139024893013315)
          ·
            refine ⟨17508890049208537339519973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11672593366139024893013315 17508890049208537339519973)
            ·
              refine ⟨3282916884226600751159995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17508890049208537339519973 3282916884226600751159995)
              ·
                refine ⟨4924375326339901126739993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3282916884226600751159995 4924375326339901126739993)
                ·
                  refine ⟨3693281494754925845054995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4924375326339901126739993 3693281494754925845054995)
                  ·
                    refine ⟨5539922242132388767582493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3693281494754925845054995 5539922242132388767582493)
                    ·
                      refine ⟨2077470840799645787843435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5539922242132388767582493 2077470840799645787843435)
                      ·
                        rfl

theorem cell23_4045860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_4045860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045860 prefixEnd_4045860 := by exact prefixLift 4045860
  have htrace : WordTrace (prefixWord ++ tailWord_4045860) baseStart_4045860 baseEnd_4045860 := by
    simpa [prefixWord, tailWord_4045860, baseEnd_4045860] using wordTrace_append hprefix tailTrace_4045860
  have hstable : (prefixWord ++ tailWord_4045860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045860).length < 2 ^ (prefixWord ++ tailWord_4045860).sum := by decide
  have hdescent : baseEnd_4045860 < baseStart_4045860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045872 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 9]
def baseStart_4045872 : Nat := 118140960795 + 4045872 * 2 ^ 59
def prefixEnd_4045872 : Nat := 4983230072969 + 3 ^ 40 * 4045872 * 2
def baseEnd_4045872 : Nat := 230830778063055526765931

theorem tailTrace_4045872 : CollatzResearch.WordTrace tailWord_4045872 prefixEnd_4045872 230830778063055526765931 := by
  unfold tailWord_4045872
  simp only [CollatzResearch.WordTrace]
  refine ⟨73782537399252099385493935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98376716532336132513991913 73782537399252099385493935)
  ·
    refine ⟨110673806098878149078240903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73782537399252099385493935 110673806098878149078240903)
    ·
      refine ⟨166010709148317223617361355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110673806098878149078240903 166010709148317223617361355)
      ·
        refine ⟨249016063722475835426042033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166010709148317223617361355 249016063722475835426042033)
        ·
          refine ⟨186762047791856876569531525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249016063722475835426042033 186762047791856876569531525)
          ·
            refine ⟨35017883960973164356787161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186762047791856876569531525 35017883960973164356787161)
            ·
              refine ⟨26263412970729873267590371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35017883960973164356787161 26263412970729873267590371)
              ·
                refine ⟨39395119456094809901385557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26263412970729873267590371 39395119456094809901385557)
                ·
                  refine ⟨230830778063055526765931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39395119456094809901385557 230830778063055526765931)
                  ·
                    rfl

theorem cell23_4045872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 9].length) (baseStart_4045872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045872 prefixEnd_4045872 := by exact prefixLift 4045872
  have htrace : WordTrace (prefixWord ++ tailWord_4045872) baseStart_4045872 baseEnd_4045872 := by
    simpa [prefixWord, tailWord_4045872, baseEnd_4045872] using wordTrace_append hprefix tailTrace_4045872
  have hstable : (prefixWord ++ tailWord_4045872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045872).length < 2 ^ (prefixWord ++ tailWord_4045872).sum := by decide
  have hdescent : baseEnd_4045872 < baseStart_4045872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045886 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_4045886 : Nat := 118140960795 + 4045886 * 2 ^ 59
def prefixEnd_4045886 : Nat := 4983230072969 + 3 ^ 40 * 4045886 * 2
def baseEnd_4045886 : Nat := 2077484191296662686118315

theorem tailTrace_4045886 : CollatzResearch.WordTrace tailWord_4045886 prefixEnd_4045886 2077484191296662686118315 := by
  unfold tailWord_4045886
  simp only [CollatzResearch.WordTrace]
  refine ⟨18445698177556684895249689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98377056946968986107998341 18445698177556684895249689)
  ·
    refine ⟨13834273633167513671437267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18445698177556684895249689 13834273633167513671437267)
    ·
      refine ⟨20751410449751270507155901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13834273633167513671437267 20751410449751270507155901)
      ·
        refine ⟨7781778918656726440183463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20751410449751270507155901 7781778918656726440183463)
        ·
          refine ⟨11672668377985089660275195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781778918656726440183463 11672668377985089660275195)
          ·
            refine ⟨17509002566977634490412793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11672668377985089660275195 17509002566977634490412793)
            ·
              refine ⟨13131751925233225867809595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17509002566977634490412793 13131751925233225867809595)
              ·
                refine ⟨19697627887849838801714393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13131751925233225867809595 19697627887849838801714393)
                ·
                  refine ⟨14773220915887379101285795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19697627887849838801714393 14773220915887379101285795)
                  ·
                    refine ⟨22159831373831068651928693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14773220915887379101285795 22159831373831068651928693)
                    ·
                      refine ⟨2077484191296662686118315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22159831373831068651928693 2077484191296662686118315)
                      ·
                        rfl

theorem cell23_4045886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_4045886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045886 prefixEnd_4045886 := by exact prefixLift 4045886
  have htrace : WordTrace (prefixWord ++ tailWord_4045886) baseStart_4045886 baseEnd_4045886 := by
    simpa [prefixWord, tailWord_4045886, baseEnd_4045886] using wordTrace_append hprefix tailTrace_4045886
  have hstable : (prefixWord ++ tailWord_4045886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045886).length < 2 ^ (prefixWord ++ tailWord_4045886).sum := by decide
  have hdescent : baseEnd_4045886 < baseStart_4045886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045916 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_4045916 : Nat := 118140960795 + 4045916 * 2 ^ 59
def prefixEnd_4045916 : Nat := 4983230072969 + 3 ^ 40 * 4045916 * 2
def baseEnd_4045916 : Nat := 2077499595716297568743177

theorem tailTrace_4045916 : CollatzResearch.WordTrace tailWord_4045916 prefixEnd_4045916 2077499595716297568743177 := by
  unfold tailWord_4045916
  simp only [CollatzResearch.WordTrace]
  refine ⟨73783339805172397142794801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98377786406896529523726401 73783339805172397142794801)
  ·
    refine ⟨55337504853879297857096101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73783339805172397142794801 55337504853879297857096101)
    ·
      refine ⟨10375782160102368348205519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55337504853879297857096101 10375782160102368348205519)
      ·
        refine ⟨15563673240153552522308279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10375782160102368348205519 15563673240153552522308279)
        ·
          refine ⟨23345509860230328783462419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15563673240153552522308279 23345509860230328783462419)
          ·
            refine ⟨35018264790345493175193629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23345509860230328783462419 35018264790345493175193629)
            ·
              refine ⟨13131849296379559940697611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35018264790345493175193629 13131849296379559940697611)
              ·
                refine ⟨19697773944569339911046417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13131849296379559940697611 19697773944569339911046417)
                ·
                  refine ⟨14773330458427004933284813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19697773944569339911046417 14773330458427004933284813)
                  ·
                    refine ⟨5539998921910126849981805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14773330458427004933284813 5539998921910126849981805)
                    ·
                      refine ⟨2077499595716297568743177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5539998921910126849981805 2077499595716297568743177)
                      ·
                        rfl

theorem cell23_4045916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_4045916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045916 prefixEnd_4045916 := by exact prefixLift 4045916
  have htrace : WordTrace (prefixWord ++ tailWord_4045916) baseStart_4045916 baseEnd_4045916 := by
    simpa [prefixWord, tailWord_4045916, baseEnd_4045916] using wordTrace_append hprefix tailTrace_4045916
  have hstable : (prefixWord ++ tailWord_4045916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045916).length < 2 ^ (prefixWord ++ tailWord_4045916).sum := by decide
  have hdescent : baseEnd_4045916 < baseStart_4045916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4045976 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 1, 4, 3]
def baseStart_4045976 : Nat := 118140960795 + 4045976 * 2 ^ 59
def prefixEnd_4045976 : Nat := 4983230072969 + 3 ^ 40 * 4045976 * 2
def baseEnd_4045976 : Nat := 2077530404555567333992901

theorem tailTrace_4045976 : CollatzResearch.WordTrace tailWord_4045976 prefixEnd_4045976 2077530404555567333992901 := by
  unfold tailWord_4045976
  simp only [CollatzResearch.WordTrace]
  refine ⟨73784433995063712266386891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98379245326751616355182521 73784433995063712266386891)
  ·
    refine ⟨110676650992595568399580337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73784433995063712266386891 110676650992595568399580337)
    ·
      refine ⟨83007488244446676299685253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110676650992595568399580337 83007488244446676299685253)
      ·
        refine ⟨15563904045833751806190985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83007488244446676299685253 15563904045833751806190985)
        ·
          refine ⟨11672928034375313854643239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15563904045833751806190985 11672928034375313854643239)
          ·
            refine ⟨17509392051562970781964859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11672928034375313854643239 17509392051562970781964859)
            ·
              refine ⟨26264088077344456172947289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17509392051562970781964859 26264088077344456172947289)
              ·
                refine ⟨19698066058008342129710467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26264088077344456172947289 19698066058008342129710467)
                ·
                  refine ⟨29547099087012513194565701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19698066058008342129710467 29547099087012513194565701)
                  ·
                    refine ⟨5540081078814846223981069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29547099087012513194565701 5540081078814846223981069)
                    ·
                      refine ⟨2077530404555567333992901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5540081078814846223981069 2077530404555567333992901)
                      ·
                        rfl

theorem cell23_4045976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_4045976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4045976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4045976 prefixEnd_4045976 := by exact prefixLift 4045976
  have htrace : WordTrace (prefixWord ++ tailWord_4045976) baseStart_4045976 baseEnd_4045976 := by
    simpa [prefixWord, tailWord_4045976, baseEnd_4045976] using wordTrace_append hprefix tailTrace_4045976
  have hstable : (prefixWord ++ tailWord_4045976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4045976).length < 2 ^ (prefixWord ++ tailWord_4045976).sum := by decide
  have hdescent : baseEnd_4045976 < baseStart_4045976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4045976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046030 : List Nat := [4, 1, 1, 1, 5, 2, 2, 1, 6]
def baseStart_4046030 : Nat := 118140960795 + 4046030 * 2 ^ 59
def prefixEnd_4046030 : Nat := 4983230072969 + 3 ^ 40 * 4046030 * 2
def baseEnd_4046030 : Nat := 230839792501212235857517

theorem tailTrace_4046030 : CollatzResearch.WordTrace tailWord_4046030 prefixEnd_4046030 230839792501212235857517 := by
  unfold tailWord_4046030
  simp only [CollatzResearch.WordTrace]
  refine ⟨18446354691491473969404943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98380558354621194503493029 18446354691491473969404943)
  ·
    refine ⟨27669532037237210954107415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18446354691491473969404943 27669532037237210954107415)
    ·
      refine ⟨41504298055855816431161123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27669532037237210954107415 41504298055855816431161123)
      ·
        refine ⟨62256447083783724646741685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41504298055855816431161123 62256447083783724646741685)
        ·
          refine ⟨5836541914104724185632033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62256447083783724646741685 5836541914104724185632033)
          ·
            refine ⟨4377406435578543139224025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5836541914104724185632033 4377406435578543139224025)
            ·
              refine ⟨3283054826683907354418019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4377406435578543139224025 3283054826683907354418019)
              ·
                refine ⟨4924582240025861031627029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283054826683907354418019 4924582240025861031627029)
                ·
                  refine ⟨230839792501212235857517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4924582240025861031627029 230839792501212235857517)
                  ·
                    rfl

theorem cell23_4046030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_4046030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046030 prefixEnd_4046030 := by exact prefixLift 4046030
  have htrace : WordTrace (prefixWord ++ tailWord_4046030) baseStart_4046030 baseEnd_4046030 := by
    simpa [prefixWord, tailWord_4046030, baseEnd_4046030] using wordTrace_append hprefix tailTrace_4046030
  have hstable : (prefixWord ++ tailWord_4046030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046030).length < 2 ^ (prefixWord ++ tailWord_4046030).sum := by decide
  have hdescent : baseEnd_4046030 < baseStart_4046030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046056 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 1, 6]
def baseStart_4046056 : Nat := 118140960795 + 4046056 * 2 ^ 59
def prefixEnd_4046056 : Nat := 4983230072969 + 3 ^ 40 * 4046056 * 2
def baseEnd_4046056 : Nat := 692523827669309006997511

theorem tailTrace_4046056 : CollatzResearch.WordTrace tailWord_4046056 prefixEnd_4046056 692523827669309006997511 := by
  unfold tailWord_4046056
  simp only [CollatzResearch.WordTrace]
  refine ⟨73785892914918799097843011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98381190553225065463790681 73785892914918799097843011)
  ·
    refine ⟨110678839372378198646764517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73785892914918799097843011 110678839372378198646764517)
    ·
      refine ⟨20752282382320912246268347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110678839372378198646764517 20752282382320912246268347)
      ·
        refine ⟨31128423573481368369402521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20752282382320912246268347 31128423573481368369402521)
        ·
          refine ⟨23346317680111026277051891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31128423573481368369402521 23346317680111026277051891)
          ·
            refine ⟨35019476520166539415577837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23346317680111026277051891 35019476520166539415577837)
            ·
              refine ⟨13132303695062452280841689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35019476520166539415577837 13132303695062452280841689)
              ·
                refine ⟨9849227771296839210631267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13132303695062452280841689 9849227771296839210631267)
                ·
                  refine ⟨14773841656945258815946901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9849227771296839210631267 14773841656945258815946901)
                  ·
                    refine ⟨692523827669309006997511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14773841656945258815946901 692523827669309006997511)
                    ·
                      rfl

theorem cell23_4046056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_4046056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046056 prefixEnd_4046056 := by exact prefixLift 4046056
  have htrace : WordTrace (prefixWord ++ tailWord_4046056) baseStart_4046056 baseEnd_4046056 := by
    simpa [prefixWord, tailWord_4046056, baseEnd_4046056] using wordTrace_append hprefix tailTrace_4046056
  have hstable : (prefixWord ++ tailWord_4046056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046056).length < 2 ^ (prefixWord ++ tailWord_4046056).sum := by decide
  have hdescent : baseEnd_4046056 < baseStart_4046056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046068 : List Nat := [2, 6, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_4046068 : Nat := 118140960795 + 4046068 * 2 ^ 59
def prefixEnd_4046068 : Nat := 4983230072969 + 3 ^ 40 * 4046068 * 2
def baseEnd_4046068 : Nat := 692525881591926991347493

theorem tailTrace_4046068 : CollatzResearch.WordTrace tailWord_4046068 prefixEnd_4046068 692525881591926991347493 := by
  unfold tailWord_4046068
  simp only [CollatzResearch.WordTrace]
  refine ⟨73786111752897062122561429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98381482337196082830081905 73786111752897062122561429)
  ·
    refine ⟨3458723988417049786995067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73786111752897062122561429 3458723988417049786995067)
    ·
      refine ⟨5188085982625574680492601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3458723988417049786995067 5188085982625574680492601)
      ·
        refine ⟨3891064486969181010369451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5188085982625574680492601 3891064486969181010369451)
        ·
          refine ⟨5836596730453771515554177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3891064486969181010369451 5836596730453771515554177)
          ·
            refine ⟨4377447547840328636665633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5836596730453771515554177 4377447547840328636665633)
            ·
              refine ⟨3283085660880246477499225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4377447547840328636665633 3283085660880246477499225)
              ·
                refine ⟨2462314245660184858124419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3283085660880246477499225 2462314245660184858124419)
                ·
                  refine ⟨3693471368490277287186629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462314245660184858124419 3693471368490277287186629)
                  ·
                    refine ⟨692525881591926991347493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3693471368490277287186629 692525881591926991347493)
                    ·
                      rfl

theorem cell23_4046068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_4046068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046068 prefixEnd_4046068 := by exact prefixLift 4046068
  have htrace : WordTrace (prefixWord ++ tailWord_4046068) baseStart_4046068 baseEnd_4046068 := by
    simpa [prefixWord, tailWord_4046068, baseEnd_4046068] using wordTrace_append hprefix tailTrace_4046068
  have hstable : (prefixWord ++ tailWord_4046068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046068).length < 2 ^ (prefixWord ++ tailWord_4046068).sum := by decide
  have hdescent : baseEnd_4046068 < baseStart_4046068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046073 : List Nat := [1, 2, 1, 3, 1, 1, 6, 2, 2, 4]
def baseStart_4046073 : Nat := 118140960795 + 4046073 * 2 ^ 59
def prefixEnd_4046073 : Nat := 4983230072969 + 3 ^ 40 * 4046073 * 2
def baseEnd_4046073 : Nat := 692526737393017818159985

theorem tailTrace_4046073 : CollatzResearch.WordTrace tailWord_4046073 prefixEnd_4046073 692526737393017818159985 := by
  unfold tailWord_4046073
  simp only [CollatzResearch.WordTrace]
  refine ⟨147572405870776010099054873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98381603913850673399369915 147572405870776010099054873)
  ·
    refine ⟨110679304403082007574291155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147572405870776010099054873 110679304403082007574291155)
    ·
      refine ⟨166018956604623011361436733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110679304403082007574291155 166018956604623011361436733)
      ·
        refine ⟨62257108726733629260538775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166018956604623011361436733 62257108726733629260538775)
        ·
          refine ⟨93385663090100443890808163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62257108726733629260538775 93385663090100443890808163)
          ·
            refine ⟨140078494635150665836212245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93385663090100443890808163 140078494635150665836212245)
            ·
              refine ⟨6566179436022687461072449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140078494635150665836212245 6566179436022687461072449)
              ·
                refine ⟨4924634577017015595804337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6566179436022687461072449 4924634577017015595804337)
                ·
                  refine ⟨3693475932762761696853253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4924634577017015595804337 3693475932762761696853253)
                  ·
                    refine ⟨692526737393017818159985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3693475932762761696853253 692526737393017818159985)
                    ·
                      rfl

theorem cell23_4046073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 4].length) (baseStart_4046073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046073 prefixEnd_4046073 := by exact prefixLift 4046073
  have htrace : WordTrace (prefixWord ++ tailWord_4046073) baseStart_4046073 baseEnd_4046073 := by
    simpa [prefixWord, tailWord_4046073, baseEnd_4046073] using wordTrace_append hprefix tailTrace_4046073
  have hstable : (prefixWord ++ tailWord_4046073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046073).length < 2 ^ (prefixWord ++ tailWord_4046073).sum := by decide
  have hdescent : baseEnd_4046073 < baseStart_4046073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046113 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_4046113 : Nat := 118140960795 + 4046113 * 2 ^ 59
def prefixEnd_4046113 : Nat := 4983230072969 + 3 ^ 40 * 4046113 * 2
def baseEnd_4046113 : Nat := 2077600751405233297979771

theorem tailTrace_4046113 : CollatzResearch.WordTrace tailWord_4046113 prefixEnd_4046113 2077600751405233297979771 := by
  unfold tailWord_4046113
  simp only [CollatzResearch.WordTrace]
  refine ⟨147573864790631096930510993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98382576527087397953673995 147573864790631096930510993)
  ·
    refine ⟨110680398592973322697883245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147573864790631096930510993 110680398592973322697883245)
    ·
      refine ⟨41505149472364996011706217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110680398592973322697883245 41505149472364996011706217)
      ·
        refine ⟨31128862104273747008779663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41505149472364996011706217 31128862104273747008779663)
        ·
          refine ⟨46693293156410620513169495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31128862104273747008779663 46693293156410620513169495)
          ·
            refine ⟨70039939734615930769754243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46693293156410620513169495 70039939734615930769754243)
            ·
              refine ⟨105059909601923896154631365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70039939734615930769754243 105059909601923896154631365)
              ·
                refine ⟨19698733050360730528993381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105059909601923896154631365 19698733050360730528993381)
                ·
                  refine ⟨3693512446942636974186259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19698733050360730528993381 3693512446942636974186259)
                  ·
                    refine ⟨5540268670413955461279389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3693512446942636974186259 5540268670413955461279389)
                    ·
                      refine ⟨2077600751405233297979771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5540268670413955461279389 2077600751405233297979771)
                      ·
                        rfl

theorem cell23_4046113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_4046113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046113 prefixEnd_4046113 := by exact prefixLift 4046113
  have htrace : WordTrace (prefixWord ++ tailWord_4046113) baseStart_4046113 baseEnd_4046113 := by
    simpa [prefixWord, tailWord_4046113, baseEnd_4046113] using wordTrace_append hprefix tailTrace_4046113
  have hstable : (prefixWord ++ tailWord_4046113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046113).length < 2 ^ (prefixWord ++ tailWord_4046113).sum := by decide
  have hdescent : baseEnd_4046113 < baseStart_4046113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046114 : List Nat := [3, 3, 1, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_4046114 : Nat := 118140960795 + 4046114 * 2 ^ 59
def prefixEnd_4046114 : Nat := 4983230072969 + 3 ^ 40 * 4046114 * 2
def baseEnd_4046114 : Nat := 2077601264885887794067267

theorem tailTrace_4046114 : CollatzResearch.WordTrace tailWord_4046114 prefixEnd_4046114 2077601264885887794067267 := by
  unfold tailWord_4046114
  simp only [CollatzResearch.WordTrace]
  refine ⟨36893475315906868525324349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98382600842418316067531597 36893475315906868525324349)
  ·
    refine ⟨13835053243465075696996631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36893475315906868525324349 13835053243465075696996631)
    ·
      refine ⟨20752579865197613545494947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13835053243465075696996631 20752579865197613545494947)
      ·
        refine ⟨31128869797796420318242421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20752579865197613545494947 31128869797796420318242421)
        ·
          refine ⟨2918331543543414404835227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31128869797796420318242421 2918331543543414404835227)
          ·
            refine ⟨4377497315315121607252841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2918331543543414404835227 4377497315315121607252841)
            ·
              refine ⟨3283122986486341205439631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4377497315315121607252841 3283122986486341205439631)
              ·
                refine ⟨4924684479729511808159447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283122986486341205439631 4924684479729511808159447)
                ·
                  refine ⟨7387026719594267712239171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4924684479729511808159447 7387026719594267712239171)
                  ·
                    refine ⟨11080540079391401568358757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7387026719594267712239171 11080540079391401568358757)
                    ·
                      refine ⟨2077601264885887794067267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11080540079391401568358757 2077601264885887794067267)
                      ·
                        rfl

theorem cell23_4046114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_4046114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046114 prefixEnd_4046114 := by exact prefixLift 4046114
  have htrace : WordTrace (prefixWord ++ tailWord_4046114) baseStart_4046114 baseEnd_4046114 := by
    simpa [prefixWord, tailWord_4046114, baseEnd_4046114] using wordTrace_append hprefix tailTrace_4046114
  have hstable : (prefixWord ++ tailWord_4046114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046114).length < 2 ^ (prefixWord ++ tailWord_4046114).sum := by decide
  have hdescent : baseEnd_4046114 < baseStart_4046114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046117 : List Nat := [1, 3, 1, 2, 4, 3, 2, 1, 1, 2, 3]
def baseStart_4046117 : Nat := 118140960795 + 4046117 * 2 ^ 59
def prefixEnd_4046117 : Nat := 4983230072969 + 3 ^ 40 * 4046117 * 2
def baseEnd_4046117 : Nat := 2077602805327851282329753

theorem tailTrace_4046117 : CollatzResearch.WordTrace tailWord_4046117 prefixEnd_4046117 2077602805327851282329753 := by
  unfold tailWord_4046117
  simp only [CollatzResearch.WordTrace]
  refine ⟨147574010682616605613656605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98382673788411070409104403 147574010682616605613656605)
  ·
    refine ⟨55340254005981227105121227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147574010682616605613656605 55340254005981227105121227)
    ·
      refine ⟨83010381008971840657681841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55340254005981227105121227 83010381008971840657681841)
      ·
        refine ⟨62257785756728880493261381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83010381008971840657681841 62257785756728880493261381)
        ·
          refine ⟨11673334829386665092486509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62257785756728880493261381 11673334829386665092486509)
          ·
            refine ⟨4377500561019999409682441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11673334829386665092486509 4377500561019999409682441)
            ·
              refine ⟨3283125420764999557261831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4377500561019999409682441 3283125420764999557261831)
              ·
                refine ⟨4924688131147499335892747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283125420764999557261831 4924688131147499335892747)
                ·
                  refine ⟨7387032196721249003839121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4924688131147499335892747 7387032196721249003839121)
                  ·
                    refine ⟨5540274147540936752879341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7387032196721249003839121 5540274147540936752879341)
                    ·
                      refine ⟨2077602805327851282329753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5540274147540936752879341 2077602805327851282329753)
                      ·
                        rfl

theorem cell23_4046117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_4046117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046117 prefixEnd_4046117 := by exact prefixLift 4046117
  have htrace : WordTrace (prefixWord ++ tailWord_4046117) baseStart_4046117 baseEnd_4046117 := by
    simpa [prefixWord, tailWord_4046117, baseEnd_4046117] using wordTrace_append hprefix tailTrace_4046117
  have hstable : (prefixWord ++ tailWord_4046117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046117).length < 2 ^ (prefixWord ++ tailWord_4046117).sum := by decide
  have hdescent : baseEnd_4046117 < baseStart_4046117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046130 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_4046130 : Nat := 118140960795 + 4046130 * 2 ^ 59
def prefixEnd_4046130 : Nat := 4983230072969 + 3 ^ 40 * 4046130 * 2
def baseEnd_4046130 : Nat := 2077609480576359731467193

theorem tailTrace_4046130 : CollatzResearch.WordTrace tailWord_4046130 prefixEnd_4046130 2077609480576359731467193 := by
  unfold tailWord_4046130
  simp only [CollatzResearch.WordTrace]
  refine ⟨36893621207892377208469961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98382989887713005889253229 36893621207892377208469961)
  ·
    refine ⟨27670215905919282906352471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36893621207892377208469961 27670215905919282906352471)
    ·
      refine ⟨41505323858878924359528707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27670215905919282906352471 41505323858878924359528707)
      ·
        refine ⟨62257985788318386539293061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41505323858878924359528707 62257985788318386539293061)
        ·
          refine ⟨11673372335309697476117449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62257985788318386539293061 11673372335309697476117449)
          ·
            refine ⟨8755029251482273107088087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11673372335309697476117449 8755029251482273107088087)
            ·
              refine ⟨13132543877223409660632131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8755029251482273107088087 13132543877223409660632131)
              ·
                refine ⟨19698815815835114490948197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13132543877223409660632131 19698815815835114490948197)
                ·
                  refine ⟨3693527965469083967052787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19698815815835114490948197 3693527965469083967052787)
                  ·
                    refine ⟨5540291948203625950579181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3693527965469083967052787 5540291948203625950579181)
                    ·
                      refine ⟨2077609480576359731467193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5540291948203625950579181 2077609480576359731467193)
                      ·
                        rfl

theorem cell23_4046130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_4046130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046130 prefixEnd_4046130 := by exact prefixLift 4046130
  have htrace : WordTrace (prefixWord ++ tailWord_4046130) baseStart_4046130 baseEnd_4046130 := by
    simpa [prefixWord, tailWord_4046130, baseEnd_4046130] using wordTrace_append hprefix tailTrace_4046130
  have hstable : (prefixWord ++ tailWord_4046130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046130).length < 2 ^ (prefixWord ++ tailWord_4046130).sum := by decide
  have hdescent : baseEnd_4046130 < baseStart_4046130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046170 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2]
def baseStart_4046170 : Nat := 118140960795 + 4046170 * 2 ^ 59
def prefixEnd_4046170 : Nat := 4983230072969 + 3 ^ 40 * 4046170 * 2
def baseEnd_4046170 : Nat := 2077630019802539574967009

theorem tailTrace_4046170 : CollatzResearch.WordTrace tailWord_4046170 prefixEnd_4046170 2077630019802539574967009 := by
  unfold tailWord_4046170
  simp only [CollatzResearch.WordTrace]
  refine ⟨36893985937856148916333991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98383962500949730443557309 36893985937856148916333991)
  ·
    refine ⟨55340978906784223374500987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36893985937856148916333991 55340978906784223374500987)
    ·
      refine ⟨83011468360176335061751481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55340978906784223374500987 83011468360176335061751481)
      ·
        refine ⟨62258601270132251296313611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83011468360176335061751481 62258601270132251296313611)
        ·
          refine ⟨93387901905198376944470417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62258601270132251296313611 93387901905198376944470417)
          ·
            refine ⟨70040926428898782708352813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93387901905198376944470417 70040926428898782708352813)
            ·
              refine ⟨26265347410837043515632305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70040926428898782708352813 26265347410837043515632305)
              ·
                refine ⟨19699010558127782636724229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26265347410837043515632305 19699010558127782636724229)
                ·
                  refine ⟨3693564479648959244385793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19699010558127782636724229 3693564479648959244385793)
                  ·
                    refine ⟨2770173359736719433289345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3693564479648959244385793 2770173359736719433289345)
                    ·
                      refine ⟨2077630019802539574967009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2770173359736719433289345 2077630019802539574967009)
                      ·
                        rfl

theorem cell23_4046170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_4046170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046170 prefixEnd_4046170 := by exact prefixLift 4046170
  have htrace : WordTrace (prefixWord ++ tailWord_4046170) baseStart_4046170 baseEnd_4046170 := by
    simpa [prefixWord, tailWord_4046170, baseEnd_4046170] using wordTrace_append hprefix tailTrace_4046170
  have hstable : (prefixWord ++ tailWord_4046170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046170).length < 2 ^ (prefixWord ++ tailWord_4046170).sum := by decide
  have hdescent : baseEnd_4046170 < baseStart_4046170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046193 : List Nat := [1, 2, 2, 2, 1, 2, 2, 6, 5]
def baseStart_4046193 : Nat := 118140960795 + 4046193 * 2 ^ 59
def prefixEnd_4046193 : Nat := 4983230072969 + 3 ^ 40 * 4046193 * 2
def baseEnd_4046193 : Nat := 230849092206399220553267

theorem tailTrace_4046193 : CollatzResearch.WordTrace tailWord_4046193 prefixEnd_4046193 230849092206399220553267 := by
  unfold tailWord_4046193
  simp only [CollatzResearch.WordTrace]
  refine ⟨147576782630341270593423233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98384521753560847062282155 147576782630341270593423233)
  ·
    refine ⟨110682586972755952945067425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147576782630341270593423233 110682586972755952945067425)
    ·
      refine ⟨83011940229566964708800569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110682586972755952945067425 83011940229566964708800569)
      ·
        refine ⟨62258955172175223531600427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83011940229566964708800569 62258955172175223531600427)
        ·
          refine ⟨93388432758262835297400641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62258955172175223531600427 93388432758262835297400641)
          ·
            refine ⟨70041324568697126473050481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93388432758262835297400641 70041324568697126473050481)
            ·
              refine ⟨52530993426522844854787861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70041324568697126473050481 52530993426522844854787861)
              ·
                refine ⟨2462390316868258352568181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52530993426522844854787861 2462390316868258352568181)
                ·
                  refine ⟨230849092206399220553267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2462390316868258352568181 230849092206399220553267)
                  ·
                    rfl

theorem cell23_4046193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 5].length) (baseStart_4046193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046193 prefixEnd_4046193 := by exact prefixLift 4046193
  have htrace : WordTrace (prefixWord ++ tailWord_4046193) baseStart_4046193 baseEnd_4046193 := by
    simpa [prefixWord, tailWord_4046193, baseEnd_4046193] using wordTrace_append hprefix tailTrace_4046193
  have hstable : (prefixWord ++ tailWord_4046193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046193).length < 2 ^ (prefixWord ++ tailWord_4046193).sum := by decide
  have hdescent : baseEnd_4046193 < baseStart_4046193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046243 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 4]
def baseStart_4046243 : Nat := 118140960795 + 4046243 * 2 ^ 59
def prefixEnd_4046243 : Nat := 4983230072969 + 3 ^ 40 * 4046243 * 2
def baseEnd_4046243 : Nat := 2077667503890317789354173

theorem tailTrace_4046243 : CollatzResearch.WordTrace tailWord_4046243 prefixEnd_4046243 2077667503890317789354173 := by
  unfold tailWord_4046243
  simp only [CollatzResearch.WordTrace]
  refine ⟨147578606280160129132743383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98385737520106752755162255 147578606280160129132743383)
  ·
    refine ⟨221367909420240193699115075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147578606280160129132743383 221367909420240193699115075)
    ·
      refine ⟨332051864130360290548672613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221367909420240193699115075 332051864130360290548672613)
      ·
        refine ⟨62259724524442554477876115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332051864130360290548672613 62259724524442554477876115)
        ·
          refine ⟨93389586786663831716814173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62259724524442554477876115 93389586786663831716814173)
          ·
            refine ⟨35021095044998936893805315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93389586786663831716814173 35021095044998936893805315)
            ·
              refine ⟨52531642567498405340707973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35021095044998936893805315 52531642567498405340707973)
              ·
                refine ⟨9849682981405951001382745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52531642567498405340707973 9849682981405951001382745)
                ·
                  refine ⟨7387262236054463251037059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9849682981405951001382745 7387262236054463251037059)
                  ·
                    refine ⟨11080893354081694876555589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7387262236054463251037059 11080893354081694876555589)
                    ·
                      refine ⟨2077667503890317789354173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11080893354081694876555589 2077667503890317789354173)
                      ·
                        rfl

theorem cell23_4046243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_4046243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046243 prefixEnd_4046243 := by exact prefixLift 4046243
  have htrace : WordTrace (prefixWord ++ tailWord_4046243) baseStart_4046243 baseEnd_4046243 := by
    simpa [prefixWord, tailWord_4046243, baseEnd_4046243] using wordTrace_append hprefix tailTrace_4046243
  have hstable : (prefixWord ++ tailWord_4046243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046243).length < 2 ^ (prefixWord ++ tailWord_4046243).sum := by decide
  have hdescent : baseEnd_4046243 < baseStart_4046243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046256 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 6]
def baseStart_4046256 : Nat := 118140960795 + 4046256 * 2 ^ 59
def prefixEnd_4046256 : Nat := 4983230072969 + 3 ^ 40 * 4046256 * 2
def baseEnd_4046256 : Nat := 2077674179138826238491613

theorem tailTrace_4046256 : CollatzResearch.WordTrace tailWord_4046256 prefixEnd_4046256 2077674179138826238491613 := by
  unfold tailWord_4046256
  simp only [CollatzResearch.WordTrace]
  refine ⟨73789540214556516176483311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98386053619408688235311081 73789540214556516176483311)
  ·
    refine ⟨110684310321834774264724967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73789540214556516176483311 110684310321834774264724967)
    ·
      refine ⟨166026465482752161397087451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110684310321834774264724967 166026465482752161397087451)
      ·
        refine ⟨249039698224128242095631177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166026465482752161397087451 249039698224128242095631177)
        ·
          refine ⟨186779773668096181571723383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249039698224128242095631177 186779773668096181571723383)
          ·
            refine ⟨280169660502144272357585075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186779773668096181571723383 280169660502144272357585075)
            ·
              refine ⟨420254490753216408536377613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280169660502144272357585075 420254490753216408536377613)
              ·
                refine ⟨157595434032456153201141605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420254490753216408536377613 157595434032456153201141605)
                ·
                  refine ⟨29549143881085528725214051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157595434032456153201141605 29549143881085528725214051)
                  ·
                    refine ⟨44323715821628293087821077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29549143881085528725214051 44323715821628293087821077)
                    ·
                      refine ⟨2077674179138826238491613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44323715821628293087821077 2077674179138826238491613)
                      ·
                        rfl

theorem cell23_4046256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_4046256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046256 prefixEnd_4046256 := by exact prefixLift 4046256
  have htrace : WordTrace (prefixWord ++ tailWord_4046256) baseStart_4046256 baseEnd_4046256 := by
    simpa [prefixWord, tailWord_4046256, baseEnd_4046256] using wordTrace_append hprefix tailTrace_4046256
  have hstable : (prefixWord ++ tailWord_4046256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046256).length < 2 ^ (prefixWord ++ tailWord_4046256).sum := by decide
  have hdescent : baseEnd_4046256 < baseStart_4046256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046263 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 3]
def baseStart_4046263 : Nat := 118140960795 + 4046263 * 2 ^ 59
def prefixEnd_4046263 : Nat := 4983230072969 + 3 ^ 40 * 4046263 * 2
def baseEnd_4046263 : Nat := 2077677773503407711104081

theorem tailTrace_4046263 : CollatzResearch.WordTrace tailWord_4046263 prefixEnd_4046263 2077677773503407711104081 := by
  unfold tailWord_4046263
  simp only [CollatzResearch.WordTrace]
  refine ⟨147579335740087672548471443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98386223826725115032314295 147579335740087672548471443)
  ·
    refine ⟨221369003610131508822707165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147579335740087672548471443 221369003610131508822707165)
    ·
      refine ⟨83013376353799315808515187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221369003610131508822707165 83013376353799315808515187)
      ·
        refine ⟨124520064530698973712772781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83013376353799315808515187 124520064530698973712772781)
        ·
          refine ⟨46695024199012115142289793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124520064530698973712772781 46695024199012115142289793)
          ·
            refine ⟨35021268149259086356717345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46695024199012115142289793 35021268149259086356717345)
            ·
              refine ⟨26265951111944314767538009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35021268149259086356717345 26265951111944314767538009)
              ·
                refine ⟨19699463333958236075653507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26265951111944314767538009 19699463333958236075653507)
                ·
                  refine ⟨29549195000937354113480261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19699463333958236075653507 29549195000937354113480261)
                  ·
                    refine ⟨5540474062675753896277549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29549195000937354113480261 5540474062675753896277549)
                    ·
                      refine ⟨2077677773503407711104081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5540474062675753896277549 2077677773503407711104081)
                      ·
                        rfl

theorem cell23_4046263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_4046263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046263 prefixEnd_4046263 := by exact prefixLift 4046263
  have htrace : WordTrace (prefixWord ++ tailWord_4046263) baseStart_4046263 baseEnd_4046263 := by
    simpa [prefixWord, tailWord_4046263, baseEnd_4046263] using wordTrace_append hprefix tailTrace_4046263
  have hstable : (prefixWord ++ tailWord_4046263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046263).length < 2 ^ (prefixWord ++ tailWord_4046263).sum := by decide
  have hdescent : baseEnd_4046263 < baseStart_4046263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046266 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 12]
def baseStart_4046266 : Nat := 118140960795 + 4046266 * 2 ^ 59
def prefixEnd_4046266 : Nat := 4983230072969 + 3 ^ 40 * 4046266 * 2
def baseEnd_4046266 : Nat := 230853257105041244374063

theorem tailTrace_4046266 : CollatzResearch.WordTrace tailWord_4046266 prefixEnd_4046266 230853257105041244374063 := by
  unfold tailWord_4046266
  simp only [CollatzResearch.WordTrace]
  refine ⟨36894861289769201015207663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98386296772717869373887101 36894861289769201015207663)
  ·
    refine ⟨55342291934653801522811495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36894861289769201015207663 55342291934653801522811495)
    ·
      refine ⟨83013437901980702284217243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55342291934653801522811495 83013437901980702284217243)
      ·
        refine ⟨124520156852971053426325865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83013437901980702284217243 124520156852971053426325865)
        ·
          refine ⟨93390117639728290069744399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124520156852971053426325865 93390117639728290069744399)
          ·
            refine ⟨140085176459592435104616599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93390117639728290069744399 140085176459592435104616599)
            ·
              refine ⟨210127764689388652656924899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140085176459592435104616599 210127764689388652656924899)
              ·
                refine ⟨315191647034082978985387349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210127764689388652656924899 315191647034082978985387349)
                ·
                  refine ⟨230853257105041244374063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 315191647034082978985387349 230853257105041244374063)
                  ·
                    rfl

theorem cell23_4046266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_4046266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046266 prefixEnd_4046266 := by exact prefixLift 4046266
  have htrace : WordTrace (prefixWord ++ tailWord_4046266) baseStart_4046266 baseEnd_4046266 := by
    simpa [prefixWord, tailWord_4046266, baseEnd_4046266] using wordTrace_append hprefix tailTrace_4046266
  have hstable : (prefixWord ++ tailWord_4046266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046266).length < 2 ^ (prefixWord ++ tailWord_4046266).sum := by decide
  have hdescent : baseEnd_4046266 < baseStart_4046266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046320 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 1, 5, 2]
def baseStart_4046320 : Nat := 118140960795 + 4046320 * 2 ^ 59
def prefixEnd_4046320 : Nat := 4983230072969 + 3 ^ 40 * 4046320 * 2
def baseEnd_4046320 : Nat := 2077707041900713988091319

theorem tailTrace_4046320 : CollatzResearch.WordTrace tailWord_4046320 prefixEnd_4046320 2077707041900713988091319 := by
  unfold tailWord_4046320
  simp only [CollatzResearch.WordTrace]
  refine ⟨73790707350440585641648207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98387609800587447522197609 73790707350440585641648207)
  ·
    refine ⟨110686061025660878462472311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73790707350440585641648207 110686061025660878462472311)
    ·
      refine ⟨166029091538491317693708467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110686061025660878462472311 166029091538491317693708467)
      ·
        refine ⟨249043637307736976540562701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166029091538491317693708467 249043637307736976540562701)
        ·
          refine ⟨93391363990401366202711013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249043637307736976540562701 93391363990401366202711013)
          ·
            refine ⟨17510880748200256163008315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93391363990401366202711013 17510880748200256163008315)
            ·
              refine ⟨26266321122300384244512473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17510880748200256163008315 26266321122300384244512473)
              ·
                refine ⟨19699740841725288183384355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26266321122300384244512473 19699740841725288183384355)
                ·
                  refine ⟨29549611262587932275076533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19699740841725288183384355 29549611262587932275076533)
                  ·
                    refine ⟨2770276055867618650788425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29549611262587932275076533 2770276055867618650788425)
                    ·
                      refine ⟨2077707041900713988091319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2770276055867618650788425 2077707041900713988091319)
                      ·
                        rfl

theorem cell23_4046320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 5, 2].length) (baseStart_4046320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046320 prefixEnd_4046320 := by exact prefixLift 4046320
  have htrace : WordTrace (prefixWord ++ tailWord_4046320) baseStart_4046320 baseEnd_4046320 := by
    simpa [prefixWord, tailWord_4046320, baseEnd_4046320] using wordTrace_append hprefix tailTrace_4046320
  have hstable : (prefixWord ++ tailWord_4046320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046320).length < 2 ^ (prefixWord ++ tailWord_4046320).sum := by decide
  have hdescent : baseEnd_4046320 < baseStart_4046320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046330 : List Nat := [3, 1, 1, 1, 1, 2, 6, 2, 1, 5]
def baseStart_4046330 : Nat := 118140960795 + 4046330 * 2 ^ 59
def prefixEnd_4046330 : Nat := 4983230072969 + 3 ^ 40 * 4046330 * 2
def baseEnd_4046330 : Nat := 692570725569086316322091

theorem tailTrace_4046330 : CollatzResearch.WordTrace tailWord_4046330 prefixEnd_4046330 692570725569086316322091 := by
  unfold tailWord_4046330
  simp only [CollatzResearch.WordTrace]
  refine ⟨36895444857711235747790111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98387852953896628660773629 36895444857711235747790111)
  ·
    refine ⟨55343167286566853621685167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36895444857711235747790111 55343167286566853621685167)
    ·
      refine ⟨83014750929850280432527751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55343167286566853621685167 83014750929850280432527751)
      ·
        refine ⟨124522126394775420648791627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83014750929850280432527751 124522126394775420648791627)
        ·
          refine ⟨186783189592163130973187441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124522126394775420648791627 186783189592163130973187441)
          ·
            refine ⟨140087392194122348229890581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186783189592163130973187441 140087392194122348229890581)
            ·
              refine ⟨6566596509099485073276121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140087392194122348229890581 6566596509099485073276121)
              ·
                refine ⟨4924947381824613804957091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6566596509099485073276121 4924947381824613804957091)
                ·
                  refine ⟨7387421072736920707435637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4924947381824613804957091 7387421072736920707435637)
                  ·
                    refine ⟨692570725569086316322091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7387421072736920707435637 692570725569086316322091)
                    ·
                      rfl

theorem cell23_4046330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_4046330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046330 prefixEnd_4046330 := by exact prefixLift 4046330
  have htrace : WordTrace (prefixWord ++ tailWord_4046330) baseStart_4046330 baseEnd_4046330 := by
    simpa [prefixWord, tailWord_4046330, baseEnd_4046330] using wordTrace_append hprefix tailTrace_4046330
  have hstable : (prefixWord ++ tailWord_4046330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046330).length < 2 ^ (prefixWord ++ tailWord_4046330).sum := by decide
  have hdescent : baseEnd_4046330 < baseStart_4046330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046344 : List Nat := [2, 1, 3, 2, 1, 1, 5, 3, 1, 1, 3]
def baseStart_4046344 : Nat := 118140960795 + 4046344 * 2 ^ 59
def prefixEnd_4046344 : Nat := 4983230072969 + 3 ^ 40 * 4046344 * 2
def baseEnd_4046344 : Nat := 2077719365436421894191209

theorem tailTrace_4046344 : CollatzResearch.WordTrace tailWord_4046344 prefixEnd_4046344 2077719365436421894191209 := by
  unfold tailWord_4046344
  simp only [CollatzResearch.WordTrace]
  refine ⟨73791145026397111691085043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98388193368529482254780057 73791145026397111691085043)
  ·
    refine ⟨110686717539595667536627565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73791145026397111691085043 110686717539595667536627565)
    ·
      refine ⟨41507519077348375326235337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110686717539595667536627565 41507519077348375326235337)
      ·
        refine ⟨31130639308011281494676503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41507519077348375326235337 31130639308011281494676503)
        ·
          refine ⟨46695958962016922242014755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31130639308011281494676503 46695958962016922242014755)
          ·
            refine ⟨70043938443025383363022133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46695958962016922242014755 70043938443025383363022133)
            ·
              refine ⟨6566619229033629690283325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70043938443025383363022133 6566619229033629690283325)
              ·
                refine ⟨2462482210887611133856247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6566619229033629690283325 2462482210887611133856247)
                ·
                  refine ⟨3693723316331416700784371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462482210887611133856247 3693723316331416700784371)
                  ·
                    refine ⟨5540584974497125051176557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3693723316331416700784371 5540584974497125051176557)
                    ·
                      refine ⟨2077719365436421894191209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5540584974497125051176557 2077719365436421894191209)
                      ·
                        rfl

theorem cell23_4046344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_4046344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046344 prefixEnd_4046344 := by exact prefixLift 4046344
  have htrace : WordTrace (prefixWord ++ tailWord_4046344) baseStart_4046344 baseEnd_4046344 := by
    simpa [prefixWord, tailWord_4046344, baseEnd_4046344] using wordTrace_append hprefix tailTrace_4046344
  have hstable : (prefixWord ++ tailWord_4046344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046344).length < 2 ^ (prefixWord ++ tailWord_4046344).sum := by decide
  have hdescent : baseEnd_4046344 < baseStart_4046344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046370 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_4046370 : Nat := 118140960795 + 4046370 * 2 ^ 59
def prefixEnd_4046370 : Nat := 4983230072969 + 3 ^ 40 * 4046370 * 2
def baseEnd_4046370 : Nat := 2077732715933438792466089

theorem tailTrace_4046370 : CollatzResearch.WordTrace tailWord_4046370 prefixEnd_4046370 2077732715933438792466089 := by
  unfold tailWord_4046370
  simp only [CollatzResearch.WordTrace]
  refine ⟨36895809587675007455654141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98388825567133353215077709 36895809587675007455654141)
  ·
    refine ⟨13835928595378127795870303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36895809587675007455654141 13835928595378127795870303)
    ·
      refine ⟨20753892893067191693805455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13835928595378127795870303 20753892893067191693805455)
      ·
        refine ⟨31130839339600787540708183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20753892893067191693805455 31130839339600787540708183)
        ·
          refine ⟨46696259009401181311062275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31130839339600787540708183 46696259009401181311062275)
          ·
            refine ⟨70044388514101771966593413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46696259009401181311062275 70044388514101771966593413)
            ·
              refine ⟨13133322846394082243736265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70044388514101771966593413 13133322846394082243736265)
              ·
                refine ⟨9849992134795561682802199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13133322846394082243736265 9849992134795561682802199)
                ·
                  refine ⟨14774988202193342524203299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9849992134795561682802199 14774988202193342524203299)
                  ·
                    refine ⟨22162482303290013786304949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14774988202193342524203299 22162482303290013786304949)
                    ·
                      refine ⟨2077732715933438792466089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22162482303290013786304949 2077732715933438792466089)
                      ·
                        rfl

theorem cell23_4046370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_4046370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046370 prefixEnd_4046370 := by exact prefixLift 4046370
  have htrace : WordTrace (prefixWord ++ tailWord_4046370) baseStart_4046370 baseEnd_4046370 := by
    simpa [prefixWord, tailWord_4046370, baseEnd_4046370] using wordTrace_append hprefix tailTrace_4046370
  have hstable : (prefixWord ++ tailWord_4046370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046370).length < 2 ^ (prefixWord ++ tailWord_4046370).sum := by decide
  have hdescent : baseEnd_4046370 < baseStart_4046370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046387 : List Nat := [1, 1, 1, 2, 4, 3, 3, 2, 1, 2, 3]
def baseStart_4046387 : Nat := 118140960795 + 4046387 * 2 ^ 59
def prefixEnd_4046387 : Nat := 4983230072969 + 3 ^ 40 * 4046387 * 2
def baseEnd_4046387 : Nat := 2077741445104565225953511

theorem tailTrace_4046387 : CollatzResearch.WordTrace tailWord_4046387 prefixEnd_4046387 2077741445104565225953511 := by
  unfold tailWord_4046387
  simp only [CollatzResearch.WordTrace]
  refine ⟨147583858391638441725985415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98389238927758961150656943 147583858391638441725985415)
  ·
    refine ⟨221375787587457662588978123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147583858391638441725985415 221375787587457662588978123)
    ·
      refine ⟨332063681381186493883467185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221375787587457662588978123 332063681381186493883467185)
      ·
        refine ⟨249047761035889870412600389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332063681381186493883467185 249047761035889870412600389)
        ·
          refine ⟨46696455194229350702362573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249047761035889870412600389 46696455194229350702362573)
          ·
            refine ⟨17511170697836006513385965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46696455194229350702362573 17511170697836006513385965)
            ·
              refine ⟨6566689011688502442519737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17511170697836006513385965 6566689011688502442519737)
              ·
                refine ⟨4925016758766376831889803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6566689011688502442519737 4925016758766376831889803)
                ·
                  refine ⟨7387525138149565247834705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925016758766376831889803 7387525138149565247834705)
                  ·
                    refine ⟨5540643853612173935876029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7387525138149565247834705 5540643853612173935876029)
                    ·
                      refine ⟨2077741445104565225953511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5540643853612173935876029 2077741445104565225953511)
                      ·
                        rfl

theorem cell23_4046387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 2, 3].length) (baseStart_4046387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046387 prefixEnd_4046387 := by exact prefixLift 4046387
  have htrace : WordTrace (prefixWord ++ tailWord_4046387) baseStart_4046387 baseEnd_4046387 := by
    simpa [prefixWord, tailWord_4046387, baseEnd_4046387] using wordTrace_append hprefix tailTrace_4046387
  have hstable : (prefixWord ++ tailWord_4046387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046387).length < 2 ^ (prefixWord ++ tailWord_4046387).sum := by decide
  have hdescent : baseEnd_4046387 < baseStart_4046387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046397 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_4046397 : Nat := 118140960795 + 4046397 * 2 ^ 59
def prefixEnd_4046397 : Nat := 4983230072969 + 3 ^ 40 * 4046397 * 2
def baseEnd_4046397 : Nat := 2077746579911110186828465

theorem tailTrace_4046397 : CollatzResearch.WordTrace tailWord_4046397 prefixEnd_4046397 2077746579911110186828465 := by
  unfold tailWord_4046397
  simp only [CollatzResearch.WordTrace]
  refine ⟨147584223121602213433849445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98389482081068142289232963 147584223121602213433849445)
  ·
    refine ⟨27672041835300415018846771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147584223121602213433849445 27672041835300415018846771)
    ·
      refine ⟨41508062752950622528270157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27672041835300415018846771 41508062752950622528270157)
      ·
        refine ⟨15565523532356483448101309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41508062752950622528270157 15565523532356483448101309)
        ·
          refine ⟨5837071324633681293037991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15565523532356483448101309 5837071324633681293037991)
          ·
            refine ⟨8755606986950521939556987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5837071324633681293037991 8755606986950521939556987)
            ·
              refine ⟨13133410480425782909335481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8755606986950521939556987 13133410480425782909335481)
              ·
                refine ⟨9850057860319337182001611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13133410480425782909335481 9850057860319337182001611)
                ·
                  refine ⟨14775086790479005773002417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9850057860319337182001611 14775086790479005773002417)
                  ·
                    refine ⟨11081315092859254329751813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14775086790479005773002417 11081315092859254329751813)
                    ·
                      refine ⟨2077746579911110186828465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11081315092859254329751813 2077746579911110186828465)
                      ·
                        rfl

theorem cell23_4046397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_4046397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046397 prefixEnd_4046397 := by exact prefixLift 4046397
  have htrace : WordTrace (prefixWord ++ tailWord_4046397) baseStart_4046397 baseEnd_4046397 := by
    simpa [prefixWord, tailWord_4046397, baseEnd_4046397] using wordTrace_append hprefix tailTrace_4046397
  have hstable : (prefixWord ++ tailWord_4046397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046397).length < 2 ^ (prefixWord ++ tailWord_4046397).sum := by decide
  have hdescent : baseEnd_4046397 < baseStart_4046397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046401 : List Nat := [1, 2, 5, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_4046401 : Nat := 118140960795 + 4046401 * 2 ^ 59
def prefixEnd_4046401 : Nat := 4983230072969 + 3 ^ 40 * 4046401 * 2
def baseEnd_4046401 : Nat := 2077748633833728171178447

theorem tailTrace_4046401 : CollatzResearch.WordTrace tailWord_4046401 prefixEnd_4046401 2077748633833728171178447 := by
  unfold tailWord_4046401
  simp only [CollatzResearch.WordTrace]
  refine ⟨147584369013587722116995057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98389579342391814744663371 147584369013587722116995057)
  ·
    refine ⟨110688276760190791587746293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147584369013587722116995057 110688276760190791587746293)
    ·
      refine ⟨10377025946267886711351215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110688276760190791587746293 10377025946267886711351215)
      ·
        refine ⟨15565538919401830067026823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10377025946267886711351215 15565538919401830067026823)
        ·
          refine ⟨23348308379102745100540235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15565538919401830067026823 23348308379102745100540235)
          ·
            refine ⟨35022462568654117650810353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23348308379102745100540235 35022462568654117650810353)
            ·
              refine ⟨26266846926490588238107765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35022462568654117650810353 26266846926490588238107765)
              ·
                refine ⟨2462516899358492647322603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26266846926490588238107765 2462516899358492647322603)
                ·
                  refine ⟨3693775349037738970983905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462516899358492647322603 3693775349037738970983905)
                  ·
                    refine ⟨2770331511778304228237929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3693775349037738970983905 2770331511778304228237929)
                    ·
                      refine ⟨2077748633833728171178447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2770331511778304228237929 2077748633833728171178447)
                      ·
                        rfl

theorem cell23_4046401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_4046401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046401 prefixEnd_4046401 := by exact prefixLift 4046401
  have htrace : WordTrace (prefixWord ++ tailWord_4046401) baseStart_4046401 baseEnd_4046401 := by
    simpa [prefixWord, tailWord_4046401, baseEnd_4046401] using wordTrace_append hprefix tailTrace_4046401
  have hstable : (prefixWord ++ tailWord_4046401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046401).length < 2 ^ (prefixWord ++ tailWord_4046401).sum := by decide
  have hdescent : baseEnd_4046401 < baseStart_4046401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046418 : List Nat := [3, 2, 2, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_4046418 : Nat := 118140960795 + 4046418 * 2 ^ 59
def prefixEnd_4046418 : Nat := 4983230072969 + 3 ^ 40 * 4046418 * 2
def baseEnd_4046418 : Nat := 2077757363004854604665869

theorem tailTrace_4046418 : CollatzResearch.WordTrace tailWord_4046418 prefixEnd_4046418 2077757363004854604665869 := by
  unfold tailWord_4046418
  simp only [CollatzResearch.WordTrace]
  refine ⟨36896247263631533505090977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98389992703017422680242605 36896247263631533505090977)
  ·
    refine ⟨27672185447723650128818233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36896247263631533505090977 27672185447723650128818233)
    ·
      refine ⟨20754139085792737596613675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27672185447723650128818233 20754139085792737596613675)
      ·
        refine ⟨31131208628689106394920513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20754139085792737596613675 31131208628689106394920513)
        ·
          refine ⟨23348406471516829796190385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31131208628689106394920513 23348406471516829796190385)
          ·
            refine ⟨17511304853637622347142789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23348406471516829796190385 17511304853637622347142789)
            ·
              refine ⟨3283369660057054190089273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17511304853637622347142789 3283369660057054190089273)
              ·
                refine ⟨2462527245042790642566955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3283369660057054190089273 2462527245042790642566955)
                ·
                  refine ⟨3693790867564185963850433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462527245042790642566955 3693790867564185963850433)
                  ·
                    refine ⟨2770343150673139472887825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3693790867564185963850433 2770343150673139472887825)
                    ·
                      refine ⟨2077757363004854604665869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2770343150673139472887825 2077757363004854604665869)
                      ·
                        rfl

theorem cell23_4046418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_4046418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046418 prefixEnd_4046418 := by exact prefixLift 4046418
  have htrace : WordTrace (prefixWord ++ tailWord_4046418) baseStart_4046418 baseEnd_4046418 := by
    simpa [prefixWord, tailWord_4046418, baseEnd_4046418] using wordTrace_append hprefix tailTrace_4046418
  have hstable : (prefixWord ++ tailWord_4046418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046418).length < 2 ^ (prefixWord ++ tailWord_4046418).sum := by decide
  have hdescent : baseEnd_4046418 < baseStart_4046418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046457 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 1, 4, 2]
def baseStart_4046457 : Nat := 118140960795 + 4046457 * 2 ^ 59
def prefixEnd_4046457 : Nat := 4983230072969 + 3 ^ 40 * 4046457 * 2
def baseEnd_4046457 : Nat := 2077777388750379952078189

theorem tailTrace_4046457 : CollatzResearch.WordTrace tailWord_4046457 prefixEnd_4046457 2077777388750379952078189 := by
  unfold tailWord_4046457
  simp only [CollatzResearch.WordTrace]
  refine ⟨147586411501384843681033625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98390941000923229120689083 147586411501384843681033625)
  ·
    refine ⟨110689808626038632760775219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147586411501384843681033625 110689808626038632760775219)
    ·
      refine ⟨166034712939057949141162829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110689808626038632760775219 166034712939057949141162829)
      ·
        refine ⟨62263017352146730927936061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166034712939057949141162829 62263017352146730927936061)
        ·
          refine ⟨23348631507055024097976023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62263017352146730927936061 23348631507055024097976023)
          ·
            refine ⟨35022947260582536146964035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23348631507055024097976023 35022947260582536146964035)
            ·
              refine ⟨52534420890873804220446053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35022947260582536146964035 52534420890873804220446053)
              ·
                refine ⟨9850203917038838291333635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52534420890873804220446053 9850203917038838291333635)
                ·
                  refine ⟨14775305875558257437000453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9850203917038838291333635 14775305875558257437000453)
                  ·
                    refine ⟨2770369851667173269437585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14775305875558257437000453 2770369851667173269437585)
                    ·
                      refine ⟨2077777388750379952078189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2770369851667173269437585 2077777388750379952078189)
                      ·
                        rfl

theorem cell23_4046457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_4046457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046457 prefixEnd_4046457 := by exact prefixLift 4046457
  have htrace : WordTrace (prefixWord ++ tailWord_4046457) baseStart_4046457 baseEnd_4046457 := by
    simpa [prefixWord, tailWord_4046457, baseEnd_4046457] using wordTrace_append hprefix tailTrace_4046457
  have hstable : (prefixWord ++ tailWord_4046457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046457).length < 2 ^ (prefixWord ++ tailWord_4046457).sum := by decide
  have hdescent : baseEnd_4046457 < baseStart_4046457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046461 : List Nat := [1, 4, 1, 1, 4, 1, 4, 1, 1, 3, 2]
def baseStart_4046461 : Nat := 118140960795 + 4046461 * 2 ^ 59
def prefixEnd_4046461 : Nat := 4983230072969 + 3 ^ 40 * 4046461 * 2
def baseEnd_4046461 : Nat := 2077779442672997936428171

theorem tailTrace_4046461 : CollatzResearch.WordTrace tailWord_4046461 prefixEnd_4046461 2077779442672997936428171 := by
  unfold tailWord_4046461
  simp only [CollatzResearch.WordTrace]
  refine ⟨147586557393370352364179237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98391038262246901576119491 147586557393370352364179237)
  ·
    refine ⟨27672479511256941068283607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147586557393370352364179237 27672479511256941068283607)
    ·
      refine ⟨41508719266885411602425411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27672479511256941068283607 41508719266885411602425411)
      ·
        refine ⟨62263078900328117403638117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41508719266885411602425411 62263078900328117403638117)
        ·
          refine ⟨11674327293811522013182147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62263078900328117403638117 11674327293811522013182147)
          ·
            refine ⟨17511490940717283019773221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11674327293811522013182147 17511490940717283019773221)
            ·
              refine ⟨3283404551384490566207479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17511490940717283019773221 3283404551384490566207479)
              ·
                refine ⟨4925106827076735849311219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283404551384490566207479 4925106827076735849311219)
                ·
                  refine ⟨7387660240615103773966829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925106827076735849311219 7387660240615103773966829)
                  ·
                    refine ⟨2770372590230663915237561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7387660240615103773966829 2770372590230663915237561)
                    ·
                      refine ⟨2077779442672997936428171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2770372590230663915237561 2077779442672997936428171)
                      ·
                        rfl

theorem cell23_4046461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_4046461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046461 prefixEnd_4046461 := by exact prefixLift 4046461
  have htrace : WordTrace (prefixWord ++ tailWord_4046461) baseStart_4046461 baseEnd_4046461 := by
    simpa [prefixWord, tailWord_4046461, baseEnd_4046461] using wordTrace_append hprefix tailTrace_4046461
  have hstable : (prefixWord ++ tailWord_4046461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046461).length < 2 ^ (prefixWord ++ tailWord_4046461).sum := by decide
  have hdescent : baseEnd_4046461 < baseStart_4046461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046468 : List Nat := [2, 3, 2, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_4046468 : Nat := 118140960795 + 4046468 * 2 ^ 59
def prefixEnd_4046468 : Nat := 4983230072969 + 3 ^ 40 * 4046468 * 2
def baseEnd_4046468 : Nat := 2077783037037579409040639

theorem tailTrace_4046468 : CollatzResearch.WordTrace tailWord_4046468 prefixEnd_4046468 2077783037037579409040639 := by
  unfold tailWord_4046468
  simp only [CollatzResearch.WordTrace]
  refine ⟨73793406352172496279842029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98391208469563328373122705 73793406352172496279842029)
  ·
    refine ⟨27672527382064686104940761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73793406352172496279842029 27672527382064686104940761)
    ·
      refine ⟨20754395536548514578705571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27672527382064686104940761 20754395536548514578705571)
      ·
        refine ⟨31131593304822771868058357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20754395536548514578705571 31131593304822771868058357)
        ·
          refine ⟨2918586872327134862630471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31131593304822771868058357 2918586872327134862630471)
          ·
            refine ⟨4377880308490702293945707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2918586872327134862630471 4377880308490702293945707)
            ·
              refine ⟨6566820462736053440918561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4377880308490702293945707 6566820462736053440918561)
              ·
                refine ⟨4925115347052040080688921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6566820462736053440918561 4925115347052040080688921)
                ·
                  refine ⟨3693836510289030060516691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4925115347052040080688921 3693836510289030060516691)
                  ·
                    refine ⟨5540754765433545090775037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3693836510289030060516691 5540754765433545090775037)
                    ·
                      refine ⟨2077783037037579409040639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5540754765433545090775037 2077783037037579409040639)
                      ·
                        rfl

theorem cell23_4046468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_4046468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046468 prefixEnd_4046468 := by exact prefixLift 4046468
  have htrace : WordTrace (prefixWord ++ tailWord_4046468) baseStart_4046468 baseEnd_4046468 := by
    simpa [prefixWord, tailWord_4046468, baseEnd_4046468] using wordTrace_append hprefix tailTrace_4046468
  have hstable : (prefixWord ++ tailWord_4046468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046468).length < 2 ^ (prefixWord ++ tailWord_4046468).sum := by decide
  have hdescent : baseEnd_4046468 < baseStart_4046468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046483 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 8]
def baseStart_4046483 : Nat := 118140960795 + 4046483 * 2 ^ 59
def prefixEnd_4046483 : Nat := 4983230072969 + 3 ^ 40 * 4046483 * 2
def baseEnd_4046483 : Nat := 2077790739247396850353069

theorem tailTrace_4046483 : CollatzResearch.WordTrace tailWord_4046483 prefixEnd_4046483 2077790739247396850353069 := by
  unfold tailWord_4046483
  simp only [CollatzResearch.WordTrace]
  refine ⟨147587359799290650121480103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98391573199527100080986735 147587359799290650121480103)
  ·
    refine ⟨221381039698935975182220155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147587359799290650121480103 221381039698935975182220155)
    ·
      refine ⟨332071559548403962773330233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221381039698935975182220155 332071559548403962773330233)
      ·
        refine ⟨249053669661302972079997675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332071559548403962773330233 249053669661302972079997675)
        ·
          refine ⟨373580504491954458119996513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249053669661302972079997675 373580504491954458119996513)
          ·
            refine ⟨280185378368965843589997385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373580504491954458119996513 280185378368965843589997385)
            ·
              refine ⟨210139033776724382692498039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280185378368965843589997385 210139033776724382692498039)
              ·
                refine ⟨315208550665086574038747059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210139033776724382692498039 315208550665086574038747059)
                ·
                  refine ⟨472812825997629861058120589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315208550665086574038747059 472812825997629861058120589)
                  ·
                    refine ⟨177304809749111197896795221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 472812825997629861058120589 177304809749111197896795221)
                    ·
                      refine ⟨2077790739247396850353069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 177304809749111197896795221 2077790739247396850353069)
                      ·
                        rfl

theorem cell23_4046483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_4046483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046483 prefixEnd_4046483 := by exact prefixLift 4046483
  have htrace : WordTrace (prefixWord ++ tailWord_4046483) baseStart_4046483 baseEnd_4046483 := by
    simpa [prefixWord, tailWord_4046483, baseEnd_4046483] using wordTrace_append hprefix tailTrace_4046483
  have hstable : (prefixWord ++ tailWord_4046483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046483).length < 2 ^ (prefixWord ++ tailWord_4046483).sum := by decide
  have hdescent : baseEnd_4046483 < baseStart_4046483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046560 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 4]
def baseStart_4046560 : Nat := 118140960795 + 4046560 * 2 ^ 59
def prefixEnd_4046560 : Nat := 4983230072969 + 3 ^ 40 * 4046560 * 2
def baseEnd_4046560 : Nat := 2077830277257793049090215

theorem tailTrace_4046560 : CollatzResearch.WordTrace tailWord_4046560 prefixEnd_4046560 2077830277257793049090215 := by
  unfold tailWord_4046560
  simp only [CollatzResearch.WordTrace]
  refine ⟨73795084110005846136016567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98393445480007794848022089 73795084110005846136016567)
  ·
    refine ⟨110692626165008769204024851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73795084110005846136016567 110692626165008769204024851)
    ·
      refine ⟨166038939247513153806037277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110692626165008769204024851 166038939247513153806037277)
      ·
        refine ⟨62264602217817432677263979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166038939247513153806037277 62264602217817432677263979)
        ·
          refine ⟨93396903326726149015895969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62264602217817432677263979 93396903326726149015895969)
          ·
            refine ⟨70047677495044611761921977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93396903326726149015895969 70047677495044611761921977)
            ·
              refine ⟨52535758121283458821441483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70047677495044611761921977 52535758121283458821441483)
              ·
                refine ⟨78803637181925188232162225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52535758121283458821441483 78803637181925188232162225)
                ·
                  refine ⟨59102727886443891174121669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78803637181925188232162225 59102727886443891174121669)
                  ·
                    refine ⟨11081761478708229595147813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59102727886443891174121669 11081761478708229595147813)
                    ·
                      refine ⟨2077830277257793049090215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11081761478708229595147813 2077830277257793049090215)
                      ·
                        rfl

theorem cell23_4046560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_4046560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046560 prefixEnd_4046560 := by exact prefixLift 4046560
  have htrace : WordTrace (prefixWord ++ tailWord_4046560) baseStart_4046560 baseEnd_4046560 := by
    simpa [prefixWord, tailWord_4046560, baseEnd_4046560] using wordTrace_append hprefix tailTrace_4046560
  have hstable : (prefixWord ++ tailWord_4046560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046560).length < 2 ^ (prefixWord ++ tailWord_4046560).sum := by decide
  have hdescent : baseEnd_4046560 < baseStart_4046560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046570 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 10]
def baseStart_4046570 : Nat := 118140960795 + 4046570 * 2 ^ 59
def prefixEnd_4046570 : Nat := 4983230072969 + 3 ^ 40 * 4046570 * 2
def baseEnd_4046570 : Nat := 230870601340482001107241

theorem tailTrace_4046570 : CollatzResearch.WordTrace tailWord_4046570 prefixEnd_4046570 230870601340482001107241 := by
  unfold tailWord_4046570
  simp only [CollatzResearch.WordTrace]
  refine ⟨36897633237493865994974291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98393688633316975986598109 36897633237493865994974291)
  ·
    refine ⟨55346449856240798992461437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36897633237493865994974291 55346449856240798992461437)
    ·
      refine ⟨20754918696090299622173039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55346449856240798992461437 20754918696090299622173039)
      ·
        refine ⟨31132378044135449433259559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20754918696090299622173039 31132378044135449433259559)
        ·
          refine ⟨46698567066203174149889339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31132378044135449433259559 46698567066203174149889339)
          ·
            refine ⟨70047850599304761224834009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46698567066203174149889339 70047850599304761224834009)
            ·
              refine ⟨52535887949478570918625507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70047850599304761224834009 52535887949478570918625507)
              ·
                refine ⟨78803831924217856377938261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52535887949478570918625507 78803831924217856377938261)
                ·
                  refine ⟨230870601340482001107241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 78803831924217856377938261 230870601340482001107241)
                  ·
                    rfl

theorem cell23_4046570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_4046570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046570 prefixEnd_4046570 := by exact prefixLift 4046570
  have htrace : WordTrace (prefixWord ++ tailWord_4046570) baseStart_4046570 baseEnd_4046570 := by
    simpa [prefixWord, tailWord_4046570, baseEnd_4046570] using wordTrace_append hprefix tailTrace_4046570
  have hstable : (prefixWord ++ tailWord_4046570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046570).length < 2 ^ (prefixWord ++ tailWord_4046570).sum := by decide
  have hdescent : baseEnd_4046570 < baseStart_4046570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046591 : List Nat := [1, 1, 2, 2, 1, 3, 6, 2, 1, 4]
def baseStart_4046591 : Nat := 118140960795 + 4046591 * 2 ^ 59
def prefixEnd_4046591 : Nat := 4983230072969 + 3 ^ 40 * 4046591 * 2
def baseEnd_4046591 : Nat := 692615398386027475934191

theorem tailTrace_4046591 : CollatzResearch.WordTrace tailWord_4046591 prefixEnd_4046591 692615398386027475934191 := by
  unfold tailWord_4046591
  simp only [CollatzResearch.WordTrace]
  refine ⟨147591298882899384566411627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98394199255266256377607751 147591298882899384566411627)
  ·
    refine ⟨221386948324349076849617441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147591298882899384566411627 221386948324349076849617441)
    ·
      refine ⟨166040211243261807637213081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221386948324349076849617441 166040211243261807637213081)
      ·
        refine ⟨124530158432446355727909811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166040211243261807637213081 124530158432446355727909811)
        ·
          refine ⟨186795237648669533591864717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124530158432446355727909811 186795237648669533591864717)
          ·
            refine ⟨70048214118251075096949269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186795237648669533591864717 70048214118251075096949269)
            ·
              refine ⟨3283510036793019145169497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70048214118251075096949269 3283510036793019145169497)
              ·
                refine ⟨2462632527594764358877123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3283510036793019145169497 2462632527594764358877123)
                ·
                  refine ⟨3693948791392146538315685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462632527594764358877123 3693948791392146538315685)
                  ·
                    refine ⟨692615398386027475934191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3693948791392146538315685 692615398386027475934191)
                    ·
                      rfl

theorem cell23_4046591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 1, 4].length) (baseStart_4046591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046591 prefixEnd_4046591 := by exact prefixLift 4046591
  have htrace : WordTrace (prefixWord ++ tailWord_4046591) baseStart_4046591 baseEnd_4046591 := by
    simpa [prefixWord, tailWord_4046591, baseEnd_4046591] using wordTrace_append hprefix tailTrace_4046591
  have hstable : (prefixWord ++ tailWord_4046591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046591).length < 2 ^ (prefixWord ++ tailWord_4046591).sum := by decide
  have hdescent : baseEnd_4046591 < baseStart_4046591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046624 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 1, 5, 2]
def baseStart_4046624 : Nat := 118140960795 + 4046624 * 2 ^ 59
def prefixEnd_4046624 : Nat := 4983230072969 + 3 ^ 40 * 4046624 * 2
def baseEnd_4046624 : Nat := 2077863140019680798689921

theorem tailTrace_4046624 : CollatzResearch.WordTrace tailWord_4046624 prefixEnd_4046624 2077863140019680798689921 := by
  unfold tailWord_4046624
  simp only [CollatzResearch.WordTrace]
  refine ⟨73796251245889915601181463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98395001661186554134908617 73796251245889915601181463)
  ·
    refine ⟨110694376868834873401772195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73796251245889915601181463 110694376868834873401772195)
    ·
      refine ⟨166041565303252310102658293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110694376868834873401772195 166041565303252310102658293)
      ·
        refine ⟨15566396747179904072124215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166041565303252310102658293 15566396747179904072124215)
        ·
          refine ⟨23349595120769856108186323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15566396747179904072124215 23349595120769856108186323)
          ·
            refine ⟨35024392681154784162279485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23349595120769856108186323 35024392681154784162279485)
            ·
              refine ⟨13134147255433044060854807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35024392681154784162279485 13134147255433044060854807)
              ·
                refine ⟨19701220883149566091282211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13134147255433044060854807 19701220883149566091282211)
                ·
                  refine ⟨29551831324724349136923317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19701220883149566091282211 29551831324724349136923317)
                  ·
                    refine ⟨2770484186692907731586561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29551831324724349136923317 2770484186692907731586561)
                    ·
                      refine ⟨2077863140019680798689921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2770484186692907731586561 2077863140019680798689921)
                      ·
                        rfl

theorem cell23_4046624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_4046624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046624 prefixEnd_4046624 := by exact prefixLift 4046624
  have htrace : WordTrace (prefixWord ++ tailWord_4046624) baseStart_4046624 baseEnd_4046624 := by
    simpa [prefixWord, tailWord_4046624, baseEnd_4046624] using wordTrace_append hprefix tailTrace_4046624
  have hstable : (prefixWord ++ tailWord_4046624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046624).length < 2 ^ (prefixWord ++ tailWord_4046624).sum := by decide
  have hdescent : baseEnd_4046624 < baseStart_4046624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046638 : List Nat := [4, 1, 3, 2, 3, 1, 1, 2, 6]
def baseStart_4046638 : Nat := 118140960795 + 4046638 * 2 ^ 59
def prefixEnd_4046638 : Nat := 4983230072969 + 3 ^ 40 * 4046638 * 2
def baseEnd_4046638 : Nat := 230874480972093749323873

theorem tailTrace_4046638 : CollatzResearch.WordTrace tailWord_4046638 prefixEnd_4046638 230874480972093749323873 := by
  unfold tailWord_4046638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18449126639216138949171571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98395342075819407728915045 18449126639216138949171571)
  ·
    refine ⟨27673689958824208423757357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18449126639216138949171571 27673689958824208423757357)
    ·
      refine ⟨10377633734559078158909009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27673689958824208423757357 10377633734559078158909009)
      ·
        refine ⟨7783225300919308619181757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10377633734559078158909009 7783225300919308619181757)
        ·
          refine ⟨2918709487844740732193159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7783225300919308619181757 2918709487844740732193159)
          ·
            refine ⟨4378064231767111098289739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2918709487844740732193159 4378064231767111098289739)
            ·
              refine ⟨6567096347650666647434609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378064231767111098289739 6567096347650666647434609)
              ·
                refine ⟨4925322260737999985575957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6567096347650666647434609 4925322260737999985575957)
                ·
                  refine ⟨230874480972093749323873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4925322260737999985575957 230874480972093749323873)
                  ·
                    rfl

theorem cell23_4046638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_4046638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046638 prefixEnd_4046638 := by exact prefixLift 4046638
  have htrace : WordTrace (prefixWord ++ tailWord_4046638) baseStart_4046638 baseEnd_4046638 := by
    simpa [prefixWord, tailWord_4046638, baseEnd_4046638] using wordTrace_append hprefix tailTrace_4046638
  have hstable : (prefixWord ++ tailWord_4046638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046638).length < 2 ^ (prefixWord ++ tailWord_4046638).sum := by decide
  have hdescent : baseEnd_4046638 < baseStart_4046638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046664 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 1, 6]
def baseStart_4046664 : Nat := 118140960795 + 4046664 * 2 ^ 59
def prefixEnd_4046664 : Nat := 4983230072969 + 3 ^ 40 * 4046664 * 2
def baseEnd_4046664 : Nat := 692627893081953547396579

theorem tailTrace_4046664 : CollatzResearch.WordTrace tailWord_4046664 prefixEnd_4046664 692627893081953547396579 := by
  unfold tailWord_4046664
  simp only [CollatzResearch.WordTrace]
  refine ⟨73796980705817459016909523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98395974274423278689212697 73796980705817459016909523)
  ·
    refine ⟨110695471058726188525364285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73796980705817459016909523 110695471058726188525364285)
    ·
      refine ⟨41510801647022320697011607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110695471058726188525364285 41510801647022320697011607)
      ·
        refine ⟨62266202470533481045517411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41510801647022320697011607 62266202470533481045517411)
        ·
          refine ⟨93399303705800221568276117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62266202470533481045517411 93399303705800221568276117)
          ·
            refine ⟨4378092361209385386012943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93399303705800221568276117 4378092361209385386012943)
            ·
              refine ⟨6567138541814078079019415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378092361209385386012943 6567138541814078079019415)
              ·
                refine ⟨9850707812721117118529123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6567138541814078079019415 9850707812721117118529123)
                ·
                  refine ⟨14776061719081675677793685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9850707812721117118529123 14776061719081675677793685)
                  ·
                    refine ⟨692627893081953547396579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14776061719081675677793685 692627893081953547396579)
                    ·
                      rfl

theorem cell23_4046664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_4046664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046664 prefixEnd_4046664 := by exact prefixLift 4046664
  have htrace : WordTrace (prefixWord ++ tailWord_4046664) baseStart_4046664 baseEnd_4046664 := by
    simpa [prefixWord, tailWord_4046664, baseEnd_4046664] using wordTrace_append hprefix tailTrace_4046664
  have hstable : (prefixWord ++ tailWord_4046664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046664).length < 2 ^ (prefixWord ++ tailWord_4046664).sum := by decide
  have hdescent : baseEnd_4046664 < baseStart_4046664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046677 : List Nat := [1, 3, 2, 2, 2, 3, 1, 9]
def baseStart_4046677 : Nat := 118140960795 + 4046677 * 2 ^ 59
def prefixEnd_4046677 : Nat := 4983230072969 + 3 ^ 40 * 4046677 * 2
def baseEnd_4046677 : Nat := 76958902018309966345451

theorem tailTrace_4046677 : CollatzResearch.WordTrace tailWord_4046677 prefixEnd_4046677 76958902018309966345451 := by
  unfold tailWord_4046677
  simp only [CollatzResearch.WordTrace]
  refine ⟨147594435560587821254042285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98396290373725214169361523 147594435560587821254042285)
  ·
    refine ⟨55347913335220432970265857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147594435560587821254042285 55347913335220432970265857)
    ·
      refine ⟨41510935001415324727699393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55347913335220432970265857 41510935001415324727699393)
      ·
        refine ⟨31133201251061493545774545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41510935001415324727699393 31133201251061493545774545)
        ·
          refine ⟨23349900938296120159330909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31133201251061493545774545 23349900938296120159330909)
          ·
            refine ⟨8756212851861045059749091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23349900938296120159330909 8756212851861045059749091)
            ·
              refine ⟨13134319277791567589623637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8756212851861045059749091 13134319277791567589623637)
              ·
                refine ⟨76958902018309966345451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13134319277791567589623637 76958902018309966345451)
                ·
                  rfl

theorem cell23_4046677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 9].length) (baseStart_4046677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046677 prefixEnd_4046677 := by exact prefixLift 4046677
  have htrace : WordTrace (prefixWord ++ tailWord_4046677) baseStart_4046677 baseEnd_4046677 := by
    simpa [prefixWord, tailWord_4046677, baseEnd_4046677] using wordTrace_append hprefix tailTrace_4046677
  have hstable : (prefixWord ++ tailWord_4046677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046677).length < 2 ^ (prefixWord ++ tailWord_4046677).sum := by decide
  have hdescent : baseEnd_4046677 < baseStart_4046677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046705 : List Nat := [1, 2, 2, 2, 1, 3, 5, 2, 1, 2, 2]
def baseStart_4046705 : Nat := 118140960795 + 4046705 * 2 ^ 59
def prefixEnd_4046705 : Nat := 4983230072969 + 3 ^ 40 * 4046705 * 2
def baseEnd_4046705 : Nat := 2077904731952694981777049

theorem tailTrace_4046705 : CollatzResearch.WordTrace tailWord_4046705 prefixEnd_4046705 2077904731952694981777049 := by
  unfold tailWord_4046705
  simp only [CollatzResearch.WordTrace]
  refine ⟨147595456804486382036061569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98396971202990921357374379 147595456804486382036061569)
  ·
    refine ⟨110696592603364786527046177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147595456804486382036061569 110696592603364786527046177)
    ·
      refine ⟨83022444452523589895284633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110696592603364786527046177 83022444452523589895284633)
      ·
        refine ⟨62266833339392692421463475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83022444452523589895284633 62266833339392692421463475)
        ·
          refine ⟨93400250009089038632195213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62266833339392692421463475 93400250009089038632195213)
          ·
            refine ⟨35025093753408389487073205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93400250009089038632195213 35025093753408389487073205)
            ·
              refine ⟨3283602539382036514413113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35025093753408389487073205 3283602539382036514413113)
              ·
                refine ⟨2462701904536527385809835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3283602539382036514413113 2462701904536527385809835)
                ·
                  refine ⟨3694052856804791078714753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462701904536527385809835 3694052856804791078714753)
                  ·
                    refine ⟨2770539642603593309036065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3694052856804791078714753 2770539642603593309036065)
                    ·
                      refine ⟨2077904731952694981777049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2770539642603593309036065 2077904731952694981777049)
                      ·
                        rfl

theorem cell23_4046705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_4046705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046705 prefixEnd_4046705 := by exact prefixLift 4046705
  have htrace : WordTrace (prefixWord ++ tailWord_4046705) baseStart_4046705 baseEnd_4046705 := by
    simpa [prefixWord, tailWord_4046705, baseEnd_4046705] using wordTrace_append hprefix tailTrace_4046705
  have hstable : (prefixWord ++ tailWord_4046705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046705).length < 2 ^ (prefixWord ++ tailWord_4046705).sum := by decide
  have hdescent : baseEnd_4046705 < baseStart_4046705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046742 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_4046742 : Nat := 118140960795 + 4046742 * 2 ^ 59
def prefixEnd_4046742 : Nat := 4983230072969 + 3 ^ 40 * 4046742 * 2
def baseEnd_4046742 : Nat := 2077923730736911337014379

theorem tailTrace_4046742 : CollatzResearch.WordTrace tailWord_4046742 prefixEnd_4046742 2077923730736911337014379 := by
  unfold tailWord_4046742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9224800394084521084697405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98397870870234891570105653 9224800394084521084697405)
  ·
    refine ⟨3459300147781695406761527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9224800394084521084697405 3459300147781695406761527)
    ·
      refine ⟨5188950221672543110142291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3459300147781695406761527 5188950221672543110142291)
      ·
        refine ⟨7783425332508814665213437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5188950221672543110142291 7783425332508814665213437)
        ·
          refine ⟨2918784499690805499455039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7783425332508814665213437 2918784499690805499455039)
          ·
            refine ⟨4378176749536208249182559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2918784499690805499455039 4378176749536208249182559)
            ·
              refine ⟨6567265124304312373773839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378176749536208249182559 6567265124304312373773839)
              ·
                refine ⟨9850897686456468560660759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6567265124304312373773839 9850897686456468560660759)
                ·
                  refine ⟨14776346529684702840991139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9850897686456468560660759 14776346529684702840991139)
                  ·
                    refine ⟨22164519794527054261486709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14776346529684702840991139 22164519794527054261486709)
                    ·
                      refine ⟨2077923730736911337014379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22164519794527054261486709 2077923730736911337014379)
                      ·
                        rfl

theorem cell23_4046742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_4046742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046742 prefixEnd_4046742 := by exact prefixLift 4046742
  have htrace : WordTrace (prefixWord ++ tailWord_4046742) baseStart_4046742 baseEnd_4046742 := by
    simpa [prefixWord, tailWord_4046742, baseEnd_4046742] using wordTrace_append hprefix tailTrace_4046742
  have hstable : (prefixWord ++ tailWord_4046742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046742).length < 2 ^ (prefixWord ++ tailWord_4046742).sum := by decide
  have hdescent : baseEnd_4046742 < baseStart_4046742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046757 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_4046757 : Nat := 118140960795 + 4046757 * 2 ^ 59
def prefixEnd_4046757 : Nat := 4983230072969 + 3 ^ 40 * 4046757 * 2
def baseEnd_4046757 : Nat := 2077931432946728778326809

theorem tailTrace_4046757 : CollatzResearch.WordTrace tailWord_4046757 prefixEnd_4046757 2077931432946728778326809 := by
  unfold tailWord_4046757
  simp only [CollatzResearch.WordTrace]
  refine ⟨147597353400297994916954525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98398235600198663277969683 147597353400297994916954525)
  ·
    refine ⟨55349007525111748093857947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147597353400297994916954525 55349007525111748093857947)
    ·
      refine ⟨83023511287667622140786921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55349007525111748093857947 83023511287667622140786921)
      ·
        refine ⟨62267633465750716605590191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83023511287667622140786921 62267633465750716605590191)
        ·
          refine ⟨93401450198626074908385287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62267633465750716605590191 93401450198626074908385287)
          ·
            refine ⟨140102175297939112362577931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93401450198626074908385287 140102175297939112362577931)
            ·
              refine ⟨210153262946908668543866897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140102175297939112362577931 210153262946908668543866897)
              ·
                refine ⟨157614947210181501407900173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210153262946908668543866897 157614947210181501407900173)
                ·
                  refine ⟨59105605203818063027962565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157614947210181501407900173 59105605203818063027962565)
                  ·
                    refine ⟨11082300975715886817742981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59105605203818063027962565 11082300975715886817742981)
                    ·
                      refine ⟨2077931432946728778326809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11082300975715886817742981 2077931432946728778326809)
                      ·
                        rfl

theorem cell23_4046757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_4046757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046757 prefixEnd_4046757 := by exact prefixLift 4046757
  have htrace : WordTrace (prefixWord ++ tailWord_4046757) baseStart_4046757 baseEnd_4046757 := by
    simpa [prefixWord, tailWord_4046757, baseEnd_4046757] using wordTrace_append hprefix tailTrace_4046757
  have hstable : (prefixWord ++ tailWord_4046757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046757).length < 2 ^ (prefixWord ++ tailWord_4046757).sum := by decide
  have hdescent : baseEnd_4046757 < baseStart_4046757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046767 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 7]
def baseStart_4046767 : Nat := 118140960795 + 4046767 * 2 ^ 59
def prefixEnd_4046767 : Nat := 4983230072969 + 3 ^ 40 * 4046767 * 2
def baseEnd_4046767 : Nat := 230881840861474859911307

theorem tailTrace_4046767 : CollatzResearch.WordTrace tailWord_4046767 prefixEnd_4046767 230881840861474859911307 := by
  unfold tailWord_4046767
  simp only [CollatzResearch.WordTrace]
  refine ⟨147597718130261766624818555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98398478753507844416545703 147597718130261766624818555)
  ·
    refine ⟨221396577195392649937227833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147597718130261766624818555 221396577195392649937227833)
    ·
      refine ⟨166047432896544487452920875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221396577195392649937227833 166047432896544487452920875)
      ·
        refine ⟨249071149344816731179381313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166047432896544487452920875 249071149344816731179381313)
        ·
          refine ⟨186803362008612548384535985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249071149344816731179381313 186803362008612548384535985)
          ·
            refine ⟨140102521506459411288401989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186803362008612548384535985 140102521506459411288401989)
            ·
              refine ⟨26269222782461139616575373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140102521506459411288401989 26269222782461139616575373)
              ·
                refine ⟨9850958543422927356215765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26269222782461139616575373 9850958543422927356215765)
                ·
                  refine ⟨230881840861474859911307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9850958543422927356215765 230881840861474859911307)
                  ·
                    rfl

theorem cell23_4046767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 7].length) (baseStart_4046767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046767 prefixEnd_4046767 := by exact prefixLift 4046767
  have htrace : WordTrace (prefixWord ++ tailWord_4046767) baseStart_4046767 baseEnd_4046767 := by
    simpa [prefixWord, tailWord_4046767, baseEnd_4046767] using wordTrace_append hprefix tailTrace_4046767
  have hstable : (prefixWord ++ tailWord_4046767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046767).length < 2 ^ (prefixWord ++ tailWord_4046767).sum := by decide
  have hdescent : baseEnd_4046767 < baseStart_4046767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046818 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 7]
def baseStart_4046818 : Nat := 118140960795 + 4046818 * 2 ^ 59
def prefixEnd_4046818 : Nat := 4983230072969 + 3 ^ 40 * 4046818 * 2
def baseEnd_4046818 : Nat := 230884750585183671073781

theorem tailTrace_4046818 : CollatzResearch.WordTrace tailWord_4046818 prefixEnd_4046818 230884750585183671073781 := by
  unfold tailWord_4046818
  simp only [CollatzResearch.WordTrace]
  refine ⟨36899894563269250583731277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98399718835384668223283405 36899894563269250583731277)
  ·
    refine ⟨13837460461225968968899229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36899894563269250583731277 13837460461225968968899229)
    ·
      refine ⟨5189047672959738363337211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13837460461225968968899229 5189047672959738363337211)
      ·
        refine ⟨7783571509439607545005817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5189047672959738363337211 7783571509439607545005817)
        ·
          refine ⟨5837678632079705658754363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7783571509439607545005817 5837678632079705658754363)
          ·
            refine ⟨8756517948119558488131545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5837678632079705658754363 8756517948119558488131545)
            ·
              refine ⟨6567388461089668866098659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8756517948119558488131545 6567388461089668866098659)
              ·
                refine ⟨9851082691634503299147989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6567388461089668866098659 9851082691634503299147989)
                ·
                  refine ⟨230884750585183671073781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9851082691634503299147989 230884750585183671073781)
                  ·
                    rfl

theorem cell23_4046818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_4046818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046818 prefixEnd_4046818 := by exact prefixLift 4046818
  have htrace : WordTrace (prefixWord ++ tailWord_4046818) baseStart_4046818 baseEnd_4046818 := by
    simpa [prefixWord, tailWord_4046818, baseEnd_4046818] using wordTrace_append hprefix tailTrace_4046818
  have hstable : (prefixWord ++ tailWord_4046818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046818).length < 2 ^ (prefixWord ++ tailWord_4046818).sum := by decide
  have hdescent : baseEnd_4046818 < baseStart_4046818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046829 : List Nat := [1, 5, 1, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4046829 : Nat := 118140960795 + 4046829 * 2 ^ 59
def prefixEnd_4046829 : Nat := 4983230072969 + 3 ^ 40 * 4046829 * 2
def baseEnd_4046829 : Nat := 2077968403553852496626479

theorem tailTrace_4046829 : CollatzResearch.WordTrace tailWord_4046829 prefixEnd_4046829 2077968403553852496626479 := by
  unfold tailWord_4046829
  simp only [CollatzResearch.WordTrace]
  refine ⟨147599979456037151213575541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98399986304024767475717027 147599979456037151213575541)
  ·
    refine ⟨13837498074003482926272707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147599979456037151213575541 13837498074003482926272707)
    ·
      refine ⟨20756247111005224389409061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13837498074003482926272707 20756247111005224389409061)
      ·
        refine ⟨3891796333313479573014199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20756247111005224389409061 3891796333313479573014199)
        ·
          refine ⟨5837694499970219359521299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3891796333313479573014199 5837694499970219359521299)
          ·
            refine ⟨8756541749955329039281949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5837694499970219359521299 8756541749955329039281949)
            ·
              refine ⟨3283703156233248389730731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8756541749955329039281949 3283703156233248389730731)
              ·
                refine ⟨4925554734349872584596097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283703156233248389730731 4925554734349872584596097)
                ·
                  refine ⟨3694166050762404438447073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4925554734349872584596097 3694166050762404438447073)
                  ·
                    refine ⟨2770624538071803328835305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3694166050762404438447073 2770624538071803328835305)
                    ·
                      refine ⟨2077968403553852496626479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2770624538071803328835305 2077968403553852496626479)
                      ·
                        rfl

theorem cell23_4046829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4046829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046829 prefixEnd_4046829 := by exact prefixLift 4046829
  have htrace : WordTrace (prefixWord ++ tailWord_4046829) baseStart_4046829 baseEnd_4046829 := by
    simpa [prefixWord, tailWord_4046829, baseEnd_4046829] using wordTrace_append hprefix tailTrace_4046829
  have hstable : (prefixWord ++ tailWord_4046829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046829).length < 2 ^ (prefixWord ++ tailWord_4046829).sum := by decide
  have hdescent : baseEnd_4046829 < baseStart_4046829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046852 : List Nat := [2, 3, 2, 4, 2, 1, 1, 3, 5]
def baseStart_4046852 : Nat := 118140960795 + 4046852 * 2 ^ 59
def prefixEnd_4046852 : Nat := 4983230072969 + 3 ^ 40 * 4046852 * 2
def baseEnd_4046852 : Nat := 230886690400989545182097

theorem tailTrace_4046852 : CollatzResearch.WordTrace tailWord_4046852 prefixEnd_4046852 230886690400989545182097 := by
  unfold tailWord_4046852
  simp only [CollatzResearch.WordTrace]
  refine ⟨73800409167476913070831405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98400545556635884094441873 73800409167476913070831405)
  ·
    refine ⟨27675153437803842401561777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73800409167476913070831405 27675153437803842401561777)
    ·
      refine ⟨20756365078352881801171333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27675153437803842401561777 20756365078352881801171333)
      ·
        refine ⟨3891818452191165337719625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20756365078352881801171333 3891818452191165337719625)
        ·
          refine ⟨2918863839143374003289719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3891818452191165337719625 2918863839143374003289719)
          ·
            refine ⟨4378295758715061004934579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2918863839143374003289719 4378295758715061004934579)
            ·
              refine ⟨6567443638072591507401869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378295758715061004934579 6567443638072591507401869)
              ·
                refine ⟨2462791364277221815275701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6567443638072591507401869 2462791364277221815275701)
                ·
                  refine ⟨230886690400989545182097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2462791364277221815275701 230886690400989545182097)
                  ·
                    rfl

theorem cell23_4046852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_4046852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046852 prefixEnd_4046852 := by exact prefixLift 4046852
  have htrace : WordTrace (prefixWord ++ tailWord_4046852) baseStart_4046852 baseEnd_4046852 := by
    simpa [prefixWord, tailWord_4046852, baseEnd_4046852] using wordTrace_append hprefix tailTrace_4046852
  have hstable : (prefixWord ++ tailWord_4046852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046852).length < 2 ^ (prefixWord ++ tailWord_4046852).sum := by decide
  have hdescent : baseEnd_4046852 < baseStart_4046852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046874 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 8]
def baseStart_4046874 : Nat := 118140960795 + 4046874 * 2 ^ 59
def prefixEnd_4046874 : Nat := 4983230072969 + 3 ^ 40 * 4046874 * 2
def baseEnd_4046874 : Nat := 230887945575922757840419

theorem tailTrace_4046874 : CollatzResearch.WordTrace tailWord_4046874 prefixEnd_4046874 230887945575922757840419 := by
  unfold tailWord_4046874
  simp only [CollatzResearch.WordTrace]
  refine ⟨36900405185218530974740919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98401080493916082599309117 36900405185218530974740919)
  ·
    refine ⟨55350607777827796462111379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36900405185218530974740919 55350607777827796462111379)
    ·
      refine ⟨83025911666741694693167069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55350607777827796462111379 83025911666741694693167069)
      ·
        refine ⟨31134716875028135509937651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83025911666741694693167069 31134716875028135509937651)
        ·
          refine ⟨46702075312542203264906477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31134716875028135509937651 46702075312542203264906477)
          ·
            refine ⟨17513278242203326224339929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46702075312542203264906477 17513278242203326224339929)
            ·
              refine ⟨13134958681652494668254947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17513278242203326224339929 13134958681652494668254947)
              ·
                refine ⟨19702438022478742002382421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13134958681652494668254947 19702438022478742002382421)
                ·
                  refine ⟨230887945575922757840419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19702438022478742002382421 230887945575922757840419)
                  ·
                    rfl

theorem cell23_4046874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_4046874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046874 prefixEnd_4046874 := by exact prefixLift 4046874
  have htrace : WordTrace (prefixWord ++ tailWord_4046874) baseStart_4046874 baseEnd_4046874 := by
    simpa [prefixWord, tailWord_4046874, baseEnd_4046874] using wordTrace_append hprefix tailTrace_4046874
  have hstable : (prefixWord ++ tailWord_4046874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046874).length < 2 ^ (prefixWord ++ tailWord_4046874).sum := by decide
  have hdescent : baseEnd_4046874 < baseStart_4046874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046911 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 1, 5, 2]
def baseStart_4046911 : Nat := 118140960795 + 4046911 * 2 ^ 59
def prefixEnd_4046911 : Nat := 4983230072969 + 3 ^ 40 * 4046911 * 2
def baseEnd_4046911 : Nat := 2078010508967521175801101

theorem tailTrace_4046911 : CollatzResearch.WordTrace tailWord_4046911 prefixEnd_4046911 2078010508967521175801101 := by
  unfold tailWord_4046911
  simp only [CollatzResearch.WordTrace]
  refine ⟨147602970241740079218060587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98401980161160052812040391 147602970241740079218060587)
  ·
    refine ⟨221404455362610118827090881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147602970241740079218060587 221404455362610118827090881)
    ·
      refine ⟨166053341521957589120318161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221404455362610118827090881 166053341521957589120318161)
      ·
        refine ⟨124540006141468191840238621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166053341521957589120318161 124540006141468191840238621)
        ·
          refine ⟨46702502303050571940089483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124540006141468191840238621 46702502303050571940089483)
          ·
            refine ⟨70053753454575857910134225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46702502303050571940089483 70053753454575857910134225)
            ·
              refine ⟨52540315090931893432600669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70053753454575857910134225 52540315090931893432600669)
              ·
                refine ⟨19702618159099460037225251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52540315090931893432600669 19702618159099460037225251)
                ·
                  refine ⟨29553927238649190055837877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19702618159099460037225251 29553927238649190055837877)
                  ·
                    refine ⟨2770680678623361567734801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29553927238649190055837877 2770680678623361567734801)
                    ·
                      refine ⟨2078010508967521175801101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2770680678623361567734801 2078010508967521175801101)
                      ·
                        rfl

theorem cell23_4046911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 5, 2].length) (baseStart_4046911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046911 prefixEnd_4046911 := by exact prefixLift 4046911
  have htrace : WordTrace (prefixWord ++ tailWord_4046911) baseStart_4046911 baseEnd_4046911 := by
    simpa [prefixWord, tailWord_4046911, baseEnd_4046911] using wordTrace_append hprefix tailTrace_4046911
  have hstable : (prefixWord ++ tailWord_4046911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046911).length < 2 ^ (prefixWord ++ tailWord_4046911).sum := by decide
  have hdescent : baseEnd_4046911 < baseStart_4046911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046951 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 1, 6]
def baseStart_4046951 : Nat := 118140960795 + 4046951 * 2 ^ 59
def prefixEnd_4046951 : Nat := 4983230072969 + 3 ^ 40 * 4046951 * 2
def baseEnd_4046951 : Nat := 692677016064567006433639

theorem tailTrace_4046951 : CollatzResearch.WordTrace tailWord_4046951 prefixEnd_4046951 692677016064567006433639 := by
  unfold tailWord_4046951
  simp only [CollatzResearch.WordTrace]
  refine ⟨147604429161595166049516707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98402952774396777366344471 147604429161595166049516707)
  ·
    refine ⟨221406643742392749074275061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147604429161595166049516707 221406643742392749074275061)
    ·
      refine ⟨20756872850849320225713287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221406643742392749074275061 20756872850849320225713287)
      ·
        refine ⟨31135309276273980338569931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20756872850849320225713287 31135309276273980338569931)
        ·
          refine ⟨46702963914410970507854897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31135309276273980338569931 46702963914410970507854897)
          ·
            refine ⟨35027222935808227880891173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46702963914410970507854897 35027222935808227880891173)
            ·
              refine ⟨6567604300464042727667095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35027222935808227880891173 6567604300464042727667095)
              ·
                refine ⟨9851406450696064091500643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6567604300464042727667095 9851406450696064091500643)
                ·
                  refine ⟨14777109676044096137250965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9851406450696064091500643 14777109676044096137250965)
                  ·
                    refine ⟨692677016064567006433639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14777109676044096137250965 692677016064567006433639)
                    ·
                      rfl

theorem cell23_4046951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_4046951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046951 prefixEnd_4046951 := by exact prefixLift 4046951
  have htrace : WordTrace (prefixWord ++ tailWord_4046951) baseStart_4046951 baseEnd_4046951 := by
    simpa [prefixWord, tailWord_4046951, baseEnd_4046951] using wordTrace_append hprefix tailTrace_4046951
  have hstable : (prefixWord ++ tailWord_4046951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046951).length < 2 ^ (prefixWord ++ tailWord_4046951).sum := by decide
  have hdescent : baseEnd_4046951 < baseStart_4046951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046958 : List Nat := [4, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_4046958 : Nat := 118140960795 + 4046958 * 2 ^ 59
def prefixEnd_4046958 : Nat := 4983230072969 + 3 ^ 40 * 4046958 * 2
def baseEnd_4046958 : Nat := 2078034642558282491913385

theorem tailTrace_4046958 : CollatzResearch.WordTrace tailWord_4046958 prefixEnd_4046958 2078034642558282491913385 := by
  unfold tailWord_4046958
  simp only [CollatzResearch.WordTrace]
  refine ⟨18450585559071225780627691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98403122981713204163347685 18450585559071225780627691)
  ·
    refine ⟨27675878338606838670941537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18450585559071225780627691 27675878338606838670941537)
    ·
      refine ⟨20756908753955129003206153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27675878338606838670941537 20756908753955129003206153)
      ·
        refine ⟨15567681565466346752404615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20756908753955129003206153 15567681565466346752404615)
        ·
          refine ⟨23351522348199520128606923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15567681565466346752404615 23351522348199520128606923)
          ·
            refine ⟨35027283522299280192910385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23351522348199520128606923 35027283522299280192910385)
            ·
              refine ⟨26270462641724460144682789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35027283522299280192910385 26270462641724460144682789)
              ·
                refine ⟨4925711745323336277128023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26270462641724460144682789 4925711745323336277128023)
                ·
                  refine ⟨7388567617985004415692035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925711745323336277128023 7388567617985004415692035)
                  ·
                    refine ⟨11082851426977506623538053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7388567617985004415692035 11082851426977506623538053)
                    ·
                      refine ⟨2078034642558282491913385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11082851426977506623538053 2078034642558282491913385)
                      ·
                        rfl

theorem cell23_4046958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_4046958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046958 prefixEnd_4046958 := by exact prefixLift 4046958
  have htrace : WordTrace (prefixWord ++ tailWord_4046958) baseStart_4046958 baseEnd_4046958 := by
    simpa [prefixWord, tailWord_4046958, baseEnd_4046958] using wordTrace_append hprefix tailTrace_4046958
  have hstable : (prefixWord ++ tailWord_4046958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046958).length < 2 ^ (prefixWord ++ tailWord_4046958).sum := by decide
  have hdescent : baseEnd_4046958 < baseStart_4046958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4046961 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 3, 2, 3]
def baseStart_4046961 : Nat := 118140960795 + 4046961 * 2 ^ 59
def prefixEnd_4046961 : Nat := 4983230072969 + 3 ^ 40 * 4046961 * 2
def baseEnd_4046961 : Nat := 2078036183000245980175871

theorem tailTrace_4046961 : CollatzResearch.WordTrace tailWord_4046961 prefixEnd_4046961 2078036183000245980175871 := by
  unfold tailWord_4046961
  simp only [CollatzResearch.WordTrace]
  refine ⟨147604793891558937757380737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98403195927705958504920491 147604793891558937757380737)
  ·
    refine ⟨110703595418669203318035553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147604793891558937757380737 110703595418669203318035553)
    ·
      refine ⟨83027696564001902488526665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110703595418669203318035553 83027696564001902488526665)
      ·
        refine ⟨62270772423001426866394999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83027696564001902488526665 62270772423001426866394999)
        ·
          refine ⟨93406158634502140299592499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62270772423001426866394999 93406158634502140299592499)
          ·
            refine ⟨140109237951753210449388749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93406158634502140299592499 140109237951753210449388749)
            ·
              refine ⟨52540964231907453918520781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140109237951753210449388749 52540964231907453918520781)
              ·
                refine ⟨19702861586965295219445293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52540964231907453918520781 19702861586965295219445293)
                ·
                  refine ⟨7388573095111985707291985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19702861586965295219445293 7388573095111985707291985)
                  ·
                    refine ⟨5541429821333989280468989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7388573095111985707291985 5541429821333989280468989)
                    ·
                      refine ⟨2078036183000245980175871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5541429821333989280468989 2078036183000245980175871)
                      ·
                        rfl

theorem cell23_4046961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_4046961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4046961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4046961 prefixEnd_4046961 := by exact prefixLift 4046961
  have htrace : WordTrace (prefixWord ++ tailWord_4046961) baseStart_4046961 baseEnd_4046961 := by
    simpa [prefixWord, tailWord_4046961, baseEnd_4046961] using wordTrace_append hprefix tailTrace_4046961
  have hstable : (prefixWord ++ tailWord_4046961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4046961).length < 2 ^ (prefixWord ++ tailWord_4046961).sum := by decide
  have hdescent : baseEnd_4046961 < baseStart_4046961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4046961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047002 : List Nat := [3, 1, 1, 5, 2, 1, 3, 1, 2, 4]
def baseStart_4047002 : Nat := 118140960795 + 4047002 * 2 ^ 59
def prefixEnd_4047002 : Nat := 4983230072969 + 3 ^ 40 * 4047002 * 2
def baseEnd_4047002 : Nat := 692685745235693439921061

theorem tailTrace_4047002 : CollatzResearch.WordTrace tailWord_4047002 prefixEnd_4047002 692685745235693439921061 := by
  unfold tailWord_4047002
  simp only [CollatzResearch.WordTrace]
  refine ⟨36901572321102600439905815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98404192856273601173082173 36901572321102600439905815)
  ·
    refine ⟨55352358481653900659858723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36901572321102600439905815 55352358481653900659858723)
    ·
      refine ⟨83028537722480850989788085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55352358481653900659858723 83028537722480850989788085)
      ·
        refine ⟨7783925411482579780292633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83028537722480850989788085 7783925411482579780292633)
        ·
          refine ⟨5837944058611934835219475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7783925411482579780292633 5837944058611934835219475)
          ·
            refine ⟨8756916087917902252829213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5837944058611934835219475 8756916087917902252829213)
            ·
              refine ⟨3283843532969213344810955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8756916087917902252829213 3283843532969213344810955)
              ·
                refine ⟨4925765299453820017216433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283843532969213344810955 4925765299453820017216433)
                ·
                  refine ⟨3694323974590365012912325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4925765299453820017216433 3694323974590365012912325)
                  ·
                    refine ⟨692685745235693439921061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3694323974590365012912325 692685745235693439921061)
                    ·
                      rfl

theorem cell23_4047002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_4047002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047002 prefixEnd_4047002 := by exact prefixLift 4047002
  have htrace : WordTrace (prefixWord ++ tailWord_4047002) baseStart_4047002 baseEnd_4047002 := by
    simpa [prefixWord, tailWord_4047002, baseEnd_4047002] using wordTrace_append hprefix tailTrace_4047002
  have hstable : (prefixWord ++ tailWord_4047002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047002).length < 2 ^ (prefixWord ++ tailWord_4047002).sum := by decide
  have hdescent : baseEnd_4047002 < baseStart_4047002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047008 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 3]
def baseStart_4047008 : Nat := 118140960795 + 4047008 * 2 ^ 59
def prefixEnd_4047008 : Nat := 4983230072969 + 3 ^ 40 * 4047008 * 2
def baseEnd_4047008 : Nat := 2078060316591007296288155

theorem tailTrace_4047008 : CollatzResearch.WordTrace tailWord_4047008 prefixEnd_4047008 2078060316591007296288155 := by
  unfold tailWord_4047008
  simp only [CollatzResearch.WordTrace]
  refine ⟨73803254061194332392170839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98404338748259109856227785 73803254061194332392170839)
  ·
    refine ⟨110704881091791498588256259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73803254061194332392170839 110704881091791498588256259)
    ·
      refine ⟨166057321637687247882384389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110704881091791498588256259 166057321637687247882384389)
      ·
        refine ⟨31135747807066358977947073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166057321637687247882384389 31135747807066358977947073)
        ·
          refine ⟨23351810855299769233460305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31135747807066358977947073 23351810855299769233460305)
          ·
            refine ⟨17513858141474826925095229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23351810855299769233460305 17513858141474826925095229)
            ·
              refine ⟨6567696803053060096910711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17513858141474826925095229 6567696803053060096910711)
              ·
                refine ⟨9851545204579590145366067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6567696803053060096910711 9851545204579590145366067)
                ·
                  refine ⟨14777317806869385218049101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9851545204579590145366067 14777317806869385218049101)
                  ·
                    refine ⟨5541494177576019456768413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14777317806869385218049101 5541494177576019456768413)
                    ·
                      refine ⟨2078060316591007296288155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5541494177576019456768413 2078060316591007296288155)
                      ·
                        rfl

theorem cell23_4047008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_4047008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047008 prefixEnd_4047008 := by exact prefixLift 4047008
  have htrace : WordTrace (prefixWord ++ tailWord_4047008) baseStart_4047008 baseEnd_4047008 := by
    simpa [prefixWord, tailWord_4047008, baseEnd_4047008] using wordTrace_append hprefix tailTrace_4047008
  have hstable : (prefixWord ++ tailWord_4047008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047008).length < 2 ^ (prefixWord ++ tailWord_4047008).sum := by decide
  have hdescent : baseEnd_4047008 < baseStart_4047008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047015 : List Nat := [1, 1, 6, 2, 2, 2, 2, 7]
def baseStart_4047015 : Nat := 118140960795 + 4047015 * 2 ^ 59
def prefixEnd_4047015 : Nat := 4983230072969 + 3 ^ 40 * 4047015 * 2
def baseEnd_4047015 : Nat := 76965330035392176625949

theorem tailTrace_4047015 : CollatzResearch.WordTrace tailWord_4047015 prefixEnd_4047015 76965330035392176625949 := by
  unfold tailWord_4047015
  simp only [CollatzResearch.WordTrace]
  refine ⟨147606763433363304979846499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98404508955575536653230999 147606763433363304979846499)
  ·
    refine ⟨221410145150044957469769749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147606763433363304979846499 221410145150044957469769749)
    ·
      refine ⟨10378600553908357381395457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 221410145150044957469769749 10378600553908357381395457)
      ·
        refine ⟨7783950415431268036046593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10378600553908357381395457 7783950415431268036046593)
        ·
          refine ⟨5837962811573451027034945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7783950415431268036046593 5837962811573451027034945)
          ·
            refine ⟨4378472108680088270276209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5837962811573451027034945 4378472108680088270276209)
            ·
              refine ⟨3283854081510066202707157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4378472108680088270276209 3283854081510066202707157)
              ·
                refine ⟨76965330035392176625949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3283854081510066202707157 76965330035392176625949)
                ·
                  rfl

theorem cell23_4047015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 7].length) (baseStart_4047015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047015 prefixEnd_4047015 := by exact prefixLift 4047015
  have htrace : WordTrace (prefixWord ++ tailWord_4047015) baseStart_4047015 baseEnd_4047015 := by
    simpa [prefixWord, tailWord_4047015, baseEnd_4047015] using wordTrace_append hprefix tailTrace_4047015
  have hstable : (prefixWord ++ tailWord_4047015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047015).length < 2 ^ (prefixWord ++ tailWord_4047015).sum := by decide
  have hdescent : baseEnd_4047015 < baseStart_4047015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047051 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 3]
def baseStart_4047051 : Nat := 118140960795 + 4047051 * 2 ^ 59
def prefixEnd_4047051 : Nat := 4983230072969 + 3 ^ 40 * 4047051 * 2
def baseEnd_4047051 : Nat := 2078082396259150628050457

theorem tailTrace_4047051 : CollatzResearch.WordTrace tailWord_4047051 prefixEnd_4047051 2078082396259150628050457 := by
  unfold tailWord_4047051
  simp only [CollatzResearch.WordTrace]
  refine ⟨147608076461232883128157007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98405384307488588752104671 147608076461232883128157007)
  ·
    refine ⟨221412114691849324692235511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147608076461232883128157007 221412114691849324692235511)
    ·
      refine ⟨332118172037773987038353267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221412114691849324692235511 332118172037773987038353267)
      ·
        refine ⟨498177258056660980557529901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332118172037773987038353267 498177258056660980557529901)
        ·
          refine ⟨186816471771247867709073713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498177258056660980557529901 186816471771247867709073713)
          ·
            refine ⟨140112353828435900781805285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186816471771247867709073713 140112353828435900781805285)
            ·
              refine ⟨26271066342831731396588491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140112353828435900781805285 26271066342831731396588491)
              ·
                refine ⟨39406599514247597094882737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26271066342831731396588491 39406599514247597094882737)
                ·
                  refine ⟨29554949635685697821162053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39406599514247597094882737 29554949635685697821162053)
                  ·
                    refine ⟨5541553056691068341467885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29554949635685697821162053 5541553056691068341467885)
                    ·
                      refine ⟨2078082396259150628050457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5541553056691068341467885 2078082396259150628050457)
                      ·
                        rfl

theorem cell23_4047051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 3].length) (baseStart_4047051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047051 prefixEnd_4047051 := by exact prefixLift 4047051
  have htrace : WordTrace (prefixWord ++ tailWord_4047051) baseStart_4047051 baseEnd_4047051 := by
    simpa [prefixWord, tailWord_4047051, baseEnd_4047051] using wordTrace_append hprefix tailTrace_4047051
  have hstable : (prefixWord ++ tailWord_4047051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047051).length < 2 ^ (prefixWord ++ tailWord_4047051).sum := by decide
  have hdescent : baseEnd_4047051 < baseStart_4047051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047069 : List Nat := [1, 4, 3, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_4047069 : Nat := 118140960795 + 4047069 * 2 ^ 59
def prefixEnd_4047069 : Nat := 4983230072969 + 3 ^ 40 * 4047069 * 2
def baseEnd_4047069 : Nat := 2078091638910931557625375

theorem tailTrace_4047069 : CollatzResearch.WordTrace tailWord_4047069 prefixEnd_4047069 2078091638910931557625375 := by
  unfold tailWord_4047069
  simp only [CollatzResearch.WordTrace]
  refine ⟨147608732975167672202312261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98405821983445114801541507 147608732975167672202312261)
  ·
    refine ⟨27676637432843938537933549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147608732975167672202312261 27676637432843938537933549)
    ·
      refine ⟨10378739037316476951725081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27676637432843938537933549 10378739037316476951725081)
      ·
        refine ⟨7784054277987357713793811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10378739037316476951725081 7784054277987357713793811)
        ·
          refine ⟨11676081416981036570690717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7784054277987357713793811 11676081416981036570690717)
          ·
            refine ⟨4378530531367888714009019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11676081416981036570690717 4378530531367888714009019)
            ·
              refine ⟨6567795797051833071013529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378530531367888714009019 6567795797051833071013529)
              ·
                refine ⟨4925846847788874803260147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6567795797051833071013529 4925846847788874803260147)
                ·
                  refine ⟨7388770271683312204890221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925846847788874803260147 7388770271683312204890221)
                  ·
                    refine ⟨2770788851881242076833833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7388770271683312204890221 2770788851881242076833833)
                    ·
                      refine ⟨2078091638910931557625375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2770788851881242076833833 2078091638910931557625375)
                      ·
                        rfl

theorem cell23_4047069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_4047069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047069 prefixEnd_4047069 := by exact prefixLift 4047069
  have htrace : WordTrace (prefixWord ++ tailWord_4047069) baseStart_4047069 baseEnd_4047069 := by
    simpa [prefixWord, tailWord_4047069, baseEnd_4047069] using wordTrace_append hprefix tailTrace_4047069
  have hstable : (prefixWord ++ tailWord_4047069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047069).length < 2 ^ (prefixWord ++ tailWord_4047069).sum := by decide
  have hdescent : baseEnd_4047069 < baseStart_4047069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047081 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 1, 5, 3]
def baseStart_4047081 : Nat := 118140960795 + 4047081 * 2 ^ 59
def prefixEnd_4047081 : Nat := 4983230072969 + 3 ^ 40 * 4047081 * 2
def baseEnd_4047081 : Nat := 2078097800678785510675319

theorem tailTrace_4047081 : CollatzResearch.WordTrace tailWord_4047081 prefixEnd_4047081 2078097800678785510675319 := by
  unfold tailWord_4047081
  simp only [CollatzResearch.WordTrace]
  refine ⟨147609170651124198251749097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98406113767416132167832731 147609170651124198251749097)
  ·
    refine ⟨110706877988343148688811823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147609170651124198251749097 110706877988343148688811823)
    ·
      refine ⟨166060316982514723033217735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110706877988343148688811823 166060316982514723033217735)
      ·
        refine ⟨249090475473772084549826603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166060316982514723033217735 249090475473772084549826603)
        ·
          refine ⟨373635713210658126824739905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249090475473772084549826603 373635713210658126824739905)
          ·
            refine ⟨280226784907993595118554929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373635713210658126824739905 280226784907993595118554929)
            ·
              refine ⟨210170088680995196338916197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280226784907993595118554929 210170088680995196338916197)
              ·
                refine ⟨39406891627686599313546787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210170088680995196338916197 39406891627686599313546787)
                ·
                  refine ⟨59110337441529898970320181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39406891627686599313546787 59110337441529898970320181)
                  ·
                    refine ⟨5541594135143428028467517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59110337441529898970320181 5541594135143428028467517)
                    ·
                      refine ⟨2078097800678785510675319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5541594135143428028467517 2078097800678785510675319)
                      ·
                        rfl

theorem cell23_4047081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 5, 3].length) (baseStart_4047081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047081 prefixEnd_4047081 := by exact prefixLift 4047081
  have htrace : WordTrace (prefixWord ++ tailWord_4047081) baseStart_4047081 baseEnd_4047081 := by
    simpa [prefixWord, tailWord_4047081, baseEnd_4047081] using wordTrace_append hprefix tailTrace_4047081
  have hstable : (prefixWord ++ tailWord_4047081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047081).length < 2 ^ (prefixWord ++ tailWord_4047081).sum := by decide
  have hdescent : baseEnd_4047081 < baseStart_4047081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047135 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 2, 5]
def baseStart_4047135 : Nat := 118140960795 + 4047135 * 2 ^ 59
def prefixEnd_4047135 : Nat := 4983230072969 + 3 ^ 40 * 4047135 * 2
def baseEnd_4047135 : Nat := 692708509544709433133357

theorem tailTrace_4047135 : CollatzResearch.WordTrace tailWord_4047135 prefixEnd_4047135 692708509544709433133357 := by
  unfold tailWord_4047135
  simp only [CollatzResearch.WordTrace]
  refine ⟨147611140192928565474214859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98407426795285710316143239 147611140192928565474214859)
  ·
    refine ⟨221416710289392848211322289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147611140192928565474214859 221416710289392848211322289)
    ·
      refine ⟨166062532717044636158491717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221416710289392848211322289 166062532717044636158491717)
      ·
        refine ⟨31136724884445869279717197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166062532717044636158491717 31136724884445869279717197)
        ·
          refine ⟨11676271831667200979893949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31136724884445869279717197 11676271831667200979893949)
          ·
            refine ⟨4378601936875200367460231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11676271831667200979893949 4378601936875200367460231)
            ·
              refine ⟨6567902905312800551190347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378601936875200367460231 6567902905312800551190347)
              ·
                refine ⟨9851854357969200826785521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6567902905312800551190347 9851854357969200826785521)
                ·
                  refine ⟨7388890768476900620089141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9851854357969200826785521 7388890768476900620089141)
                  ·
                    refine ⟨692708509544709433133357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7388890768476900620089141 692708509544709433133357)
                    ·
                      rfl

theorem cell23_4047135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 5].length) (baseStart_4047135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047135 prefixEnd_4047135 := by exact prefixLift 4047135
  have htrace : WordTrace (prefixWord ++ tailWord_4047135) baseStart_4047135 baseEnd_4047135 := by
    simpa [prefixWord, tailWord_4047135, baseEnd_4047135] using wordTrace_append hprefix tailTrace_4047135
  have hstable : (prefixWord ++ tailWord_4047135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047135).length < 2 ^ (prefixWord ++ tailWord_4047135).sum := by decide
  have hdescent : baseEnd_4047135 < baseStart_4047135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047151 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 6]
def baseStart_4047151 : Nat := 118140960795 + 4047151 * 2 ^ 59
def prefixEnd_4047151 : Nat := 4983230072969 + 3 ^ 40 * 4047151 * 2
def baseEnd_4047151 : Nat := 2078133744324600236799997

theorem tailTrace_4047151 : CollatzResearch.WordTrace tailWord_4047151 prefixEnd_4047151 2078133744324600236799997 := by
  unfold tailWord_4047151
  simp only [CollatzResearch.WordTrace]
  refine ⟨147611723760870600206797307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98407815840580400137864871 147611723760870600206797307)
  ·
    refine ⟨221417585641305900310195961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147611723760870600206797307 221417585641305900310195961)
    ·
      refine ⟨166063189230979425232646971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221417585641305900310195961 166063189230979425232646971)
      ·
        refine ⟨249094783846469137848970457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166063189230979425232646971 249094783846469137848970457)
        ·
          refine ⟨186821087884851853386727843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249094783846469137848970457 186821087884851853386727843)
          ·
            refine ⟨280231631827277780080091765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186821087884851853386727843 280231631827277780080091765)
            ·
              refine ⟨26271715483807291882508603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280231631827277780080091765 26271715483807291882508603)
              ·
                refine ⟨39407573225710937823762905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26271715483807291882508603 39407573225710937823762905)
                ·
                  refine ⟨29555679919283203367822179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39407573225710937823762905 29555679919283203367822179)
                  ·
                    refine ⟨44333519878924805051733269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29555679919283203367822179 44333519878924805051733269)
                    ·
                      refine ⟨2078133744324600236799997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44333519878924805051733269 2078133744324600236799997)
                      ·
                        rfl

theorem cell23_4047151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_4047151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047151 prefixEnd_4047151 := by exact prefixLift 4047151
  have htrace : WordTrace (prefixWord ++ tailWord_4047151) baseStart_4047151 baseEnd_4047151 := by
    simpa [prefixWord, tailWord_4047151, baseEnd_4047151] using wordTrace_append hprefix tailTrace_4047151
  have hstable : (prefixWord ++ tailWord_4047151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047151).length < 2 ^ (prefixWord ++ tailWord_4047151).sum := by decide
  have hdescent : baseEnd_4047151 < baseStart_4047151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047242 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 3, 5]
def baseStart_4047242 : Nat := 118140960795 + 4047242 * 2 ^ 59
def prefixEnd_4047242 : Nat := 4983230072969 + 3 ^ 40 * 4047242 * 2
def baseEnd_4047242 : Nat := 692726823688053126920693

theorem tailTrace_4047242 : CollatzResearch.WordTrace tailWord_4047242 prefixEnd_4047242 692726823688053126920693 := by
  unfold tailWord_4047242
  simp only [CollatzResearch.WordTrace]
  refine ⟨36903760700885230687089995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98410028535693948498906653 36903760700885230687089995)
  ·
    refine ⟨55355641051327846030634993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36903760700885230687089995 55355641051327846030634993)
    ·
      refine ⟨41516730788495884522976245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55355641051327846030634993 41516730788495884522976245)
      ·
        refine ⟨3892193511421489174029023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41516730788495884522976245 3892193511421489174029023)
        ·
          refine ⟨5838290267132233761043535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892193511421489174029023 5838290267132233761043535)
          ·
            refine ⟨8757435400698350641565303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838290267132233761043535 8757435400698350641565303)
            ·
              refine ⟨13136153101047525962347955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8757435400698350641565303 13136153101047525962347955)
              ·
                refine ⟨19704229651571288943521933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13136153101047525962347955 19704229651571288943521933)
                ·
                  refine ⟨7389086119339233353820725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19704229651571288943521933 7389086119339233353820725)
                  ·
                    refine ⟨692726823688053126920693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7389086119339233353820725 692726823688053126920693)
                    ·
                      rfl

theorem cell23_4047242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_4047242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047242 prefixEnd_4047242 := by exact prefixLift 4047242
  have htrace : WordTrace (prefixWord ++ tailWord_4047242) baseStart_4047242 baseEnd_4047242 := by
    simpa [prefixWord, tailWord_4047242, baseEnd_4047242] using wordTrace_append hprefix tailTrace_4047242
  have hstable : (prefixWord ++ tailWord_4047242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047242).length < 2 ^ (prefixWord ++ tailWord_4047242).sum := by decide
  have hdescent : baseEnd_4047242 < baseStart_4047242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047292 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_4047292 : Nat := 118140960795 + 4047292 * 2 ^ 59
def prefixEnd_4047292 : Nat := 4983230072969 + 3 ^ 40 * 4047292 * 2
def baseEnd_4047292 : Nat := 2078206145096884185136849

theorem tailTrace_4047292 : CollatzResearch.WordTrace tailWord_4047292 prefixEnd_4047292 2078206145096884185136849 := by
  unfold tailWord_4047292
  simp only [CollatzResearch.WordTrace]
  refine ⟨73808433226679890643840065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98411244302239854191786753 73808433226679890643840065)
  ·
    refine ⟨55356324920009917982880049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73808433226679890643840065 55356324920009917982880049)
    ·
      refine ⟨41517243690007438487160037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55356324920009917982880049 41517243690007438487160037)
      ·
        refine ⟨7784483191876394716342507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41517243690007438487160037 7784483191876394716342507)
        ·
          refine ⟨11676724787814592074513761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7784483191876394716342507 11676724787814592074513761)
          ·
            refine ⟨8757543590860944055885321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11676724787814592074513761 8757543590860944055885321)
            ·
              refine ⟨6568157693145708041913991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8757543590860944055885321 6568157693145708041913991)
              ·
                refine ⟨9852236539718562062870987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6568157693145708041913991 9852236539718562062870987)
                ·
                  refine ⟨14778354809577843094306481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9852236539718562062870987 14778354809577843094306481)
                  ·
                    refine ⟨11083766107183382320729861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14778354809577843094306481 11083766107183382320729861)
                    ·
                      refine ⟨2078206145096884185136849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11083766107183382320729861 2078206145096884185136849)
                      ·
                        rfl

theorem cell23_4047292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_4047292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047292 prefixEnd_4047292 := by exact prefixLift 4047292
  have htrace : WordTrace (prefixWord ++ tailWord_4047292) baseStart_4047292 baseEnd_4047292 := by
    simpa [prefixWord, tailWord_4047292, baseEnd_4047292] using wordTrace_append hprefix tailTrace_4047292
  have hstable : (prefixWord ++ tailWord_4047292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047292).length < 2 ^ (prefixWord ++ tailWord_4047292).sum := by decide
  have hdescent : baseEnd_4047292 < baseStart_4047292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047295 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 8, 1, 3]
def baseStart_4047295 : Nat := 118140960795 + 4047295 * 2 ^ 59
def prefixEnd_4047295 : Nat := 4983230072969 + 3 ^ 40 * 4047295 * 2
def baseEnd_4047295 : Nat := 2078207685538847673399335

theorem tailTrace_4047295 : CollatzResearch.WordTrace tailWord_4047295 prefixEnd_4047295 2078207685538847673399335 := by
  unfold tailWord_4047295
  simp only [CollatzResearch.WordTrace]
  refine ⟨147616975872348912800039339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98411317248232608533359559 147616975872348912800039339)
  ·
    refine ⟨221425463808523369200059009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147616975872348912800039339 221425463808523369200059009)
    ·
      refine ⟨166069097856392526900044257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221425463808523369200059009 166069097856392526900044257)
      ·
        refine ⟨124551823392294395175033193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166069097856392526900044257 124551823392294395175033193)
        ·
          refine ⟨93413867544220796381274895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124551823392294395175033193 93413867544220796381274895)
          ·
            refine ⟨140120801316331194571912343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93413867544220796381274895 140120801316331194571912343)
            ·
              refine ⟨210181201974496791857868515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140120801316331194571912343 210181201974496791857868515)
              ·
                refine ⟨315271802961745187786802773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210181201974496791857868515 315271802961745187786802773)
                ·
                  refine ⟨3694591440957951419376595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 315271802961745187786802773 3694591440957951419376595)
                  ·
                    refine ⟨5541887161436927129064893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3694591440957951419376595 5541887161436927129064893)
                    ·
                      refine ⟨2078207685538847673399335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5541887161436927129064893 2078207685538847673399335)
                      ·
                        rfl

theorem cell23_4047295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_4047295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047295 prefixEnd_4047295 := by exact prefixLift 4047295
  have htrace : WordTrace (prefixWord ++ tailWord_4047295) baseStart_4047295 baseEnd_4047295 := by
    simpa [prefixWord, tailWord_4047295, baseEnd_4047295] using wordTrace_append hprefix tailTrace_4047295
  have hstable : (prefixWord ++ tailWord_4047295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047295).length < 2 ^ (prefixWord ++ tailWord_4047295).sum := by decide
  have hdescent : baseEnd_4047295 < baseStart_4047295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047316 : List Nat := [2, 4, 1, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_4047316 : Nat := 118140960795 + 4047316 * 2 ^ 59
def prefixEnd_4047316 : Nat := 4983230072969 + 3 ^ 40 * 4047316 * 2
def baseEnd_4047316 : Nat := 2078218468632592091236739

theorem tailTrace_4047316 : CollatzResearch.WordTrace tailWord_4047316 prefixEnd_4047316 2078218468632592091236739 := by
  unfold tailWord_4047316
  simp only [CollatzResearch.WordTrace]
  refine ⟨73808870902636416693276901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98411827870181888924369201 73808870902636416693276901)
  ·
    refine ⟨13839163294244328129989419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73808870902636416693276901 13839163294244328129989419)
    ·
      refine ⟨20758744941366492194984129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13839163294244328129989419 20758744941366492194984129)
      ·
        refine ⟨15569058706024869146238097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20758744941366492194984129 15569058706024869146238097)
        ·
          refine ⟨11676794029518651859678573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15569058706024869146238097 11676794029518651859678573)
          ·
            refine ⟨4378797761069494447379465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11676794029518651859678573 4378797761069494447379465)
            ·
              refine ⟨3284098320802120835534599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4378797761069494447379465 3284098320802120835534599)
              ·
                refine ⟨4926147481203181253301899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284098320802120835534599 4926147481203181253301899)
                ·
                  refine ⟨7389221221804771879952849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926147481203181253301899 7389221221804771879952849)
                  ·
                    refine ⟨5541915916353578909964637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7389221221804771879952849 5541915916353578909964637)
                    ·
                      refine ⟨2078218468632592091236739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5541915916353578909964637 2078218468632592091236739)
                      ·
                        rfl

theorem cell23_4047316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_4047316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047316 prefixEnd_4047316 := by exact prefixLift 4047316
  have htrace : WordTrace (prefixWord ++ tailWord_4047316) baseStart_4047316 baseEnd_4047316 := by
    simpa [prefixWord, tailWord_4047316, baseEnd_4047316] using wordTrace_append hprefix tailTrace_4047316
  have hstable : (prefixWord ++ tailWord_4047316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047316).length < 2 ^ (prefixWord ++ tailWord_4047316).sum := by decide
  have hdescent : baseEnd_4047316 < baseStart_4047316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047328 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 4, 6]
def baseStart_4047328 : Nat := 118140960795 + 4047328 * 2 ^ 59
def prefixEnd_4047328 : Nat := 4983230072969 + 3 ^ 40 * 4047328 * 2
def baseEnd_4047328 : Nat := 692741543466815348095561

theorem tailTrace_4047328 : CollatzResearch.WordTrace tailWord_4047328 prefixEnd_4047328 692741543466815348095561 := by
  unfold tailWord_4047328
  simp only [CollatzResearch.WordTrace]
  refine ⟨73809089740614679717995319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98412119654152906290660425 73809089740614679717995319)
  ·
    refine ⟨110713634610922019576992979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73809089740614679717995319 110713634610922019576992979)
    ·
      refine ⟨166070451916383029365489469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110713634610922019576992979 166070451916383029365489469)
      ·
        refine ⟨62276419468643636012058551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166070451916383029365489469 62276419468643636012058551)
        ·
          refine ⟨93414629202965454018087827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62276419468643636012058551 93414629202965454018087827)
          ·
            refine ⟨140121943804448181027131741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93414629202965454018087827 140121943804448181027131741)
            ·
              refine ⟨52545728926668067885174403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140121943804448181027131741 52545728926668067885174403)
              ·
                refine ⟨78818593390002101827761605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52545728926668067885174403 78818593390002101827761605)
                ·
                  refine ⟨14778486260625394092705301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78818593390002101827761605 14778486260625394092705301)
                  ·
                    refine ⟨692741543466815348095561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14778486260625394092705301 692741543466815348095561)
                    ·
                      rfl

theorem cell23_4047328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_4047328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047328 prefixEnd_4047328 := by exact prefixLift 4047328
  have htrace : WordTrace (prefixWord ++ tailWord_4047328) baseStart_4047328 baseEnd_4047328 := by
    simpa [prefixWord, tailWord_4047328, baseEnd_4047328] using wordTrace_append hprefix tailTrace_4047328
  have hstable : (prefixWord ++ tailWord_4047328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047328).length < 2 ^ (prefixWord ++ tailWord_4047328).sum := by decide
  have hdescent : baseEnd_4047328 < baseStart_4047328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047346 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 1, 3, 3]
def baseStart_4047346 : Nat := 118140960795 + 4047346 * 2 ^ 59
def prefixEnd_4047346 : Nat := 4983230072969 + 3 ^ 40 * 4047346 * 2
def baseEnd_4047346 : Nat := 2078233873052226973861601

theorem tailTrace_4047346 : CollatzResearch.WordTrace tailWord_4047346 prefixEnd_4047346 2078233873052226973861601 := by
  unfold tailWord_4047346
  simp only [CollatzResearch.WordTrace]
  refine ⟨36904708998791037127536473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98412557330109432340097261 36904708998791037127536473)
  ·
    refine ⟨27678531749093277845652355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36904708998791037127536473 27678531749093277845652355)
    ·
      refine ⟨41517797623639916768478533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27678531749093277845652355 41517797623639916768478533)
      ·
        refine ⟨7784587054432484394089725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41517797623639916768478533 7784587054432484394089725)
        ·
          refine ⟨2919220145412181647783647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7784587054432484394089725 2919220145412181647783647)
          ·
            refine ⟨4378830218118272471675471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919220145412181647783647 4378830218118272471675471)
            ·
              refine ⟨6568245327177408707513207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378830218118272471675471 6568245327177408707513207)
              ·
                refine ⟨9852367990766113061269811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6568245327177408707513207 9852367990766113061269811)
                ·
                  refine ⟨14778551986149169591904717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9852367990766113061269811 14778551986149169591904717)
                  ·
                    refine ⟨5541956994805938596964269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14778551986149169591904717 5541956994805938596964269)
                    ·
                      refine ⟨2078233873052226973861601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5541956994805938596964269 2078233873052226973861601)
                      ·
                        rfl

theorem cell23_4047346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_4047346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047346 prefixEnd_4047346 := by exact prefixLift 4047346
  have htrace : WordTrace (prefixWord ++ tailWord_4047346) baseStart_4047346 baseEnd_4047346 := by
    simpa [prefixWord, tailWord_4047346, baseEnd_4047346] using wordTrace_append hprefix tailTrace_4047346
  have hstable : (prefixWord ++ tailWord_4047346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047346).length < 2 ^ (prefixWord ++ tailWord_4047346).sum := by decide
  have hdescent : baseEnd_4047346 < baseStart_4047346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047373 : List Nat := [1, 7, 1, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_4047373 : Nat := 118140960795 + 4047373 * 2 ^ 59
def prefixEnd_4047373 : Nat := 4983230072969 + 3 ^ 40 * 4047373 * 2
def baseEnd_4047373 : Nat := 2078247737029898368223977

theorem tailTrace_4047373 : CollatzResearch.WordTrace tailWord_4047373 prefixEnd_4047373 2078247737029898368223977 := by
  unfold tailWord_4047373
  simp only [CollatzResearch.WordTrace]
  refine ⟨147619820766066332121378773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98413213844044221414252515 147619820766066332121378773)
  ·
    refine ⟨3459839549204679659094815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 147619820766066332121378773 3459839549204679659094815)
    ·
      refine ⟨5189759323807019488642223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3459839549204679659094815 5189759323807019488642223)
      ·
        refine ⟨7784638985710529232963335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5189759323807019488642223 7784638985710529232963335)
        ·
          refine ⟨11676958478565793849445003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7784638985710529232963335 11676958478565793849445003)
          ·
            refine ⟨17515437717848690774167505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11676958478565793849445003 17515437717848690774167505)
            ·
              refine ⟨13136578288386518080625629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17515437717848690774167505 13136578288386518080625629)
              ·
                refine ⟨4926216858144944280234611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13136578288386518080625629 4926216858144944280234611)
                ·
                  refine ⟨7389325287217416420351917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926216858144944280234611 7389325287217416420351917)
                  ·
                    refine ⟨2770996982706531157631969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7389325287217416420351917 2770996982706531157631969)
                    ·
                      refine ⟨2078247737029898368223977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2770996982706531157631969 2078247737029898368223977)
                      ·
                        rfl

theorem cell23_4047373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_4047373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047373 prefixEnd_4047373 := by exact prefixLift 4047373
  have htrace : WordTrace (prefixWord ++ tailWord_4047373) baseStart_4047373 baseEnd_4047373 := by
    simpa [prefixWord, tailWord_4047373, baseEnd_4047373] using wordTrace_append hprefix tailTrace_4047373
  have hstable : (prefixWord ++ tailWord_4047373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047373).length < 2 ^ (prefixWord ++ tailWord_4047373).sum := by decide
  have hdescent : baseEnd_4047373 < baseStart_4047373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047442 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_4047442 : Nat := 118140960795 + 4047442 * 2 ^ 59
def prefixEnd_4047442 : Nat := 4983230072969 + 3 ^ 40 * 4047442 * 2
def baseEnd_4047442 : Nat := 2078283167195058598261159

theorem tailTrace_4047442 : CollatzResearch.WordTrace tailWord_4047442 prefixEnd_4047442 2078283167195058598261159 := by
  unfold tailWord_4047442
  simp only [CollatzResearch.WordTrace]
  refine ⟨36905584350704089226410145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98414891601877571270427053 36905584350704089226410145)
  ·
    refine ⟨27679188263028066919807609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36905584350704089226410145 27679188263028066919807609)
    ·
      refine ⟨20759391197271050189855707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27679188263028066919807609 20759391197271050189855707)
      ·
        refine ⟨31139086795906575284783561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20759391197271050189855707 31139086795906575284783561)
        ·
          refine ⟨23354315096929931463587671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31139086795906575284783561 23354315096929931463587671)
          ·
            refine ⟨35031472645394897195381507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23354315096929931463587671 35031472645394897195381507)
            ·
              refine ⟨52547208968092345793072261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35031472645394897195381507 52547208968092345793072261)
              ·
                refine ⟨9852601681517314836201049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52547208968092345793072261 9852601681517314836201049)
                ·
                  refine ⟨7389451261137986127150787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9852601681517314836201049 7389451261137986127150787)
                  ·
                    refine ⟨11084176891706979190726181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7389451261137986127150787 11084176891706979190726181)
                    ·
                      refine ⟨2078283167195058598261159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11084176891706979190726181 2078283167195058598261159)
                      ·
                        rfl

theorem cell23_4047442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_4047442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047442 prefixEnd_4047442 := by exact prefixLift 4047442
  have htrace : WordTrace (prefixWord ++ tailWord_4047442) baseStart_4047442 baseEnd_4047442 := by
    simpa [prefixWord, tailWord_4047442, baseEnd_4047442] using wordTrace_append hprefix tailTrace_4047442
  have hstable : (prefixWord ++ tailWord_4047442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047442).length < 2 ^ (prefixWord ++ tailWord_4047442).sum := by decide
  have hdescent : baseEnd_4047442 < baseStart_4047442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047469 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_4047469 : Nat := 118140960795 + 4047469 * 2 ^ 59
def prefixEnd_4047469 : Nat := 4983230072969 + 3 ^ 40 * 4047469 * 2
def baseEnd_4047469 : Nat := 692765677057576664207845

theorem tailTrace_4047469 : CollatzResearch.WordTrace tailWord_4047469 prefixEnd_4047469 692765677057576664207845 := by
  unfold tailWord_4047469
  simp only [CollatzResearch.WordTrace]
  refine ⟨147623322173718540516873461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98415548115812360344582307 147623322173718540516873461)
  ·
    refine ⟨13839686453786113173456887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147623322173718540516873461 13839686453786113173456887)
    ·
      refine ⟨20759529680679169760185331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13839686453786113173456887 20759529680679169760185331)
      ·
        refine ⟨31139294521018754640277997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20759529680679169760185331 31139294521018754640277997)
        ·
          refine ⟨11677235445382032990104249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31139294521018754640277997 11677235445382032990104249)
          ·
            refine ⟨8757926584036524742578187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11677235445382032990104249 8757926584036524742578187)
            ·
              refine ⟨13136889876054787113867281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8757926584036524742578187 13136889876054787113867281)
              ·
                refine ⟨9852667407041090335400461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13136889876054787113867281 9852667407041090335400461)
                ·
                  refine ⟨3694750277640408875775173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9852667407041090335400461 3694750277640408875775173)
                  ·
                    refine ⟨692765677057576664207845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3694750277640408875775173 692765677057576664207845)
                    ·
                      rfl

theorem cell23_4047469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_4047469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047469 prefixEnd_4047469 := by exact prefixLift 4047469
  have htrace : WordTrace (prefixWord ++ tailWord_4047469) baseStart_4047469 baseEnd_4047469 := by
    simpa [prefixWord, tailWord_4047469, baseEnd_4047469] using wordTrace_append hprefix tailTrace_4047469
  have hstable : (prefixWord ++ tailWord_4047469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047469).length < 2 ^ (prefixWord ++ tailWord_4047469).sum := by decide
  have hdescent : baseEnd_4047469 < baseStart_4047469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047475 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 3]
def baseStart_4047475 : Nat := 118140960795 + 4047475 * 2 ^ 59
def prefixEnd_4047475 : Nat := 4983230072969 + 3 ^ 40 * 4047475 * 2
def baseEnd_4047475 : Nat := 2078300112056656969148507

theorem tailTrace_4047475 : CollatzResearch.WordTrace tailWord_4047475 prefixEnd_4047475 2078300112056656969148507 := by
  unfold tailWord_4047475
  simp only [CollatzResearch.WordTrace]
  refine ⟨147623541011696803541591879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98415694007797869027727919 147623541011696803541591879)
  ·
    refine ⟨221435311517545205312387819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147623541011696803541591879 221435311517545205312387819)
    ·
      refine ⟨332152967276317807968581729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221435311517545205312387819 332152967276317807968581729)
      ·
        refine ⟨249114725457238355976436297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332152967276317807968581729 249114725457238355976436297)
        ·
          refine ⟨186836044092928766982327223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249114725457238355976436297 186836044092928766982327223)
          ·
            refine ⟨280254066139393150473490835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186836044092928766982327223 280254066139393150473490835)
            ·
              refine ⟨420381099209089725710236253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280254066139393150473490835 420381099209089725710236253)
              ·
                refine ⟨157642912203408647141338595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420381099209089725710236253 157642912203408647141338595)
                ·
                  refine ⟨236464368305112970712007893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157642912203408647141338595 236464368305112970712007893)
                  ·
                    refine ⟨5542133632151085251062685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 236464368305112970712007893 5542133632151085251062685)
                    ·
                      refine ⟨2078300112056656969148507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5542133632151085251062685 2078300112056656969148507)
                      ·
                        rfl

theorem cell23_4047475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 3].length) (baseStart_4047475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047475 prefixEnd_4047475 := by exact prefixLift 4047475
  have htrace : WordTrace (prefixWord ++ tailWord_4047475) baseStart_4047475 baseEnd_4047475 := by
    simpa [prefixWord, tailWord_4047475, baseEnd_4047475] using wordTrace_append hprefix tailTrace_4047475
  have hstable : (prefixWord ++ tailWord_4047475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047475).length < 2 ^ (prefixWord ++ tailWord_4047475).sum := by decide
  have hdescent : baseEnd_4047475 < baseStart_4047475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047549 : List Nat := [1, 4, 1, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_4047549 : Nat := 118140960795 + 4047549 * 2 ^ 59
def prefixEnd_4047549 : Nat := 4983230072969 + 3 ^ 40 * 4047549 * 2
def baseEnd_4047549 : Nat := 2078338109625089679623167

theorem tailTrace_4047549 : CollatzResearch.WordTrace tailWord_4047549 prefixEnd_4047549 2078338109625089679623167 := by
  unfold tailWord_4047549
  simp only [CollatzResearch.WordTrace]
  refine ⟨147626240013428714179785701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98417493342285809453190467 147626240013428714179785701)
  ·
    refine ⟨27679920002517883908709819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147626240013428714179785701 27679920002517883908709819)
    ·
      refine ⟨41519880003776825863064729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27679920002517883908709819 41519880003776825863064729)
      ·
        refine ⟨31139910002832619397298547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41519880003776825863064729 31139910002832619397298547)
        ·
          refine ⟨46709865004248929095947821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31139910002832619397298547 46709865004248929095947821)
          ·
            refine ⟨17516199376593348410980433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46709865004248929095947821 17516199376593348410980433)
            ·
              refine ⟨13137149532445011308235325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17516199376593348410980433 13137149532445011308235325)
              ·
                refine ⟨4926431074666879240588247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13137149532445011308235325 4926431074666879240588247)
                ·
                  refine ⟨7389646612000318860882371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926431074666879240588247 7389646612000318860882371)
                  ·
                    refine ⟨11084469918000478291323557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7389646612000318860882371 11084469918000478291323557)
                    ·
                      refine ⟨2078338109625089679623167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11084469918000478291323557 2078338109625089679623167)
                      ·
                        rfl

theorem cell23_4047549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_4047549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047549 prefixEnd_4047549 := by exact prefixLift 4047549
  have htrace : WordTrace (prefixWord ++ tailWord_4047549) baseStart_4047549 baseEnd_4047549 := by
    simpa [prefixWord, tailWord_4047549, baseEnd_4047549] using wordTrace_append hprefix tailTrace_4047549
  have hstable : (prefixWord ++ tailWord_4047549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047549).length < 2 ^ (prefixWord ++ tailWord_4047549).sum := by decide
  have hdescent : baseEnd_4047549 < baseStart_4047549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047552 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 5]
def baseStart_4047552 : Nat := 118140960795 + 4047552 * 2 ^ 59
def prefixEnd_4047552 : Nat := 4983230072969 + 3 ^ 40 * 4047552 * 2
def baseEnd_4047552 : Nat := 2078339650067053167885653

theorem tailTrace_4047552 : CollatzResearch.WordTrace tailWord_4047552 prefixEnd_4047552 2078339650067053167885653 := by
  unfold tailWord_4047552
  simp only [CollatzResearch.WordTrace]
  refine ⟨73813174716208922846072455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98417566288278563794763273 73813174716208922846072455)
  ·
    refine ⟨110719762074313384269108683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73813174716208922846072455 110719762074313384269108683)
    ·
      refine ⟨166079643111470076403663025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110719762074313384269108683 166079643111470076403663025)
      ·
        refine ⟨124559732333602557302747269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166079643111470076403663025 124559732333602557302747269)
        ·
          refine ⟨23354949812550479494265113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124559732333602557302747269 23354949812550479494265113)
          ·
            refine ⟨17516212359412859620698835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23354949812550479494265113 17516212359412859620698835)
            ·
              refine ⟨26274318539119289431048253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17516212359412859620698835 26274318539119289431048253)
              ·
                refine ⟨9852869452169733536643095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26274318539119289431048253 9852869452169733536643095)
                ·
                  refine ⟨14779304178254600304964643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9852869452169733536643095 14779304178254600304964643)
                  ·
                    refine ⟨22168956267381900457446965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14779304178254600304964643 22168956267381900457446965)
                    ·
                      refine ⟨2078339650067053167885653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22168956267381900457446965 2078339650067053167885653)
                      ·
                        rfl

theorem cell23_4047552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_4047552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047552 prefixEnd_4047552 := by exact prefixLift 4047552
  have htrace : WordTrace (prefixWord ++ tailWord_4047552) baseStart_4047552 baseEnd_4047552 := by
    simpa [prefixWord, tailWord_4047552, baseEnd_4047552] using wordTrace_append hprefix tailTrace_4047552
  have hstable : (prefixWord ++ tailWord_4047552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047552).length < 2 ^ (prefixWord ++ tailWord_4047552).sum := by decide
  have hdescent : baseEnd_4047552 < baseStart_4047552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047562 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_4047562 : Nat := 118140960795 + 4047562 * 2 ^ 59
def prefixEnd_4047562 : Nat := 4983230072969 + 3 ^ 40 * 4047562 * 2
def baseEnd_4047562 : Nat := 2078344784873598128760607

theorem tailTrace_4047562 : CollatzResearch.WordTrace tailWord_4047562 prefixEnd_4047562 2078344784873598128760607 := by
  unfold tailWord_4047562
  simp only [CollatzResearch.WordTrace]
  refine ⟨36906678540595404350002235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98417809441587744933339293 36906678540595404350002235)
  ·
    refine ⟨55360017810893106525003353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36906678540595404350002235 55360017810893106525003353)
    ·
      refine ⟨41520013358169829893752515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55360017810893106525003353 41520013358169829893752515)
      ·
        refine ⟨62280020037254744840628773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41520013358169829893752515 62280020037254744840628773)
        ·
          refine ⟨11677503756985264657617895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62280020037254744840628773 11677503756985264657617895)
          ·
            refine ⟨17516255635477896986426843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11677503756985264657617895 17516255635477896986426843)
            ·
              refine ⟨26274383453216845479640265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17516255635477896986426843 26274383453216845479640265)
              ·
                refine ⟨19705787589912634109730199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26274383453216845479640265 19705787589912634109730199)
                ·
                  refine ⟨29558681384868951164595299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19705787589912634109730199 29558681384868951164595299)
                  ·
                    refine ⟨44338022077303426746892949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29558681384868951164595299 44338022077303426746892949)
                    ·
                      refine ⟨2078344784873598128760607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44338022077303426746892949 2078344784873598128760607)
                      ·
                        rfl

theorem cell23_4047562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_4047562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047562 prefixEnd_4047562 := by exact prefixLift 4047562
  have htrace : WordTrace (prefixWord ++ tailWord_4047562) baseStart_4047562 baseEnd_4047562 := by
    simpa [prefixWord, tailWord_4047562, baseEnd_4047562] using wordTrace_append hprefix tailTrace_4047562
  have hstable : (prefixWord ++ tailWord_4047562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047562).length < 2 ^ (prefixWord ++ tailWord_4047562).sum := by decide
  have hdescent : baseEnd_4047562 < baseStart_4047562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047576 : List Nat := [2, 1, 2, 2, 3, 2, 4, 1, 2, 4]
def baseStart_4047576 : Nat := 118140960795 + 4047576 * 2 ^ 59
def prefixEnd_4047576 : Nat := 4983230072969 + 3 ^ 40 * 4047576 * 2
def baseEnd_4047576 : Nat := 692783991200920357995181

theorem tailTrace_4047576 : CollatzResearch.WordTrace tailWord_4047576 prefixEnd_4047576 692783991200920357995181 := by
  unfold tailWord_4047576
  simp only [CollatzResearch.WordTrace]
  refine ⟨73813612392165448895509291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98418149856220598527345721 73813612392165448895509291)
  ·
    refine ⟨110720418588248173343263937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73813612392165448895509291 110720418588248173343263937)
    ·
      refine ⟨83040313941186130007447953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110720418588248173343263937 83040313941186130007447953)
      ·
        refine ⟨62280235455889597505585965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83040313941186130007447953 62280235455889597505585965)
        ·
          refine ⟨23355088295958599064594737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62280235455889597505585965 23355088295958599064594737)
          ·
            refine ⟨17516316221968949298446053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23355088295958599064594737 17516316221968949298446053)
            ·
              refine ⟨3284309291619177993458635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17516316221968949298446053 3284309291619177993458635)
              ·
                refine ⟨4926463937428766990187953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284309291619177993458635 4926463937428766990187953)
                ·
                  refine ⟨3694847953071575242640965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4926463937428766990187953 3694847953071575242640965)
                  ·
                    refine ⟨692783991200920357995181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3694847953071575242640965 692783991200920357995181)
                    ·
                      rfl

theorem cell23_4047576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_4047576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047576 prefixEnd_4047576 := by exact prefixLift 4047576
  have htrace : WordTrace (prefixWord ++ tailWord_4047576) baseStart_4047576 baseEnd_4047576 := by
    simpa [prefixWord, tailWord_4047576, baseEnd_4047576] using wordTrace_append hprefix tailTrace_4047576
  have hstable : (prefixWord ++ tailWord_4047576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047576).length < 2 ^ (prefixWord ++ tailWord_4047576).sum := by decide
  have hdescent : baseEnd_4047576 < baseStart_4047576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047599 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 3]
def baseStart_4047599 : Nat := 118140960795 + 4047599 * 2 ^ 59
def prefixEnd_4047599 : Nat := 4983230072969 + 3 ^ 40 * 4047599 * 2
def baseEnd_4047599 : Nat := 2078363783657814483997937

theorem tailTrace_4047599 : CollatzResearch.WordTrace tailWord_4047599 prefixEnd_4047599 2078363783657814483997937 := by
  unfold tailWord_4047599
  simp only [CollatzResearch.WordTrace]
  refine ⟨147628063663247572719105851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98418709108831715146070567 147628063663247572719105851)
  ·
    refine ⟨221442095494871359078658777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147628063663247572719105851 221442095494871359078658777)
    ·
      refine ⟨166081571621153519308994083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221442095494871359078658777 166081571621153519308994083)
      ·
        refine ⟨249122357431730278963491125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166081571621153519308994083 249122357431730278963491125)
        ·
          refine ⟨23355221009224713652827293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249122357431730278963491125 23355221009224713652827293)
          ·
            refine ⟨8758207878459267619810235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23355221009224713652827293 8758207878459267619810235)
            ·
              refine ⟨13137311817688901429715353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8758207878459267619810235 13137311817688901429715353)
              ·
                refine ⟨9852983863266676072286515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13137311817688901429715353 9852983863266676072286515)
                ·
                  refine ⟨14779475794900014108429773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9852983863266676072286515 14779475794900014108429773)
                  ·
                    refine ⟨5542303423087505290661165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14779475794900014108429773 5542303423087505290661165)
                    ·
                      refine ⟨2078363783657814483997937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5542303423087505290661165 2078363783657814483997937)
                      ·
                        rfl

theorem cell23_4047599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 3].length) (baseStart_4047599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047599 prefixEnd_4047599 := by exact prefixLift 4047599
  have htrace : WordTrace (prefixWord ++ tailWord_4047599) baseStart_4047599 baseEnd_4047599 := by
    simpa [prefixWord, tailWord_4047599, baseEnd_4047599] using wordTrace_append hprefix tailTrace_4047599
  have hstable : (prefixWord ++ tailWord_4047599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047599).length < 2 ^ (prefixWord ++ tailWord_4047599).sum := by decide
  have hdescent : baseEnd_4047599 < baseStart_4047599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047656 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_4047656 : Nat := 118140960795 + 4047656 * 2 ^ 59
def prefixEnd_4047656 : Nat := 4983230072969 + 3 ^ 40 * 4047656 * 2
def baseEnd_4047656 : Nat := 2078393052055120760985175

theorem tailTrace_4047656 : CollatzResearch.WordTrace tailWord_4047656 prefixEnd_4047656 2078393052055120760985175 := by
  unfold tailWord_4047656
  simp only [CollatzResearch.WordTrace]
  refine ⟨73815071312020535726965411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98420095082694047635953881 73815071312020535726965411)
  ·
    refine ⟨110722606968030803590448117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73815071312020535726965411 110722606968030803590448117)
    ·
      refine ⟨10380244403252887836604511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110722606968030803590448117 10380244403252887836604511)
      ·
        refine ⟨15570366604879331754906767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10380244403252887836604511 15570366604879331754906767)
        ·
          refine ⟨23355549907318997632360151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15570366604879331754906767 23355549907318997632360151)
          ·
            refine ⟨35033324860978496448540227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23355549907318997632360151 35033324860978496448540227)
            ·
              refine ⟨52549987291467744672810341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35033324860978496448540227 52549987291467744672810341)
              ·
                refine ⟨9853122617150202126151939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52549987291467744672810341 9853122617150202126151939)
                ·
                  refine ⟨14779683925725303189227909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9853122617150202126151939 14779683925725303189227909)
                  ·
                    refine ⟨2771190736073494347980233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14779683925725303189227909 2771190736073494347980233)
                    ·
                      refine ⟨2078393052055120760985175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2771190736073494347980233 2078393052055120760985175)
                      ·
                        rfl

theorem cell23_4047656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_4047656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047656 prefixEnd_4047656 := by exact prefixLift 4047656
  have htrace : WordTrace (prefixWord ++ tailWord_4047656) baseStart_4047656 baseEnd_4047656 := by
    simpa [prefixWord, tailWord_4047656, baseEnd_4047656] using wordTrace_append hprefix tailTrace_4047656
  have hstable : (prefixWord ++ tailWord_4047656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047656).length < 2 ^ (prefixWord ++ tailWord_4047656).sum := by decide
  have hdescent : baseEnd_4047656 < baseStart_4047656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047669 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_4047669 : Nat := 118140960795 + 4047669 * 2 ^ 59
def prefixEnd_4047669 : Nat := 4983230072969 + 3 ^ 40 * 4047669 * 2
def baseEnd_4047669 : Nat := 2078399727303629210122615

theorem tailTrace_4047669 : CollatzResearch.WordTrace tailWord_4047669 prefixEnd_4047669 2078399727303629210122615 := by
  unfold tailWord_4047669
  simp only [CollatzResearch.WordTrace]
  refine ⟨147630616772993974674154061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98420411181995983116102707 147630616772993974674154061)
  ·
    refine ⟨55361481289872740502807773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147630616772993974674154061 55361481289872740502807773)
    ·
      refine ⟨20760555483702277688552915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55361481289872740502807773 20760555483702277688552915)
      ·
        refine ⟨31140833225553416532829373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20760555483702277688552915 31140833225553416532829373)
        ·
          refine ⟨11677812459582531199811015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31140833225553416532829373 11677812459582531199811015)
          ·
            refine ⟨17516718689373796799716523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11677812459582531199811015 17516718689373796799716523)
            ·
              refine ⟨26275078034060695199574785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17516718689373796799716523 26275078034060695199574785)
              ·
                refine ⟨19706308525545521399681089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26275078034060695199574785 19706308525545521399681089)
                ·
                  refine ⟨14779731394159141049760817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19706308525545521399681089 14779731394159141049760817)
                  ·
                    refine ⟨11084798545619355787320613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14779731394159141049760817 11084798545619355787320613)
                    ·
                      refine ⟨2078399727303629210122615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11084798545619355787320613 2078399727303629210122615)
                      ·
                        rfl

theorem cell23_4047669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_4047669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047669 prefixEnd_4047669 := by exact prefixLift 4047669
  have htrace : WordTrace (prefixWord ++ tailWord_4047669) baseStart_4047669 baseEnd_4047669 := by
    simpa [prefixWord, tailWord_4047669, baseEnd_4047669] using wordTrace_append hprefix tailTrace_4047669
  have hstable : (prefixWord ++ tailWord_4047669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047669).length < 2 ^ (prefixWord ++ tailWord_4047669).sum := by decide
  have hdescent : baseEnd_4047669 < baseStart_4047669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047679 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 7]
def baseStart_4047679 : Nat := 118140960795 + 4047679 * 2 ^ 59
def prefixEnd_4047679 : Nat := 4983230072969 + 3 ^ 40 * 4047679 * 2
def baseEnd_4047679 : Nat := 230933873567797130110841

theorem tailTrace_4047679 : CollatzResearch.WordTrace tailWord_4047679 prefixEnd_4047679 230933873567797130110841 := by
  unfold tailWord_4047679
  simp only [CollatzResearch.WordTrace]
  refine ⟨147630981502957746382018091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98420654335305164254678727 147630981502957746382018091)
  ·
    refine ⟨221446472254436619573027137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147630981502957746382018091 221446472254436619573027137)
    ·
      refine ⟨166084854190827464679770353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221446472254436619573027137 166084854190827464679770353)
      ·
        refine ⟨124563640643120598509827765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166084854190827464679770353 124563640643120598509827765)
        ·
          refine ⟨11677841310292556110296353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124563640643120598509827765 11677841310292556110296353)
          ·
            refine ⟨8758380982719417082722265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11677841310292556110296353 8758380982719417082722265)
            ·
              refine ⟨6568785737039562812041699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8758380982719417082722265 6568785737039562812041699)
              ·
                refine ⟨9853178605559344218062549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6568785737039562812041699 9853178605559344218062549)
                ·
                  refine ⟨230933873567797130110841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9853178605559344218062549 230933873567797130110841)
                  ·
                    rfl

theorem cell23_4047679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 7].length) (baseStart_4047679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047679 prefixEnd_4047679 := by exact prefixLift 4047679
  have htrace : WordTrace (prefixWord ++ tailWord_4047679) baseStart_4047679 baseEnd_4047679 := by
    simpa [prefixWord, tailWord_4047679, baseEnd_4047679] using wordTrace_append hprefix tailTrace_4047679
  have hstable : (prefixWord ++ tailWord_4047679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047679).length < 2 ^ (prefixWord ++ tailWord_4047679).sum := by decide
  have hdescent : baseEnd_4047679 < baseStart_4047679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047689 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 2, 3, 3]
def baseStart_4047689 : Nat := 118140960795 + 4047689 * 2 ^ 59
def prefixEnd_4047689 : Nat := 4983230072969 + 3 ^ 40 * 4047689 * 2
def baseEnd_4047689 : Nat := 2078409996916719131872523

theorem tailTrace_4047689 : CollatzResearch.WordTrace tailWord_4047689 prefixEnd_4047689 2078409996916719131872523 := by
  unfold tailWord_4047689
  simp only [CollatzResearch.WordTrace]
  refine ⟨147631346232921518089882121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98420897488614345393254747 147631346232921518089882121)
  ·
    refine ⟨110723509674691138567411591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147631346232921518089882121 110723509674691138567411591)
    ·
      refine ⟨166085264512036707851117387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110723509674691138567411591 166085264512036707851117387)
      ·
        refine ⟨249127896768055061776676081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166085264512036707851117387 249127896768055061776676081)
        ·
          refine ⟨186845922576041296332507061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249127896768055061776676081 186845922576041296332507061)
          ·
            refine ⟨17516805241503871531172537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186845922576041296332507061 17516805241503871531172537)
            ·
              refine ⟨13137603931127903648379403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17516805241503871531172537 13137603931127903648379403)
              ·
                refine ⟨19706405896691855472569105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13137603931127903648379403 19706405896691855472569105)
                ·
                  refine ⟨14779804422518891604426829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19706405896691855472569105 14779804422518891604426829)
                  ·
                    refine ⟨5542426658444584351660061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14779804422518891604426829 5542426658444584351660061)
                    ·
                      refine ⟨2078409996916719131872523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5542426658444584351660061 2078409996916719131872523)
                      ·
                        rfl

theorem cell23_4047689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 3, 3].length) (baseStart_4047689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047689 prefixEnd_4047689 := by exact prefixLift 4047689
  have htrace : WordTrace (prefixWord ++ tailWord_4047689) baseStart_4047689 baseEnd_4047689 := by
    simpa [prefixWord, tailWord_4047689, baseEnd_4047689] using wordTrace_append hprefix tailTrace_4047689
  have hstable : (prefixWord ++ tailWord_4047689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047689).length < 2 ^ (prefixWord ++ tailWord_4047689).sum := by decide
  have hdescent : baseEnd_4047689 < baseStart_4047689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047699 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 2, 5, 2]
def baseStart_4047699 : Nat := 118140960795 + 4047699 * 2 ^ 59
def prefixEnd_4047699 : Nat := 4983230072969 + 3 ^ 40 * 4047699 * 2
def baseEnd_4047699 : Nat := 2078415131723264092747477

theorem tailTrace_4047699 : CollatzResearch.WordTrace tailWord_4047699 prefixEnd_4047699 2078415131723264092747477 := by
  unfold tailWord_4047699
  simp only [CollatzResearch.WordTrace]
  refine ⟨147631710962885289797746151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98421140641923526531830767 147631710962885289797746151)
  ·
    refine ⟨221447566444327934696619227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147631710962885289797746151 221447566444327934696619227)
    ·
      refine ⟨332171349666491902044928841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221447566444327934696619227 332171349666491902044928841)
      ·
        refine ⟨249128512249868926533696631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332171349666491902044928841 249128512249868926533696631)
        ·
          refine ⟨373692768374803389800544947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249128512249868926533696631 373692768374803389800544947)
          ·
            refine ⟨560539152562205084700817421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373692768374803389800544947 560539152562205084700817421)
            ·
              refine ⟨210202182210826906762806533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 560539152562205084700817421 210202182210826906762806533)
              ·
                refine ⟨39412909164530045018026225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210202182210826906762806533 39412909164530045018026225)
                ·
                  refine ⟨29559681873397533763519669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39412909164530045018026225 29559681873397533763519669)
                  ·
                    refine ⟨2771220175631018790329969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29559681873397533763519669 2771220175631018790329969)
                    ·
                      refine ⟨2078415131723264092747477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2771220175631018790329969 2078415131723264092747477)
                      ·
                        rfl

theorem cell23_4047699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 5, 2].length) (baseStart_4047699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047699 prefixEnd_4047699 := by exact prefixLift 4047699
  have htrace : WordTrace (prefixWord ++ tailWord_4047699) baseStart_4047699 baseEnd_4047699 := by
    simpa [prefixWord, tailWord_4047699, baseEnd_4047699] using wordTrace_append hprefix tailTrace_4047699
  have hstable : (prefixWord ++ tailWord_4047699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047699).length < 2 ^ (prefixWord ++ tailWord_4047699).sum := by decide
  have hdescent : baseEnd_4047699 < baseStart_4047699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047729 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_4047729 : Nat := 118140960795 + 4047729 * 2 ^ 59
def prefixEnd_4047729 : Nat := 4983230072969 + 3 ^ 40 * 4047729 * 2
def baseEnd_4047729 : Nat := 2078430536142898975372339

theorem tailTrace_4047729 : CollatzResearch.WordTrace tailWord_4047729 prefixEnd_4047729 2078430536142898975372339 := by
  unfold tailWord_4047729
  simp only [CollatzResearch.WordTrace]
  refine ⟨147632805152776604921338241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98421870101851069947558827 147632805152776604921338241)
  ·
    refine ⟨110724603864582453691003681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147632805152776604921338241 110724603864582453691003681)
    ·
      refine ⟨83043452898436840268252761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110724603864582453691003681 83043452898436840268252761)
      ·
        refine ⟨62282589673827630201189571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83043452898436840268252761 62282589673827630201189571)
        ·
          refine ⟨93423884510741445301784357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62282589673827630201189571 93423884510741445301784357)
          ·
            refine ⟨17516978345764020994084567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93423884510741445301784357 17516978345764020994084567)
            ·
              refine ⟨26275467518646031491126851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17516978345764020994084567 26275467518646031491126851)
              ·
                refine ⟨39413201277969047236690277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26275467518646031491126851 39413201277969047236690277)
                ·
                  refine ⟨7389975239619196356879427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39413201277969047236690277 7389975239619196356879427)
                  ·
                    refine ⟨11084962859428794535319141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7389975239619196356879427 11084962859428794535319141)
                    ·
                      refine ⟨2078430536142898975372339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11084962859428794535319141 2078430536142898975372339)
                      ·
                        rfl

theorem cell23_4047729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_4047729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047729 prefixEnd_4047729 := by exact prefixLift 4047729
  have htrace : WordTrace (prefixWord ++ tailWord_4047729) baseStart_4047729 baseEnd_4047729 := by
    simpa [prefixWord, tailWord_4047729, baseEnd_4047729] using wordTrace_append hprefix tailTrace_4047729
  have hstable : (prefixWord ++ tailWord_4047729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047729).length < 2 ^ (prefixWord ++ tailWord_4047729).sum := by decide
  have hdescent : baseEnd_4047729 < baseStart_4047729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047773 : List Nat := [1, 4, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_4047773 : Nat := 118140960795 + 4047773 * 2 ^ 59
def prefixEnd_4047773 : Nat := 4983230072969 + 3 ^ 40 * 4047773 * 2
def baseEnd_4047773 : Nat := 692817709763898934407379

theorem tailTrace_4047773 : CollatzResearch.WordTrace tailWord_4047773 prefixEnd_4047773 692817709763898934407379 := by
  unfold tailWord_4047773
  simp only [CollatzResearch.WordTrace]
  refine ⟨147634409964617200435939973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98422939976411466957293315 147634409964617200435939973)
  ·
    refine ⟨27681451868365725081738745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147634409964617200435939973 27681451868365725081738745)
    ·
      refine ⟨20761088901274293811304059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27681451868365725081738745 20761088901274293811304059)
      ·
        refine ⟨31141633351911440716956089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20761088901274293811304059 31141633351911440716956089)
        ·
          refine ⟨23356225013933580537717067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31141633351911440716956089 23356225013933580537717067)
          ·
            refine ⟨35034337520900370806575601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23356225013933580537717067 35034337520900370806575601)
            ·
              refine ⟨26275753140675278104931701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35034337520900370806575601 26275753140675278104931701)
              ·
                refine ⟨2463351856938307322337347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26275753140675278104931701 2463351856938307322337347)
                ·
                  refine ⟨3695027785407460983506021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463351856938307322337347 3695027785407460983506021)
                  ·
                    refine ⟨692817709763898934407379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3695027785407460983506021 692817709763898934407379)
                    ·
                      rfl

theorem cell23_4047773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_4047773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047773 prefixEnd_4047773 := by exact prefixLift 4047773
  have htrace : WordTrace (prefixWord ++ tailWord_4047773) baseStart_4047773 baseEnd_4047773 := by
    simpa [prefixWord, tailWord_4047773, baseEnd_4047773] using wordTrace_append hprefix tailTrace_4047773
  have hstable : (prefixWord ++ tailWord_4047773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047773).length < 2 ^ (prefixWord ++ tailWord_4047773).sum := by decide
  have hdescent : baseEnd_4047773 < baseStart_4047773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047799 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 3, 5]
def baseStart_4047799 : Nat := 118140960795 + 4047799 * 2 ^ 59
def prefixEnd_4047799 : Nat := 4983230072969 + 3 ^ 40 * 4047799 * 2
def baseEnd_4047799 : Nat := 692822159929571233832339

theorem tailTrace_4047799 : CollatzResearch.WordTrace tailWord_4047799 prefixEnd_4047799 692822159929571233832339 := by
  unfold tailWord_4047799
  simp only [CollatzResearch.WordTrace]
  refine ⟨147635358262523006876386451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98423572175015337917590967 147635358262523006876386451)
  ·
    refine ⟨221453037393784510314579677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147635358262523006876386451 221453037393784510314579677)
    ·
      refine ⟨83044889022669191367967379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221453037393784510314579677 83044889022669191367967379)
      ·
        refine ⟨124567333534003787051951069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83044889022669191367967379 124567333534003787051951069)
        ·
          refine ⟨46712750075251420144481651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124567333534003787051951069 46712750075251420144481651)
          ·
            refine ⟨70069125112877130216722477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46712750075251420144481651 70069125112877130216722477)
            ·
              refine ⟨26275921917328923831270929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70069125112877130216722477 26275921917328923831270929)
              ·
                refine ⟨19706941437996692873453197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26275921917328923831270929 19706941437996692873453197)
                ·
                  refine ⟨7390103039248759827544949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19706941437996692873453197 7390103039248759827544949)
                  ·
                    refine ⟨692822159929571233832339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7390103039248759827544949 692822159929571233832339)
                    ·
                      rfl

theorem cell23_4047799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_4047799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047799 prefixEnd_4047799 := by exact prefixLift 4047799
  have htrace : WordTrace (prefixWord ++ tailWord_4047799) baseStart_4047799 baseEnd_4047799 := by
    simpa [prefixWord, tailWord_4047799, baseEnd_4047799] using wordTrace_append hprefix tailTrace_4047799
  have hstable : (prefixWord ++ tailWord_4047799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047799).length < 2 ^ (prefixWord ++ tailWord_4047799).sum := by decide
  have hdescent : baseEnd_4047799 < baseStart_4047799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047823 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 2, 3, 2]
def baseStart_4047823 : Nat := 118140960795 + 4047823 * 2 ^ 59
def prefixEnd_4047823 : Nat := 4983230072969 + 3 ^ 40 * 4047823 * 2
def baseEnd_4047823 : Nat := 2078478803324421607596907

theorem tailTrace_4047823 : CollatzResearch.WordTrace tailWord_4047823 prefixEnd_4047823 2078478803324421607596907 := by
  unfold tailWord_4047823
  simp only [CollatzResearch.WordTrace]
  refine ⟨147636233614436058975260123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98424155742957372650173415 147636233614436058975260123)
  ·
    refine ⟨221454350421654088462890185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147636233614436058975260123 221454350421654088462890185)
    ·
      refine ⟨166090762816240566347167639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221454350421654088462890185 166090762816240566347167639)
      ·
        refine ⟨249136144224360849520751459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166090762816240566347167639 249136144224360849520751459)
        ·
          refine ⟨373704216336541274281127189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249136144224360849520751459 373704216336541274281127189)
          ·
            refine ⟨17517385140775372231927837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 373704216336541274281127189 17517385140775372231927837)
            ·
              refine ⟨6569019427790764586972939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17517385140775372231927837 6569019427790764586972939)
              ·
                refine ⟨9853529141686146880459409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6569019427790764586972939 9853529141686146880459409)
                ·
                  refine ⟨7390146856264610160344557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9853529141686146880459409 7390146856264610160344557)
                  ·
                    refine ⟨2771305071099228810129209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7390146856264610160344557 2771305071099228810129209)
                    ·
                      refine ⟨2078478803324421607596907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2771305071099228810129209 2078478803324421607596907)
                      ·
                        rfl

theorem cell23_4047823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 3, 2].length) (baseStart_4047823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047823 prefixEnd_4047823 := by exact prefixLift 4047823
  have htrace : WordTrace (prefixWord ++ tailWord_4047823) baseStart_4047823 baseEnd_4047823 := by
    simpa [prefixWord, tailWord_4047823, baseEnd_4047823] using wordTrace_append hprefix tailTrace_4047823
  have hstable : (prefixWord ++ tailWord_4047823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047823).length < 2 ^ (prefixWord ++ tailWord_4047823).sum := by decide
  have hdescent : baseEnd_4047823 < baseStart_4047823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047833 : List Nat := [1, 2, 1, 2, 5, 1, 4, 1, 1, 5]
def baseStart_4047833 : Nat := 118140960795 + 4047833 * 2 ^ 59
def prefixEnd_4047833 : Nat := 4983230072969 + 3 ^ 40 * 4047833 * 2
def baseEnd_4047833 : Nat := 692827979376988856157287

theorem tailTrace_4047833 : CollatzResearch.WordTrace tailWord_4047833 prefixEnd_4047833 692827979376988856157287 := by
  unfold tailWord_4047833
  simp only [CollatzResearch.WordTrace]
  refine ⟨147636598344399830683124153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98424398896266553788749435 147636598344399830683124153)
  ·
    refine ⟨110727448758299873012343115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147636598344399830683124153 110727448758299873012343115)
    ·
      refine ⟨166091173137449809518514673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110727448758299873012343115 166091173137449809518514673)
      ·
        refine ⟨124568379853087357138886005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166091173137449809518514673 124568379853087357138886005)
        ·
          refine ⟨11678285611226939731770563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124568379853087357138886005 11678285611226939731770563)
          ·
            refine ⟨17517428416840409597655845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11678285611226939731770563 17517428416840409597655845)
            ·
              refine ⟨3284517828157576799560471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17517428416840409597655845 3284517828157576799560471)
              ·
                refine ⟨4926776742236365199340707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284517828157576799560471 4926776742236365199340707)
                ·
                  refine ⟨7390165113354547799011061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926776742236365199340707 7390165113354547799011061)
                  ·
                    refine ⟨692827979376988856157287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7390165113354547799011061 692827979376988856157287)
                    ·
                      rfl

theorem cell23_4047833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 1, 5].length) (baseStart_4047833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047833 prefixEnd_4047833 := by exact prefixLift 4047833
  have htrace : WordTrace (prefixWord ++ tailWord_4047833) baseStart_4047833 baseEnd_4047833 := by
    simpa [prefixWord, tailWord_4047833, baseEnd_4047833] using wordTrace_append hprefix tailTrace_4047833
  have hstable : (prefixWord ++ tailWord_4047833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047833).length < 2 ^ (prefixWord ++ tailWord_4047833).sum := by decide
  have hdescent : baseEnd_4047833 < baseStart_4047833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047873 : List Nat := [1, 2, 4, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_4047873 : Nat := 118140960795 + 4047873 * 2 ^ 59
def prefixEnd_4047873 : Nat := 4983230072969 + 3 ^ 40 * 4047873 * 2
def baseEnd_4047873 : Nat := 2078504477357146411971677

theorem tailTrace_4047873 : CollatzResearch.WordTrace tailWord_4047873 prefixEnd_4047873 2078504477357146411971677 := by
  unfold tailWord_4047873
  simp only [CollatzResearch.WordTrace]
  refine ⟨147638057264254917514580273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98425371509503278343053515 147638057264254917514580273)
  ·
    refine ⟨110728542948191188135935205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147638057264254917514580273 110728542948191188135935205)
    ·
      refine ⟨20761601802785847775487851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110728542948191188135935205 20761601802785847775487851)
      ·
        refine ⟨31142402704178771663231777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20761601802785847775487851 31142402704178771663231777)
        ·
          refine ⟨23356802028134078747423833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31142402704178771663231777 23356802028134078747423833)
          ·
            refine ⟨17517601521100559060567875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23356802028134078747423833 17517601521100559060567875)
            ·
              refine ⟨26276402281650838590851813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17517601521100559060567875 26276402281650838590851813)
              ·
                refine ⟨4926825427809532235784715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26276402281650838590851813 4926825427809532235784715)
                ·
                  refine ⟨7390238141714298353677073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926825427809532235784715 7390238141714298353677073)
                  ·
                    refine ⟨5542678606285723765257805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7390238141714298353677073 5542678606285723765257805)
                    ·
                      refine ⟨2078504477357146411971677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5542678606285723765257805 2078504477357146411971677)
                      ·
                        rfl

theorem cell23_4047873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_4047873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047873 prefixEnd_4047873 := by exact prefixLift 4047873
  have htrace : WordTrace (prefixWord ++ tailWord_4047873) baseStart_4047873 baseEnd_4047873 := by
    simpa [prefixWord, tailWord_4047873, baseEnd_4047873] using wordTrace_append hprefix tailTrace_4047873
  have hstable : (prefixWord ++ tailWord_4047873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047873).length < 2 ^ (prefixWord ++ tailWord_4047873).sum := by decide
  have hdescent : baseEnd_4047873 < baseStart_4047873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047903 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 4, 1, 3]
def baseStart_4047903 : Nat := 118140960795 + 4047903 * 2 ^ 59
def prefixEnd_4047903 : Nat := 4983230072969 + 3 ^ 40 * 4047903 * 2
def baseEnd_4047903 : Nat := 2078519881776781294596539

theorem tailTrace_4047903 : CollatzResearch.WordTrace tailWord_4047903 prefixEnd_4047903 2078519881776781294596539 := by
  unfold tailWord_4047903
  simp only [CollatzResearch.WordTrace]
  refine ⟨147639151454146232638172363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98426100969430821758781575 147639151454146232638172363)
  ·
    refine ⟨221458727181219348957258545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147639151454146232638172363 221458727181219348957258545)
    ·
      refine ⟨166094045385914511717943909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221458727181219348957258545 166094045385914511717943909)
      ·
        refine ⟨31142633509858970947114483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166094045385914511717943909 31142633509858970947114483)
        ·
          refine ⟨46713950264788456420671725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31142633509858970947114483 46713950264788456420671725)
          ·
            refine ⟨17517731349295671157751897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46713950264788456420671725 17517731349295671157751897)
            ·
              refine ⟨13138298511971753368313923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17517731349295671157751897 13138298511971753368313923)
              ·
                refine ⟨19707447767957630052470885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13138298511971753368313923 19707447767957630052470885)
                ·
                  refine ⟨3695146456492055634838291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19707447767957630052470885 3695146456492055634838291)
                  ·
                    refine ⟨5542719684738083452257437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3695146456492055634838291 5542719684738083452257437)
                    ·
                      refine ⟨2078519881776781294596539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5542719684738083452257437 2078519881776781294596539)
                      ·
                        rfl

theorem cell23_4047903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_4047903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047903 prefixEnd_4047903 := by exact prefixLift 4047903
  have htrace : WordTrace (prefixWord ++ tailWord_4047903) baseStart_4047903 baseEnd_4047903 := by
    simpa [prefixWord, tailWord_4047903, baseEnd_4047903] using wordTrace_append hprefix tailTrace_4047903
  have hstable : (prefixWord ++ tailWord_4047903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047903).length < 2 ^ (prefixWord ++ tailWord_4047903).sum := by decide
  have hdescent : baseEnd_4047903 < baseStart_4047903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047904 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4047904 : Nat := 118140960795 + 4047904 * 2 ^ 59
def prefixEnd_4047904 : Nat := 4983230072969 + 3 ^ 40 * 4047904 * 2
def baseEnd_4047904 : Nat := 2078520395257435790684035

theorem tailTrace_4047904 : CollatzResearch.WordTrace tailWord_4047904 prefixEnd_4047904 2078520395257435790684035 := by
  unfold tailWord_4047904
  simp only [CollatzResearch.WordTrace]
  refine ⟨73819593963571304904479383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98426125284761739872639177 73819593963571304904479383)
  ·
    refine ⟨110729390945356957356719075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73819593963571304904479383 110729390945356957356719075)
    ·
      refine ⟨166094086418035436035078613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110729390945356957356719075 166094086418035436035078613)
      ·
        refine ⟨3892830150422705532072155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 166094086418035436035078613 3892830150422705532072155)
        ·
          refine ⟨5839245225634058298108233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892830150422705532072155 5839245225634058298108233)
          ·
            refine ⟨4379433919225543723581175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5839245225634058298108233 4379433919225543723581175)
            ·
              refine ⟨6569150878838315585371763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379433919225543723581175 6569150878838315585371763)
              ·
                refine ⟨9853726318257473378057645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6569150878838315585371763 9853726318257473378057645)
                ·
                  refine ⟨3695147369346552516771617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9853726318257473378057645 3695147369346552516771617)
                  ·
                    refine ⟨2771360527009914387578713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3695147369346552516771617 2771360527009914387578713)
                    ·
                      refine ⟨2078520395257435790684035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2771360527009914387578713 2078520395257435790684035)
                      ·
                        rfl

theorem cell23_4047904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4047904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047904 prefixEnd_4047904 := by exact prefixLift 4047904
  have htrace : WordTrace (prefixWord ++ tailWord_4047904) baseStart_4047904 baseEnd_4047904 := by
    simpa [prefixWord, tailWord_4047904, baseEnd_4047904] using wordTrace_append hprefix tailTrace_4047904
  have hstable : (prefixWord ++ tailWord_4047904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047904).length < 2 ^ (prefixWord ++ tailWord_4047904).sum := by decide
  have hdescent : baseEnd_4047904 < baseStart_4047904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047914 : List Nat := [3, 1, 4, 1, 4, 1, 2, 1, 2, 4]
def baseStart_4047914 : Nat := 118140960795 + 4047914 * 2 ^ 59
def prefixEnd_4047914 : Nat := 4983230072969 + 3 ^ 40 * 4047914 * 2
def baseEnd_4047914 : Nat := 692841843354660250519663

theorem tailTrace_4047914 : CollatzResearch.WordTrace tailWord_4047914 prefixEnd_4047914 692841843354660250519663 := by
  unfold tailWord_4047914
  simp only [CollatzResearch.WordTrace]
  refine ⟨36909888164276595379205699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98426368438070921011215197 36909888164276595379205699)
  ·
    refine ⟨55364832246414893068808549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36909888164276595379205699 55364832246414893068808549)
    ·
      refine ⟨10380906046202792450401603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55364832246414893068808549 10380906046202792450401603)
      ·
        refine ⟨15571359069304188675602405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10380906046202792450401603 15571359069304188675602405)
        ·
          refine ⟨2919629825494535376675451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15571359069304188675602405 2919629825494535376675451)
          ·
            refine ⟨4379444738241803065013177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919629825494535376675451 4379444738241803065013177)
            ·
              refine ⟨3284583553681352298759883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4379444738241803065013177 3284583553681352298759883)
              ·
                refine ⟨4926875330522028448139825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284583553681352298759883 4926875330522028448139825)
                ·
                  refine ⟨3695156497891521336104869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4926875330522028448139825 3695156497891521336104869)
                  ·
                    refine ⟨692841843354660250519663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3695156497891521336104869 692841843354660250519663)
                    ·
                      rfl

theorem cell23_4047914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_4047914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047914 prefixEnd_4047914 := by exact prefixLift 4047914
  have htrace : WordTrace (prefixWord ++ tailWord_4047914) baseStart_4047914 baseEnd_4047914 := by
    simpa [prefixWord, tailWord_4047914, baseEnd_4047914] using wordTrace_append hprefix tailTrace_4047914
  have hstable : (prefixWord ++ tailWord_4047914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047914).length < 2 ^ (prefixWord ++ tailWord_4047914).sum := by decide
  have hdescent : baseEnd_4047914 < baseStart_4047914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047919 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 6, 6]
def baseStart_4047919 : Nat := 118140960795 + 4047919 * 2 ^ 59
def prefixEnd_4047919 : Nat := 4983230072969 + 3 ^ 40 * 4047919 * 2
def baseEnd_4047919 : Nat := 692842699155751077332155

theorem tailTrace_4047919 : CollatzResearch.WordTrace tailWord_4047919 prefixEnd_4047919 692842699155751077332155 := by
  unfold tailWord_4047919
  simp only [CollatzResearch.WordTrace]
  refine ⟨147639735022088267370754811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98426490014725511580503207 147639735022088267370754811)
  ·
    refine ⟨221459602533132401056132217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147639735022088267370754811 221459602533132401056132217)
    ·
      refine ⟨166094701899849300792099163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221459602533132401056132217 166094701899849300792099163)
      ·
        refine ⟨249142052849773951188148745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166094701899849300792099163 249142052849773951188148745)
        ·
          refine ⟨186856539637330463391111559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249142052849773951188148745 186856539637330463391111559)
          ·
            refine ⟨280284809455995695086667339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186856539637330463391111559 280284809455995695086667339)
            ·
              refine ⟨420427214183993542630001009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280284809455995695086667339 420427214183993542630001009)
              ·
                refine ⟨315320410637995156972500757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420427214183993542630001009 315320410637995156972500757)
                ·
                  refine ⟨14780644248656022983085973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 315320410637995156972500757 14780644248656022983085973)
                  ·
                    refine ⟨692842699155751077332155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14780644248656022983085973 692842699155751077332155)
                    ·
                      rfl

theorem cell23_4047919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_4047919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047919 prefixEnd_4047919 := by exact prefixLift 4047919
  have htrace : WordTrace (prefixWord ++ tailWord_4047919) baseStart_4047919 baseEnd_4047919 := by
    simpa [prefixWord, tailWord_4047919, baseEnd_4047919] using wordTrace_append hprefix tailTrace_4047919
  have hstable : (prefixWord ++ tailWord_4047919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047919).length < 2 ^ (prefixWord ++ tailWord_4047919).sum := by decide
  have hdescent : baseEnd_4047919 < baseStart_4047919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047930 : List Nat := [3, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2]
def baseStart_4047930 : Nat := 118140960795 + 4047930 * 2 ^ 59
def prefixEnd_4047930 : Nat := 4983230072969 + 3 ^ 40 * 4047930 * 2
def baseEnd_4047930 : Nat := 2078533745754452688958915

theorem tailTrace_4047930 : CollatzResearch.WordTrace tailWord_4047930 prefixEnd_4047930 2078533745754452688958915 := by
  unfold tailWord_4047930
  simp only [CollatzResearch.WordTrace]
  refine ⟨36910034056262104062351311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98426757483365610832936829 36910034056262104062351311)
  ·
    refine ⟨55365051084393156093526967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36910034056262104062351311 55365051084393156093526967)
    ·
      refine ⟨83047576626589734140290451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55365051084393156093526967 83047576626589734140290451)
      ·
        refine ⟨124571364939884601210435677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83047576626589734140290451 124571364939884601210435677)
        ·
          refine ⟨46714261852456725453913379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124571364939884601210435677 46714261852456725453913379)
          ·
            refine ⟨70071392778685088180870069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46714261852456725453913379 70071392778685088180870069)
            ·
              refine ⟨6569193073001727016956569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70071392778685088180870069 6569193073001727016956569)
              ·
                refine ⟨4926894804751295262717427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6569193073001727016956569 4926894804751295262717427)
                ·
                  refine ⟨7390342207126942894076141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926894804751295262717427 7390342207126942894076141)
                  ·
                    refine ⟨2771378327672603585278553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7390342207126942894076141 2771378327672603585278553)
                    ·
                      refine ⟨2078533745754452688958915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2771378327672603585278553 2078533745754452688958915)
                      ·
                        rfl

theorem cell23_4047930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2].length) (baseStart_4047930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047930 prefixEnd_4047930 := by exact prefixLift 4047930
  have htrace : WordTrace (prefixWord ++ tailWord_4047930) baseStart_4047930 baseEnd_4047930 := by
    simpa [prefixWord, tailWord_4047930, baseEnd_4047930] using wordTrace_append hprefix tailTrace_4047930
  have hstable : (prefixWord ++ tailWord_4047930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047930).length < 2 ^ (prefixWord ++ tailWord_4047930).sum := by decide
  have hdescent : baseEnd_4047930 < baseStart_4047930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047943 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 3, 4, 2]
def baseStart_4047943 : Nat := 118140960795 + 4047943 * 2 ^ 59
def prefixEnd_4047943 : Nat := 4983230072969 + 3 ^ 40 * 4047943 * 2
def baseEnd_4047943 : Nat := 2078540421002961138096355

theorem tailTrace_4047943 : CollatzResearch.WordTrace tailWord_4047943 prefixEnd_4047943 2078540421002961138096355 := by
  unfold tailWord_4047943
  simp only [CollatzResearch.WordTrace]
  refine ⟨147640610374001319469628483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98427073582667546313085655 147640610374001319469628483)
  ·
    refine ⟨221460915561001979204442725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147640610374001319469628483 221460915561001979204442725)
    ·
      refine ⟨41523921667687871100833011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221460915561001979204442725 41523921667687871100833011)
      ·
        refine ⟨62285882501531806651249517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41523921667687871100833011 62285882501531806651249517)
        ·
          refine ⟨23357205938074427494218569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62285882501531806651249517 23357205938074427494218569)
          ·
            refine ⟨17517904453555820620663927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23357205938074427494218569 17517904453555820620663927)
            ·
              refine ⟨26276856680333730930995891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17517904453555820620663927 26276856680333730930995891)
              ·
                refine ⟨39415285020500596396493837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26276856680333730930995891 39415285020500596396493837)
                ·
                  refine ⟨14780731882687723648685189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39415285020500596396493837 14780731882687723648685189)
                  ·
                    refine ⟨2771387228003948184128473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14780731882687723648685189 2771387228003948184128473)
                    ·
                      refine ⟨2078540421002961138096355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2771387228003948184128473 2078540421002961138096355)
                      ·
                        rfl

theorem cell23_4047943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_4047943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047943 prefixEnd_4047943 := by exact prefixLift 4047943
  have htrace : WordTrace (prefixWord ++ tailWord_4047943) baseStart_4047943 baseEnd_4047943 := by
    simpa [prefixWord, tailWord_4047943, baseEnd_4047943] using wordTrace_append hprefix tailTrace_4047943
  have hstable : (prefixWord ++ tailWord_4047943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047943).length < 2 ^ (prefixWord ++ tailWord_4047943).sum := by decide
  have hdescent : baseEnd_4047943 < baseStart_4047943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047946 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_4047946 : Nat := 118140960795 + 4047946 * 2 ^ 59
def prefixEnd_4047946 : Nat := 4983230072969 + 3 ^ 40 * 4047946 * 2
def baseEnd_4047946 : Nat := 2078541961444924626358841

theorem tailTrace_4047946 : CollatzResearch.WordTrace tailWord_4047946 prefixEnd_4047946 2078541961444924626358841 := by
  unfold tailWord_4047946
  simp only [CollatzResearch.WordTrace]
  refine ⟨36910179948247612745496923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98427146528660300654658461 36910179948247612745496923)
  ·
    refine ⟨55365269922371419118245385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36910179948247612745496923 55365269922371419118245385)
    ·
      refine ⟨41523952441778564338684039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55365269922371419118245385 41523952441778564338684039)
      ·
        refine ⟨62285928662667846508026059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41523952441778564338684039 62285928662667846508026059)
        ·
          refine ⟨93428892994001769762039089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62285928662667846508026059 93428892994001769762039089)
          ·
            refine ⟨70071669745501327321529317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93428892994001769762039089 70071669745501327321529317)
            ·
              refine ⟨13138438077281498872786747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70071669745501327321529317 13138438077281498872786747)
              ·
                refine ⟨19707657115922248309180121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13138438077281498872786747 19707657115922248309180121)
                ·
                  refine ⟨14780742836941686231885091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19707657115922248309180121 14780742836941686231885091)
                  ·
                    refine ⟨22171114255412529347827637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14780742836941686231885091 22171114255412529347827637)
                    ·
                      refine ⟨2078541961444924626358841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22171114255412529347827637 2078541961444924626358841)
                      ·
                        rfl

theorem cell23_4047946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_4047946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047946 prefixEnd_4047946 := by exact prefixLift 4047946
  have htrace : WordTrace (prefixWord ++ tailWord_4047946) baseStart_4047946 baseEnd_4047946 := by
    simpa [prefixWord, tailWord_4047946, baseEnd_4047946] using wordTrace_append hprefix tailTrace_4047946
  have hstable : (prefixWord ++ tailWord_4047946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047946).length < 2 ^ (prefixWord ++ tailWord_4047946).sum := by decide
  have hdescent : baseEnd_4047946 < baseStart_4047946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047996 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 1, 7]
def baseStart_4047996 : Nat := 118140960795 + 4047996 * 2 ^ 59
def prefixEnd_4047996 : Nat := 4983230072969 + 3 ^ 40 * 4047996 * 2
def baseEnd_4047996 : Nat := 692855878492549810244537

theorem tailTrace_4047996 : CollatzResearch.WordTrace tailWord_4047996 prefixEnd_4047996 692855878492549810244537 := by
  unfold tailWord_4047996
  simp only [CollatzResearch.WordTrace]
  refine ⟨73821271721404654760653921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98428362295206206347538561 73821271721404654760653921)
  ·
    refine ⟨55365953791053491070490441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73821271721404654760653921 55365953791053491070490441)
    ·
      refine ⟨41524465343290118302867831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55365953791053491070490441 41524465343290118302867831)
      ·
        refine ⟨62286698014935177454301747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41524465343290118302867831 62286698014935177454301747)
        ·
          refine ⟨93430047022402766181452621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62286698014935177454301747 93430047022402766181452621)
          ·
            refine ⟨35036267633401037318044733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93430047022402766181452621 35036267633401037318044733)
            ·
              refine ⟨13138600362525388994266775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35036267633401037318044733 13138600362525388994266775)
              ·
                refine ⟨19707900543788083491400163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13138600362525388994266775 19707900543788083491400163)
                ·
                  refine ⟨29561850815682125237100245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19707900543788083491400163 29561850815682125237100245)
                  ·
                    refine ⟨692855878492549810244537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29561850815682125237100245 692855878492549810244537)
                    ·
                      rfl

theorem cell23_4047996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_4047996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4047996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4047996 prefixEnd_4047996 := by exact prefixLift 4047996
  have htrace : WordTrace (prefixWord ++ tailWord_4047996) baseStart_4047996 baseEnd_4047996 := by
    simpa [prefixWord, tailWord_4047996, baseEnd_4047996] using wordTrace_append hprefix tailTrace_4047996
  have hstable : (prefixWord ++ tailWord_4047996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047996).length < 2 ^ (prefixWord ++ tailWord_4047996).sum := by decide
  have hdescent : baseEnd_4047996 < baseStart_4047996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048100 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_4048100 : Nat := 118140960795 + 4048100 * 2 ^ 59
def prefixEnd_4048100 : Nat := 4983230072969 + 3 ^ 40 * 4048100 * 2
def baseEnd_4048100 : Nat := 2078621037465717023833133

theorem tailTrace_4048100 : CollatzResearch.WordTrace tailWord_4048100 prefixEnd_4048100 2078621037465717023833133 := by
  unfold tailWord_4048100
  simp only [CollatzResearch.WordTrace]
  refine ⟨73823168317216267641546877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98430891089621690188729169 73823168317216267641546877)
  ·
    refine ⟨27683688118956100365580079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73823168317216267641546877 27683688118956100365580079)
    ·
      refine ⟨41525532178434150548370119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27683688118956100365580079 41525532178434150548370119)
      ·
        refine ⟨62288298267651225822555179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41525532178434150548370119 62288298267651225822555179)
        ·
          refine ⟨93432447401476838733832769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62288298267651225822555179 93432447401476838733832769)
          ·
            refine ⟨70074335551107629050374577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93432447401476838733832769 70074335551107629050374577)
            ·
              refine ⟨52555751663330721787780933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70074335551107629050374577 52555751663330721787780933)
              ·
                refine ⟨9854203436874510335208925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52555751663330721787780933 9854203436874510335208925)
                ·
                  refine ⟨3695326288827941375703347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9854203436874510335208925 3695326288827941375703347)
                  ·
                    refine ⟨5542989433241912063555021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3695326288827941375703347 5542989433241912063555021)
                    ·
                      refine ⟨2078621037465717023833133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5542989433241912063555021 2078621037465717023833133)
                      ·
                        rfl

theorem cell23_4048100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_4048100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048100 prefixEnd_4048100 := by exact prefixLift 4048100
  have htrace : WordTrace (prefixWord ++ tailWord_4048100) baseStart_4048100 baseEnd_4048100 := by
    simpa [prefixWord, tailWord_4048100, baseEnd_4048100] using wordTrace_append hprefix tailTrace_4048100
  have hstable : (prefixWord ++ tailWord_4048100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048100).length < 2 ^ (prefixWord ++ tailWord_4048100).sum := by decide
  have hdescent : baseEnd_4048100 < baseStart_4048100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048110 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_4048110 : Nat := 118140960795 + 4048110 * 2 ^ 59
def prefixEnd_4048110 : Nat := 4983230072969 + 3 ^ 40 * 4048110 * 2
def baseEnd_4048110 : Nat := 2078626172272261984708087

theorem tailTrace_4048110 : CollatzResearch.WordTrace tailWord_4048110 prefixEnd_4048110 2078626172272261984708087 := by
  unfold tailWord_4048110
  simp only [CollatzResearch.WordTrace]
  refine ⟨18455837670549538373869723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98431134242930871327305189 18455837670549538373869723)
  ·
    refine ⟨27683756505824307560804585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18455837670549538373869723 27683756505824307560804585)
    ·
      refine ⟨20762817379368230670603439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27683756505824307560804585 20762817379368230670603439)
      ·
        refine ⟨31144226069052346005905159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20762817379368230670603439 31144226069052346005905159)
        ·
          refine ⟨46716339103578519008857739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31144226069052346005905159 46716339103578519008857739)
          ·
            refine ⟨70074508655367778513286609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46716339103578519008857739 70074508655367778513286609)
            ·
              refine ⟨52555881491525833884964957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70074508655367778513286609 52555881491525833884964957)
              ·
                refine ⟨19708455559322187706861859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52555881491525833884964957 19708455559322187706861859)
                ·
                  refine ⟨29562683338983281560292789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19708455559322187706861859 29562683338983281560292789)
                  ·
                    refine ⟨2771501563029682646277449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29562683338983281560292789 2771501563029682646277449)
                    ·
                      refine ⟨2078626172272261984708087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2771501563029682646277449 2078626172272261984708087)
                      ·
                        rfl

theorem cell23_4048110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_4048110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048110 prefixEnd_4048110 := by exact prefixLift 4048110
  have htrace : WordTrace (prefixWord ++ tailWord_4048110) baseStart_4048110 baseEnd_4048110 := by
    simpa [prefixWord, tailWord_4048110, baseEnd_4048110] using wordTrace_append hprefix tailTrace_4048110
  have hstable : (prefixWord ++ tailWord_4048110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048110).length < 2 ^ (prefixWord ++ tailWord_4048110).sum := by decide
  have hdescent : baseEnd_4048110 < baseStart_4048110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048177 : List Nat := [1, 2, 2, 3, 3, 2, 1, 3, 1, 2, 3]
def baseStart_4048177 : Nat := 118140960795 + 4048177 * 2 ^ 59
def prefixEnd_4048177 : Nat := 4983230072969 + 3 ^ 40 * 4048177 * 2
def baseEnd_4048177 : Nat := 2078660575476113222570279

theorem tailTrace_4048177 : CollatzResearch.WordTrace tailWord_4048177 prefixEnd_4048177 2078660575476113222570279 := by
  unfold tailWord_4048177
  simp only [CollatzResearch.WordTrace]
  refine ⟨147649145055153577433646785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98432763370102384955764523 147649145055153577433646785)
  ·
    refine ⟨110736858791365183075235089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147649145055153577433646785 110736858791365183075235089)
    ·
      refine ⟨83052644093523887306426317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110736858791365183075235089 83052644093523887306426317)
      ·
        refine ⟨31144741535071457739909869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83052644093523887306426317 31144741535071457739909869)
        ·
          refine ⟨11679278075651796652466201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31144741535071457739909869 11679278075651796652466201)
          ·
            refine ⟨8759458556738847489349651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11679278075651796652466201 8759458556738847489349651)
            ·
              refine ⟨13139187835108271234024477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8759458556738847489349651 13139187835108271234024477)
              ·
                refine ⟨4927195438165601712759179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13139187835108271234024477 4927195438165601712759179)
                ·
                  refine ⟨7390793157248402569138769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927195438165601712759179 7390793157248402569138769)
                  ·
                    refine ⟨5543094867936301926854077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7390793157248402569138769 5543094867936301926854077)
                    ·
                      refine ⟨2078660575476113222570279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5543094867936301926854077 2078660575476113222570279)
                      ·
                        rfl

theorem cell23_4048177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_4048177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048177 prefixEnd_4048177 := by exact prefixLift 4048177
  have htrace : WordTrace (prefixWord ++ tailWord_4048177) baseStart_4048177 baseEnd_4048177 := by
    simpa [prefixWord, tailWord_4048177, baseEnd_4048177] using wordTrace_append hprefix tailTrace_4048177
  have hstable : (prefixWord ++ tailWord_4048177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048177).length < 2 ^ (prefixWord ++ tailWord_4048177).sum := by decide
  have hdescent : baseEnd_4048177 < baseStart_4048177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048217 : List Nat := [1, 2, 1, 2, 2, 2, 3, 4, 1, 3, 2]
def baseStart_4048217 : Nat := 118140960795 + 4048217 * 2 ^ 59
def prefixEnd_4048217 : Nat := 4983230072969 + 3 ^ 40 * 4048217 * 2
def baseEnd_4048217 : Nat := 2078681114702293066070095

theorem tailTrace_4048217 : CollatzResearch.WordTrace tailWord_4048217 prefixEnd_4048217 2078681114702293066070095 := by
  unfold tailWord_4048217
  simp only [CollatzResearch.WordTrace]
  refine ⟨147650603975008664265102905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98433735983339109510068603 147650603975008664265102905)
  ·
    refine ⟨110737952981256498198827179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147650603975008664265102905 110737952981256498198827179)
    ·
      refine ⟨166106929471884747298240769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110737952981256498198827179 166106929471884747298240769)
      ·
        refine ⟨124580197103913560473680577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166106929471884747298240769 124580197103913560473680577)
        ·
          refine ⟨93435147827935170355260433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124580197103913560473680577 93435147827935170355260433)
          ·
            refine ⟨70076360870951377766445325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93435147827935170355260433 70076360870951377766445325)
            ·
              refine ⟨26278635326606766662416997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70076360870951377766445325 26278635326606766662416997)
              ·
                refine ⟨4927244123738768749203187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26278635326606766662416997 4927244123738768749203187)
                ·
                  refine ⟨7390866185608153123804781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927244123738768749203187 7390866185608153123804781)
                  ·
                    refine ⟨2771574819603057421426793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7390866185608153123804781 2771574819603057421426793)
                    ·
                      refine ⟨2078681114702293066070095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2771574819603057421426793 2078681114702293066070095)
                      ·
                        rfl

theorem cell23_4048217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 3, 2].length) (baseStart_4048217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048217 prefixEnd_4048217 := by exact prefixLift 4048217
  have htrace : WordTrace (prefixWord ++ tailWord_4048217) baseStart_4048217 baseEnd_4048217 := by
    simpa [prefixWord, tailWord_4048217, baseEnd_4048217] using wordTrace_append hprefix tailTrace_4048217
  have hstable : (prefixWord ++ tailWord_4048217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048217).length < 2 ^ (prefixWord ++ tailWord_4048217).sum := by decide
  have hdescent : baseEnd_4048217 < baseStart_4048217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048247 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 4, 2, 2]
def baseStart_4048247 : Nat := 118140960795 + 4048247 * 2 ^ 59
def prefixEnd_4048247 : Nat := 4983230072969 + 3 ^ 40 * 4048247 * 2
def baseEnd_4048247 : Nat := 2078696519121927948694957

theorem tailTrace_4048247 : CollatzResearch.WordTrace tailWord_4048247 prefixEnd_4048247 2078696519121927948694957 := by
  unfold tailWord_4048247
  simp only [CollatzResearch.WordTrace]
  refine ⟨147651698164899979388694995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98434465443266652925796663 147651698164899979388694995)
  ·
    refine ⟨221477547247349969083042493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147651698164899979388694995 221477547247349969083042493)
    ·
      refine ⟨83054080217756238406140935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221477547247349969083042493 83054080217756238406140935)
      ·
        refine ⟨124581120326634357609211403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83054080217756238406140935 124581120326634357609211403)
        ·
          refine ⟨186871680489951536413817105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124581120326634357609211403 186871680489951536413817105)
          ·
            refine ⟨140153760367463652310362829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186871680489951536413817105 140153760367463652310362829)
            ·
              refine ⟨52557660137798869616386061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140153760367463652310362829 52557660137798869616386061)
              ·
                refine ⟨19709122551674576106144773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52557660137798869616386061 19709122551674576106144773)
                ·
                  refine ⟨3695460478438983019902145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19709122551674576106144773 3695460478438983019902145)
                  ·
                    refine ⟨2771595358829237264926609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3695460478438983019902145 2771595358829237264926609)
                    ·
                      refine ⟨2078696519121927948694957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2771595358829237264926609 2078696519121927948694957)
                      ·
                        rfl

theorem cell23_4048247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 2, 2].length) (baseStart_4048247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048247 prefixEnd_4048247 := by exact prefixLift 4048247
  have htrace : WordTrace (prefixWord ++ tailWord_4048247) baseStart_4048247 baseEnd_4048247 := by
    simpa [prefixWord, tailWord_4048247, baseEnd_4048247] using wordTrace_append hprefix tailTrace_4048247
  have hstable : (prefixWord ++ tailWord_4048247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048247).length < 2 ^ (prefixWord ++ tailWord_4048247).sum := by decide
  have hdescent : baseEnd_4048247 < baseStart_4048247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048258 : List Nat := [3, 4, 2, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_4048258 : Nat := 118140960795 + 4048258 * 2 ^ 59
def prefixEnd_4048258 : Nat := 4983230072969 + 3 ^ 40 * 4048258 * 2
def baseEnd_4048258 : Nat := 2078702167409127405657407

theorem tailTrace_4048258 : CollatzResearch.WordTrace tailWord_4048258 prefixEnd_4048258 2078702167409127405657407 := by
  unfold tailWord_4048258
  simp only [CollatzResearch.WordTrace]
  refine ⟨36913024841965032066836357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98434732911906752178230285 36913024841965032066836357)
  ·
    refine ⟨6921192157868443512531817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36913024841965032066836357 6921192157868443512531817)
    ·
      refine ⟨5190894118401332634398863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6921192157868443512531817 5190894118401332634398863)
      ·
        refine ⟨7786341177601998951598295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5190894118401332634398863 7786341177601998951598295)
        ·
          refine ⟨11679511766402998427397443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7786341177601998951598295 11679511766402998427397443)
          ·
            refine ⟨17519267649604497641096165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11679511766402998427397443 17519267649604497641096165)
            ·
              refine ⟨3284862684300843307705531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17519267649604497641096165 3284862684300843307705531)
              ·
                refine ⟨4927294026451264961558297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284862684300843307705531 4927294026451264961558297)
                ·
                  refine ⟨3695470519838448721168723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4927294026451264961558297 3695470519838448721168723)
                  ·
                    refine ⟨5543205779757673081753085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3695470519838448721168723 5543205779757673081753085)
                    ·
                      refine ⟨2078702167409127405657407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5543205779757673081753085 2078702167409127405657407)
                      ·
                        rfl

theorem cell23_4048258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_4048258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048258 prefixEnd_4048258 := by exact prefixLift 4048258
  have htrace : WordTrace (prefixWord ++ tailWord_4048258) baseStart_4048258 baseEnd_4048258 := by
    simpa [prefixWord, tailWord_4048258, baseEnd_4048258] using wordTrace_append hprefix tailTrace_4048258
  have hstable : (prefixWord ++ tailWord_4048258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048258).length < 2 ^ (prefixWord ++ tailWord_4048258).sum := by decide
  have hdescent : baseEnd_4048258 < baseStart_4048258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048300 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 2, 5]
def baseStart_4048300 : Nat := 118140960795 + 4048300 * 2 ^ 59
def prefixEnd_4048300 : Nat := 4983230072969 + 3 ^ 40 * 4048300 * 2
def baseEnd_4048300 : Nat := 692907911198872080444071

theorem tailTrace_4048300 : CollatzResearch.WordTrace tailWord_4048300 prefixEnd_4048300 692907911198872080444071 := by
  unfold tailWord_4048300
  simp only [CollatzResearch.WordTrace]
  refine ⟨73826815616853984720187177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98435754155805312960249569 73826815616853984720187177)
  ·
    refine ⟨55370111712640488540140383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73826815616853984720187177 55370111712640488540140383)
    ·
      refine ⟨83055167568960732810210575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55370111712640488540140383 83055167568960732810210575)
      ·
        refine ⟨124582751353441099215315863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83055167568960732810210575 124582751353441099215315863)
        ·
          refine ⟨186874127030161648822973795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124582751353441099215315863 186874127030161648822973795)
          ·
            refine ⟨280311190545242473234460693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186874127030161648822973795 280311190545242473234460693)
            ·
              refine ⟨13139587056808240932865345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 280311190545242473234460693 13139587056808240932865345)
              ·
                refine ⟨9854690292606180699649009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13139587056808240932865345 9854690292606180699649009)
                ·
                  refine ⟨7391017719454635524736757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9854690292606180699649009 7391017719454635524736757)
                  ·
                    refine ⟨692907911198872080444071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7391017719454635524736757 692907911198872080444071)
                    ·
                      rfl

theorem cell23_4048300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_4048300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048300 prefixEnd_4048300 := by exact prefixLift 4048300
  have htrace : WordTrace (prefixWord ++ tailWord_4048300) baseStart_4048300 baseEnd_4048300 := by
    simpa [prefixWord, tailWord_4048300, baseEnd_4048300] using wordTrace_append hprefix tailTrace_4048300
  have hstable : (prefixWord ++ tailWord_4048300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048300).length < 2 ^ (prefixWord ++ tailWord_4048300).sum := by decide
  have hdescent : baseEnd_4048300 < baseStart_4048300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048320 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 4]
def baseStart_4048320 : Nat := 118140960795 + 4048320 * 2 ^ 59
def prefixEnd_4048320 : Nat := 4983230072969 + 3 ^ 40 * 4048320 * 2
def baseEnd_4048320 : Nat := 2078734003209706163082121

theorem tailTrace_4048320 : CollatzResearch.WordTrace tailWord_4048320 prefixEnd_4048320 2078734003209706163082121 := by
  unfold tailWord_4048320
  simp only [CollatzResearch.WordTrace]
  refine ⟨73827180346817756428051207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98436240462423675237401609 73827180346817756428051207)
  ·
    refine ⟨110740770520226634642076811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73827180346817756428051207 110740770520226634642076811)
    ·
      refine ⟨166111155780339951963115217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110740770520226634642076811 166111155780339951963115217)
      ·
        refine ⟨124583366835254963972336413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166111155780339951963115217 124583366835254963972336413)
        ·
          refine ⟨46718762563220611489626155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124583366835254963972336413 46718762563220611489626155)
          ·
            refine ⟨70078143844830917234439233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46718762563220611489626155 70078143844830917234439233)
            ·
              refine ⟨52558607883623187925829425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70078143844830917234439233 52558607883623187925829425)
              ·
                refine ⟨39418955912717390944372069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52558607883623187925829425 39418955912717390944372069)
                ·
                  refine ⟨7391054233634510802069763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39418955912717390944372069 7391054233634510802069763)
                  ·
                    refine ⟨11086581350451766203104645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7391054233634510802069763 11086581350451766203104645)
                    ·
                      refine ⟨2078734003209706163082121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11086581350451766203104645 2078734003209706163082121)
                      ·
                        rfl

theorem cell23_4048320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_4048320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048320 prefixEnd_4048320 := by exact prefixLift 4048320
  have htrace : WordTrace (prefixWord ++ tailWord_4048320) baseStart_4048320 baseEnd_4048320 := by
    simpa [prefixWord, tailWord_4048320, baseEnd_4048320] using wordTrace_append hprefix tailTrace_4048320
  have hstable : (prefixWord ++ tailWord_4048320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048320).length < 2 ^ (prefixWord ++ tailWord_4048320).sum := by decide
  have hdescent : baseEnd_4048320 < baseStart_4048320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048360 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 8]
def baseStart_4048360 : Nat := 118140960795 + 4048360 * 2 ^ 59
def prefixEnd_4048360 : Nat := 4983230072969 + 3 ^ 40 * 4048360 * 2
def baseEnd_4048360 : Nat := 230972726937320667397993

theorem tailTrace_4048360 : CollatzResearch.WordTrace tailWord_4048360 prefixEnd_4048360 230972726937320667397993 := by
  unfold tailWord_4048360
  simp only [CollatzResearch.WordTrace]
  refine ⟨73827909806745299843779267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98437213075660399791705689 73827909806745299843779267)
  ·
    refine ⟨110741864710117949765668901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73827909806745299843779267 110741864710117949765668901)
    ·
      refine ⟨20764099633147115581062919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110741864710117949765668901 20764099633147115581062919)
      ·
        refine ⟨31146149449720673371594379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20764099633147115581062919 31146149449720673371594379)
        ·
          refine ⟨46719224174581010057391569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31146149449720673371594379 46719224174581010057391569)
          ·
            refine ⟨35039418130935757543043677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46719224174581010057391569 35039418130935757543043677)
            ·
              refine ⟨13139781799100909078641379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35039418130935757543043677 13139781799100909078641379)
              ·
                refine ⟨19709672698651363617962069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13139781799100909078641379 19709672698651363617962069)
                ·
                  refine ⟨230972726937320667397993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19709672698651363617962069 230972726937320667397993)
                  ·
                    rfl

theorem cell23_4048360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 8].length) (baseStart_4048360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048360 prefixEnd_4048360 := by exact prefixLift 4048360
  have htrace : WordTrace (prefixWord ++ tailWord_4048360) baseStart_4048360 baseEnd_4048360 := by
    simpa [prefixWord, tailWord_4048360, baseEnd_4048360] using wordTrace_append hprefix tailTrace_4048360
  have hstable : (prefixWord ++ tailWord_4048360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048360).length < 2 ^ (prefixWord ++ tailWord_4048360).sum := by decide
  have hdescent : baseEnd_4048360 < baseStart_4048360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048387 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 5, 1, 3]
def baseStart_4048387 : Nat := 118140960795 + 4048387 * 2 ^ 59
def prefixEnd_4048387 : Nat := 4983230072969 + 3 ^ 40 * 4048387 * 2
def baseEnd_4048387 : Nat := 2078768406413557400944313

theorem tailTrace_4048387 : CollatzResearch.WordTrace tailWord_4048387 prefixEnd_4048387 2078768406413557400944313 := by
  unfold tailWord_4048387
  simp only [CollatzResearch.WordTrace]
  refine ⟨147656804384392783298791415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98437869589595188865860943 147656804384392783298791415)
  ·
    refine ⟨221485206576589174948187123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147656804384392783298791415 221485206576589174948187123)
    ·
      refine ⟨332227809864883762422280685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221485206576589174948187123 332227809864883762422280685)
      ·
        refine ⟨124585428699331410908355257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332227809864883762422280685 124585428699331410908355257)
        ·
          refine ⟨93439071524498558181266443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124585428699331410908355257 93439071524498558181266443)
          ·
            refine ⟨140158607286747837271899665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93439071524498558181266443 140158607286747837271899665)
            ·
              refine ⟨105118955465060877953924749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140158607286747837271899665 105118955465060877953924749)
              ·
                refine ⟨39419608299397829232721781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105118955465060877953924749 39419608299397829232721781)
                ·
                  refine ⟨3695588278068546490567667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39419608299397829232721781 3695588278068546490567667)
                  ·
                    refine ⟨5543382417102819735851501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3695588278068546490567667 5543382417102819735851501)
                    ·
                      refine ⟨2078768406413557400944313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5543382417102819735851501 2078768406413557400944313)
                      ·
                        rfl

theorem cell23_4048387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_4048387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048387 prefixEnd_4048387 := by exact prefixLift 4048387
  have htrace : WordTrace (prefixWord ++ tailWord_4048387) baseStart_4048387 baseEnd_4048387 := by
    simpa [prefixWord, tailWord_4048387, baseEnd_4048387] using wordTrace_append hprefix tailTrace_4048387
  have hstable : (prefixWord ++ tailWord_4048387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048387).length < 2 ^ (prefixWord ++ tailWord_4048387).sum := by decide
  have hdescent : baseEnd_4048387 < baseStart_4048387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048398 : List Nat := [4, 1, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_4048398 : Nat := 118140960795 + 4048398 * 2 ^ 59
def prefixEnd_4048398 : Nat := 4983230072969 + 3 ^ 40 * 4048398 * 2
def baseEnd_4048398 : Nat := 692924684900252285968921

theorem tailTrace_4048398 : CollatzResearch.WordTrace tailWord_4048398 prefixEnd_4048398 692924684900252285968921 := by
  unfold tailWord_4048398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18457150698419116522180231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98438137058235288118294565 18457150698419116522180231)
  ·
    refine ⟨27685726047628674783270347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18457150698419116522180231 27685726047628674783270347)
    ·
      refine ⟨41528589071443012174905521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27685726047628674783270347 41528589071443012174905521)
      ·
        refine ⟨31146441803582259131179141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41528589071443012174905521 31146441803582259131179141)
        ·
          refine ⟨5839957838171673587096089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31146441803582259131179141 5839957838171673587096089)
          ·
            refine ⟨4379968378628755190322067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5839957838171673587096089 4379968378628755190322067)
            ·
              refine ⟨6569952567943132785483101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379968378628755190322067 6569952567943132785483101)
              ·
                refine ⟨2463732212978674794556163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6569952567943132785483101 2463732212978674794556163)
                ·
                  refine ⟨3695598319468012191834245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463732212978674794556163 3695598319468012191834245)
                  ·
                    refine ⟨692924684900252285968921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3695598319468012191834245 692924684900252285968921)
                    ·
                      rfl

theorem cell23_4048398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_4048398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048398 prefixEnd_4048398 := by exact prefixLift 4048398
  have htrace : WordTrace (prefixWord ++ tailWord_4048398) baseStart_4048398 baseEnd_4048398 := by
    simpa [prefixWord, tailWord_4048398, baseEnd_4048398] using wordTrace_append hprefix tailTrace_4048398
  have hstable : (prefixWord ++ tailWord_4048398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048398).length < 2 ^ (prefixWord ++ tailWord_4048398).sum := by decide
  have hdescent : baseEnd_4048398 < baseStart_4048398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048444 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_4048444 : Nat := 118140960795 + 4048444 * 2 ^ 59
def prefixEnd_4048444 : Nat := 4983230072969 + 3 ^ 40 * 4048444 * 2
def baseEnd_4048444 : Nat := 2078797674810863677931551

theorem tailTrace_4048444 : CollatzResearch.WordTrace tailWord_4048444 prefixEnd_4048444 2078797674810863677931551 := by
  unfold tailWord_4048444
  simp only [CollatzResearch.WordTrace]
  refine ⟨73829441672593141016808193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98439255563457521355744257 73829441672593141016808193)
  ·
    refine ⟨55372081254444855762606145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73829441672593141016808193 55372081254444855762606145)
    ·
      refine ⟨41529060940833641821954609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55372081254444855762606145 41529060940833641821954609)
      ·
        refine ⟨31146795705625231366465957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41529060940833641821954609 31146795705625231366465957)
        ·
          refine ⟨5840024194804730881212367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31146795705625231366465957 5840024194804730881212367)
          ·
            refine ⟨8760036292207096321818551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5840024194804730881212367 8760036292207096321818551)
            ·
              refine ⟨13140054438310644482727827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8760036292207096321818551 13140054438310644482727827)
              ·
                refine ⟨19710081657465966724091741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13140054438310644482727827 19710081657465966724091741)
                ·
                  refine ⟨7391280621549737521534403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19710081657465966724091741 7391280621549737521534403)
                  ·
                    refine ⟨11086920932324606282301605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7391280621549737521534403 11086920932324606282301605)
                    ·
                      refine ⟨2078797674810863677931551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11086920932324606282301605 2078797674810863677931551)
                      ·
                        rfl

theorem cell23_4048444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_4048444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048444 prefixEnd_4048444 := by exact prefixLift 4048444
  have htrace : WordTrace (prefixWord ++ tailWord_4048444) baseStart_4048444 baseEnd_4048444 := by
    simpa [prefixWord, tailWord_4048444, baseEnd_4048444] using wordTrace_append hprefix tailTrace_4048444
  have hstable : (prefixWord ++ tailWord_4048444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048444).length < 2 ^ (prefixWord ++ tailWord_4048444).sum := by decide
  have hdescent : baseEnd_4048444 < baseStart_4048444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048537 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 2, 4, 3]
def baseStart_4048537 : Nat := 118140960795 + 4048537 * 2 ^ 59
def prefixEnd_4048537 : Nat := 4983230072969 + 3 ^ 40 * 4048537 * 2
def baseEnd_4048537 : Nat := 2078845428511731814068623

theorem tailTrace_4048537 : CollatzResearch.WordTrace tailWord_4048537 prefixEnd_4048537 2078845428511731814068623 := by
  unfold tailWord_4048537
  simp only [CollatzResearch.WordTrace]
  refine ⟨147662275333849358916751865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98441516889232905944501243 147662275333849358916751865)
  ·
    refine ⟨110746706500387019187563899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147662275333849358916751865 110746706500387019187563899)
    ·
      refine ⟨166120059750580528781345849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110746706500387019187563899 166120059750580528781345849)
      ·
        refine ⟨124590044812935396586009387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166120059750580528781345849 124590044812935396586009387)
        ·
          refine ⟨186885067219403094879014081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124590044812935396586009387 186885067219403094879014081)
          ·
            refine ⟨140163800414552321159260561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186885067219403094879014081 140163800414552321159260561)
            ·
              refine ⟨105122850310914240869445421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140163800414552321159260561 105122850310914240869445421)
              ·
                refine ⟨39421068866592840326042033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105122850310914240869445421 39421068866592840326042033)
                ·
                  refine ⟨29565801649944630244531525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39421068866592840326042033 29565801649944630244531525)
                  ·
                    refine ⟨5543587809364618170849661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29565801649944630244531525 5543587809364618170849661)
                    ·
                      refine ⟨2078845428511731814068623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5543587809364618170849661 2078845428511731814068623)
                      ·
                        rfl

theorem cell23_4048537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_4048537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048537 prefixEnd_4048537 := by exact prefixLift 4048537
  have htrace : WordTrace (prefixWord ++ tailWord_4048537) baseStart_4048537 baseEnd_4048537 := by
    simpa [prefixWord, tailWord_4048537, baseEnd_4048537] using wordTrace_append hprefix tailTrace_4048537
  have hstable : (prefixWord ++ tailWord_4048537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048537).length < 2 ^ (prefixWord ++ tailWord_4048537).sum := by decide
  have hdescent : baseEnd_4048537 < baseStart_4048537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048547 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 4]
def baseStart_4048547 : Nat := 118140960795 + 4048547 * 2 ^ 59
def prefixEnd_4048547 : Nat := 4983230072969 + 3 ^ 40 * 4048547 * 2
def baseEnd_4048547 : Nat := 2078850563318276774943577

theorem tailTrace_4048547 : CollatzResearch.WordTrace tailWord_4048547 prefixEnd_4048547 2078850563318276774943577 := by
  unfold tailWord_4048547
  simp only [CollatzResearch.WordTrace]
  refine ⟨147662640063813130624615895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98441760042542087083077263 147662640063813130624615895)
  ·
    refine ⟨221493960095719695936923843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147662640063813130624615895 221493960095719695936923843)
    ·
      refine ⟨332240940143579543905385765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221493960095719695936923843 332240940143579543905385765)
      ·
        refine ⟨62295176276921164482259831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332240940143579543905385765 62295176276921164482259831)
        ·
          refine ⟨93442764415381746723389747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62295176276921164482259831 93442764415381746723389747)
          ·
            refine ⟨140164146623072620085084621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93442764415381746723389747 140164146623072620085084621)
            ·
              refine ⟨52561554983652232531906733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140164146623072620085084621 52561554983652232531906733)
              ·
                refine ⟨19710583118869587199465025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52561554983652232531906733 19710583118869587199465025)
                ·
                  refine ⟨14782937339152190399598769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19710583118869587199465025 14782937339152190399598769)
                  ·
                    refine ⟨11087203004364142799699077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14782937339152190399598769 11087203004364142799699077)
                    ·
                      refine ⟨2078850563318276774943577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11087203004364142799699077 2078850563318276774943577)
                      ·
                        rfl

theorem cell23_4048547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_4048547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048547 prefixEnd_4048547 := by exact prefixLift 4048547
  have htrace : WordTrace (prefixWord ++ tailWord_4048547) baseStart_4048547 baseEnd_4048547 := by
    simpa [prefixWord, tailWord_4048547, baseEnd_4048547] using wordTrace_append hprefix tailTrace_4048547
  have hstable : (prefixWord ++ tailWord_4048547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048547).length < 2 ^ (prefixWord ++ tailWord_4048547).sum := by decide
  have hdescent : baseEnd_4048547 < baseStart_4048547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048621 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_4048621 : Nat := 118140960795 + 4048621 * 2 ^ 59
def prefixEnd_4048621 : Nat := 4983230072969 + 3 ^ 40 * 4048621 * 2
def baseEnd_4048621 : Nat := 692962853628903161806079

theorem tailTrace_4048621 : CollatzResearch.WordTrace tailWord_4048621 prefixEnd_4048621 692962853628903161806079 := by
  unfold tailWord_4048621
  simp only [CollatzResearch.WordTrace]
  refine ⟨147665339065545041262809717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98443559377030027508539811 147665339065545041262809717)
  ·
    refine ⟨13843625537394847618388411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147665339065545041262809717 13843625537394847618388411)
    ·
      refine ⟨20765438306092271427582617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13843625537394847618388411 20765438306092271427582617)
      ·
        refine ⟨15574078729569203570686963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20765438306092271427582617 15574078729569203570686963)
        ·
          refine ⟨23361118094353805356030445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15574078729569203570686963 23361118094353805356030445)
          ·
            refine ⟨8760419285382677008511417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23361118094353805356030445 8760419285382677008511417)
            ·
              refine ⟨6570314464037007756383563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8760419285382677008511417 6570314464037007756383563)
              ·
                refine ⟨9855471696055511634575345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6570314464037007756383563 9855471696055511634575345)
                ·
                  refine ⟨7391603772041633725931509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9855471696055511634575345 7391603772041633725931509)
                  ·
                    refine ⟨692962853628903161806079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7391603772041633725931509 692962853628903161806079)
                    ·
                      rfl

theorem cell23_4048621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_4048621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048621 prefixEnd_4048621 := by exact prefixLift 4048621
  have htrace : WordTrace (prefixWord ++ tailWord_4048621) baseStart_4048621 baseEnd_4048621 := by
    simpa [prefixWord, tailWord_4048621, baseEnd_4048621] using wordTrace_append hprefix tailTrace_4048621
  have hstable : (prefixWord ++ tailWord_4048621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048621).length < 2 ^ (prefixWord ++ tailWord_4048621).sum := by decide
  have hdescent : baseEnd_4048621 < baseStart_4048621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048624 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 3, 6, 2]
def baseStart_4048624 : Nat := 118140960795 + 4048624 * 2 ^ 59
def prefixEnd_4048624 : Nat := 4983230072969 + 3 ^ 40 * 4048624 * 2
def baseEnd_4048624 : Nat := 2078890101328672973680723

theorem tailTrace_4048624 : CollatzResearch.WordTrace tailWord_4048624 prefixEnd_4048624 2078890101328672973680723 := by
  unfold tailWord_4048624
  simp only [CollatzResearch.WordTrace]
  refine ⟨73832724242267086387584463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98443632323022781850112617 73832724242267086387584463)
  ·
    refine ⟨110749086363400629581376695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73832724242267086387584463 110749086363400629581376695)
    ·
      refine ⟨166123629545100944372065043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110749086363400629581376695 166123629545100944372065043)
      ·
        refine ⟨249185444317651416558097565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166123629545100944372065043 249185444317651416558097565)
        ·
          refine ⟨93444541619119281209286587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249185444317651416558097565 93444541619119281209286587)
          ·
            refine ⟨140166812428678921813929881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93444541619119281209286587 140166812428678921813929881)
            ·
              refine ⟨105125109321509191360447411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140166812428678921813929881 105125109321509191360447411)
              ·
                refine ⟨157687663982263787040671117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105125109321509191360447411 157687663982263787040671117)
                ·
                  refine ⟨59132873993348920140251669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157687663982263787040671117 59132873993348920140251669)
                  ·
                    refine ⟨2771853468438230631574297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59132873993348920140251669 2771853468438230631574297)
                    ·
                      refine ⟨2078890101328672973680723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2771853468438230631574297 2078890101328672973680723)
                      ·
                        rfl

theorem cell23_4048624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 6, 2].length) (baseStart_4048624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048624 prefixEnd_4048624 := by exact prefixLift 4048624
  have htrace : WordTrace (prefixWord ++ tailWord_4048624) baseStart_4048624 baseEnd_4048624 := by
    simpa [prefixWord, tailWord_4048624, baseEnd_4048624] using wordTrace_append hprefix tailTrace_4048624
  have hstable : (prefixWord ++ tailWord_4048624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048624).length < 2 ^ (prefixWord ++ tailWord_4048624).sum := by decide
  have hdescent : baseEnd_4048624 < baseStart_4048624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048658 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_4048658 : Nat := 118140960795 + 4048658 * 2 ^ 59
def prefixEnd_4048658 : Nat := 4983230072969 + 3 ^ 40 * 4048658 * 2
def baseEnd_4048658 : Nat := 2078907559670925840655567

theorem tailTrace_4048658 : CollatzResearch.WordTrace tailWord_4048658 prefixEnd_4048658 2078907559670925840655567 := by
  unfold tailWord_4048658
  simp only [CollatzResearch.WordTrace]
  refine ⟨36916672141602749145476657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98444459044273997721271085 36916672141602749145476657)
  ·
    refine ⟨27687504106202061859107493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36916672141602749145476657 27687504106202061859107493)
    ·
      refine ⟨5191407019912886598582655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27687504106202061859107493 5191407019912886598582655)
      ·
        refine ⟨7787110529869329897873983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5191407019912886598582655 7787110529869329897873983)
        ·
          refine ⟨11680665794803994846810975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7787110529869329897873983 11680665794803994846810975)
          ·
            refine ⟨17520998692205992270216463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11680665794803994846810975 17520998692205992270216463)
            ·
              refine ⟨26281498038308988405324695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17520998692205992270216463 26281498038308988405324695)
              ·
                refine ⟨39422247057463482607987043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26281498038308988405324695 39422247057463482607987043)
                ·
                  refine ⟨59133370586195223911980565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39422247057463482607987043 59133370586195223911980565)
                  ·
                    refine ⟨2771876746227901120874089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59133370586195223911980565 2771876746227901120874089)
                    ·
                      refine ⟨2078907559670925840655567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2771876746227901120874089 2078907559670925840655567)
                      ·
                        rfl

theorem cell23_4048658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_4048658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048658 prefixEnd_4048658 := by exact prefixLift 4048658
  have htrace : WordTrace (prefixWord ++ tailWord_4048658) baseStart_4048658 baseEnd_4048658 := by
    simpa [prefixWord, tailWord_4048658, baseEnd_4048658] using wordTrace_append hprefix tailTrace_4048658
  have hstable : (prefixWord ++ tailWord_4048658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048658).length < 2 ^ (prefixWord ++ tailWord_4048658).sum := by decide
  have hdescent : baseEnd_4048658 < baseStart_4048658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048664 : List Nat := [2, 1, 2, 3, 1, 1, 4, 3, 6]
def baseStart_4048664 : Nat := 118140960795 + 4048664 * 2 ^ 59
def prefixEnd_4048664 : Nat := 4983230072969 + 3 ^ 40 * 4048664 * 2
def baseEnd_4048664 : Nat := 230990071172761424131171

theorem tailTrace_4048664 : CollatzResearch.WordTrace tailWord_4048664 prefixEnd_4048664 230990071172761424131171 := by
  unfold tailWord_4048664
  simp only [CollatzResearch.WordTrace]
  refine ⟨73833453702194629803312523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98444604936259506404416697 73833453702194629803312523)
  ·
    refine ⟨110750180553291944704968785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73833453702194629803312523 110750180553291944704968785)
    ·
      refine ⟨83062635414968958528726589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110750180553291944704968785 83062635414968958528726589)
      ·
        refine ⟨31148488280613359448272471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83062635414968958528726589 31148488280613359448272471)
        ·
          refine ⟨46722732420920039172408707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31148488280613359448272471 46722732420920039172408707)
          ·
            refine ⟨70084098631380058758613061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46722732420920039172408707 70084098631380058758613061)
            ·
              refine ⟨13140768493383761017239949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70084098631380058758613061 13140768493383761017239949)
              ·
                refine ⟨4927788185018910381464981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13140768493383761017239949 4927788185018910381464981)
                ·
                  refine ⟨230990071172761424131171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4927788185018910381464981 230990071172761424131171)
                  ·
                    rfl

theorem cell23_4048664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 6].length) (baseStart_4048664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048664 prefixEnd_4048664 := by exact prefixLift 4048664
  have htrace : WordTrace (prefixWord ++ tailWord_4048664) baseStart_4048664 baseEnd_4048664 := by
    simpa [prefixWord, tailWord_4048664, baseEnd_4048664] using wordTrace_append hprefix tailTrace_4048664
  have hstable : (prefixWord ++ tailWord_4048664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048664).length < 2 ^ (prefixWord ++ tailWord_4048664).sum := by decide
  have hdescent : baseEnd_4048664 < baseStart_4048664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048667 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 6]
def baseStart_4048667 : Nat := 118140960795 + 4048667 * 2 ^ 59
def prefixEnd_4048667 : Nat := 4983230072969 + 3 ^ 40 * 4048667 * 2
def baseEnd_4048667 : Nat := 2078912180996816305443025

theorem tailTrace_4048667 : CollatzResearch.WordTrace tailWord_4048667 prefixEnd_4048667 2078912180996816305443025 := by
  unfold tailWord_4048667
  simp only [CollatzResearch.WordTrace]
  refine ⟨147667016823378391118984255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98444677882252260745989503 147667016823378391118984255)
  ·
    refine ⟨221500525235067586678476383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147667016823378391118984255 221500525235067586678476383)
    ·
      refine ⟨332250787852601380017714575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221500525235067586678476383 332250787852601380017714575)
      ·
        refine ⟨498376181778902070026571863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332250787852601380017714575 498376181778902070026571863)
        ·
          refine ⟨747564272668353105039857795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498376181778902070026571863 747564272668353105039857795)
          ·
            refine ⟨1121346409002529657559786693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747564272668353105039857795 1121346409002529657559786693)
            ·
              refine ⟨210252451687974310792460005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1121346409002529657559786693 210252451687974310792460005)
              ·
                refine ⟨39422334691495183273586251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210252451687974310792460005 39422334691495183273586251)
                ·
                  refine ⟨59133502037242774910379377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39422334691495183273586251 59133502037242774910379377)
                  ·
                    refine ⟨44350126527932081182784533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59133502037242774910379377 44350126527932081182784533)
                    ·
                      refine ⟨2078912180996816305443025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44350126527932081182784533 2078912180996816305443025)
                      ·
                        rfl

theorem cell23_4048667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_4048667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048667 prefixEnd_4048667 := by exact prefixLift 4048667
  have htrace : WordTrace (prefixWord ++ tailWord_4048667) baseStart_4048667 baseEnd_4048667 := by
    simpa [prefixWord, tailWord_4048667, baseEnd_4048667] using wordTrace_append hprefix tailTrace_4048667
  have hstable : (prefixWord ++ tailWord_4048667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048667).length < 2 ^ (prefixWord ++ tailWord_4048667).sum := by decide
  have hdescent : baseEnd_4048667 < baseStart_4048667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048687 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 7]
def baseStart_4048687 : Nat := 118140960795 + 4048687 * 2 ^ 59
def prefixEnd_4048687 : Nat := 4983230072969 + 3 ^ 40 * 4048687 * 2
def baseEnd_4048687 : Nat := 2078922450609906227192933

theorem tailTrace_4048687 : CollatzResearch.WordTrace tailWord_4048687 prefixEnd_4048687 2078922450609906227192933 := by
  unfold tailWord_4048687
  simp only [CollatzResearch.WordTrace]
  refine ⟨147667746283305934534712315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98445164188870623023141543 147667746283305934534712315)
  ·
    refine ⟨221501619424958901802068473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147667746283305934534712315 221501619424958901802068473)
    ·
      refine ⟨166126214568719176351551355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221501619424958901802068473 166126214568719176351551355)
      ·
        refine ⟨249189321853078764527327033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166126214568719176351551355 249189321853078764527327033)
        ·
          refine ⟨186891991389809073395495275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249189321853078764527327033 186891991389809073395495275)
          ·
            refine ⟨280337987084713610093242913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186891991389809073395495275 280337987084713610093242913)
            ·
              refine ⟨210253490313535207569932185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280337987084713610093242913 210253490313535207569932185)
              ·
                refine ⟨157690117735151405677449139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210253490313535207569932185 157690117735151405677449139)
                ·
                  refine ⟨236535176602727108516173709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157690117735151405677449139 236535176602727108516173709)
                  ·
                    refine ⟨88700691226022665693565141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 236535176602727108516173709 88700691226022665693565141)
                    ·
                      refine ⟨2078922450609906227192933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88700691226022665693565141 2078922450609906227192933)
                      ·
                        rfl

theorem cell23_4048687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_4048687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048687 prefixEnd_4048687 := by exact prefixLift 4048687
  have htrace : WordTrace (prefixWord ++ tailWord_4048687) baseStart_4048687 baseEnd_4048687 := by
    simpa [prefixWord, tailWord_4048687, baseEnd_4048687] using wordTrace_append hprefix tailTrace_4048687
  have hstable : (prefixWord ++ tailWord_4048687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048687).length < 2 ^ (prefixWord ++ tailWord_4048687).sum := by decide
  have hdescent : baseEnd_4048687 < baseStart_4048687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048782 : List Nat := [4, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4048782 : Nat := 118140960795 + 4048782 * 2 ^ 59
def prefixEnd_4048782 : Nat := 4983230072969 + 3 ^ 40 * 4048782 * 2
def baseEnd_4048782 : Nat := 2078971231272083355504997

theorem tailTrace_4048782 : CollatzResearch.WordTrace tailWord_4048782 prefixEnd_4048782 2078971231272083355504997 := by
  unfold tailWord_4048782
  simp only [CollatzResearch.WordTrace]
  refine ⟨18458901402245220719927575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98447474145307843839613733 18458901402245220719927575)
  ·
    refine ⟨27688352103367831079891363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18458901402245220719927575 27688352103367831079891363)
    ·
      refine ⟨41532528155051746619837045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27688352103367831079891363 41532528155051746619837045)
      ·
        refine ⟨3893674514536101245609723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41532528155051746619837045 3893674514536101245609723)
        ·
          refine ⟨5840511771804151868414585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893674514536101245609723 5840511771804151868414585)
          ·
            refine ⟨4380383828853113901310939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5840511771804151868414585 4380383828853113901310939)
            ·
              refine ⟨6570575743279670851966409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4380383828853113901310939 6570575743279670851966409)
              ·
                refine ⟨4927931807459753138974807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6570575743279670851966409 4927931807459753138974807)
                ·
                  refine ⟨7391897711189629708462211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927931807459753138974807 7391897711189629708462211)
                  ·
                    refine ⟨11087846566784444562693317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7391897711189629708462211 11087846566784444562693317)
                    ·
                      refine ⟨2078971231272083355504997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11087846566784444562693317 2078971231272083355504997)
                      ·
                        rfl

theorem cell23_4048782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4048782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048782 prefixEnd_4048782 := by exact prefixLift 4048782
  have htrace : WordTrace (prefixWord ++ tailWord_4048782) baseStart_4048782 baseEnd_4048782 := by
    simpa [prefixWord, tailWord_4048782, baseEnd_4048782] using wordTrace_append hprefix tailTrace_4048782
  have hstable : (prefixWord ++ tailWord_4048782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048782).length < 2 ^ (prefixWord ++ tailWord_4048782).sum := by decide
  have hdescent : baseEnd_4048782 < baseStart_4048782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048802 : List Nat := [3, 3, 1, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_4048802 : Nat := 118140960795 + 4048802 * 2 ^ 59
def prefixEnd_4048802 : Nat := 4983230072969 + 3 ^ 40 * 4048802 * 2
def baseEnd_4048802 : Nat := 2078981500885173277254905

theorem tailTrace_4048802 : CollatzResearch.WordTrace tailWord_4048802 prefixEnd_4048802 2078981500885173277254905 := by
  unfold tailWord_4048802
  simp only [CollatzResearch.WordTrace]
  refine ⟨36917985169472327293787165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98447960451926206116765773 36917985169472327293787165)
  ·
    refine ⟨13844244438552122735170187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36917985169472327293787165 13844244438552122735170187)
    ·
      refine ⟨20766366657828184102755281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13844244438552122735170187 20766366657828184102755281)
      ·
        refine ⟨15574774993371138077066461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20766366657828184102755281 15574774993371138077066461)
        ·
          refine ⟨5840540622514176778899923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15574774993371138077066461 5840540622514176778899923)
          ·
            refine ⟨8760810933771265168349885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5840540622514176778899923 8760810933771265168349885)
            ·
              refine ⟨3285304100164224438131207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8760810933771265168349885 3285304100164224438131207)
              ·
                refine ⟨4927956150246336657196811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3285304100164224438131207 4927956150246336657196811)
                ·
                  refine ⟨7391934225369504985795217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927956150246336657196811 7391934225369504985795217)
                  ·
                    refine ⟨5543950669027128739346413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7391934225369504985795217 5543950669027128739346413)
                    ·
                      refine ⟨2078981500885173277254905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5543950669027128739346413 2078981500885173277254905)
                      ·
                        rfl

theorem cell23_4048802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_4048802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048802 prefixEnd_4048802 := by exact prefixLift 4048802
  have htrace : WordTrace (prefixWord ++ tailWord_4048802) baseStart_4048802 baseEnd_4048802 := by
    simpa [prefixWord, tailWord_4048802, baseEnd_4048802] using wordTrace_append hprefix tailTrace_4048802
  have hstable : (prefixWord ++ tailWord_4048802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048802).length < 2 ^ (prefixWord ++ tailWord_4048802).sum := by decide
  have hdescent : baseEnd_4048802 < baseStart_4048802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048821 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_4048821 : Nat := 118140960795 + 4048821 * 2 ^ 59
def prefixEnd_4048821 : Nat := 4983230072969 + 3 ^ 40 * 4048821 * 2
def baseEnd_4048821 : Nat := 2078991257017608702917317

theorem tailTrace_4048821 : CollatzResearch.WordTrace tailWord_4048821 prefixEnd_4048821 2078991257017608702917317 := by
  unfold tailWord_4048821
  simp only [CollatzResearch.WordTrace]
  refine ⟨147672633664820475420090317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98448422443213650280060211 147672633664820475420090317)
  ·
    refine ⟨55377237624307678282533869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147672633664820475420090317 55377237624307678282533869)
    ·
      refine ⟨20766464109115379355950201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55377237624307678282533869 20766464109115379355950201)
      ·
        refine ⟨15574848081836534516962651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20766464109115379355950201 15574848081836534516962651)
        ·
          refine ⟨23362272122754801775443977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15574848081836534516962651 23362272122754801775443977)
          ·
            refine ⟨17521704092066101331582983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23362272122754801775443977 17521704092066101331582983)
            ·
              refine ⟨26282556138099151997374475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17521704092066101331582983 26282556138099151997374475)
              ·
                refine ⟨39423834207148727996061713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26282556138099151997374475 39423834207148727996061713)
                ·
                  refine ⟨29567875655361545997046285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39423834207148727996061713 29567875655361545997046285)
                  ·
                    refine ⟨11087953370760579748892357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29567875655361545997046285 11087953370760579748892357)
                    ·
                      refine ⟨2078991257017608702917317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11087953370760579748892357 2078991257017608702917317)
                      ·
                        rfl

theorem cell23_4048821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_4048821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048821 prefixEnd_4048821 := by exact prefixLift 4048821
  have htrace : WordTrace (prefixWord ++ tailWord_4048821) baseStart_4048821 baseEnd_4048821 := by
    simpa [prefixWord, tailWord_4048821, baseEnd_4048821] using wordTrace_append hprefix tailTrace_4048821
  have hstable : (prefixWord ++ tailWord_4048821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048821).length < 2 ^ (prefixWord ++ tailWord_4048821).sum := by decide
  have hdescent : baseEnd_4048821 < baseStart_4048821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048866 : List Nat := [3, 3, 3, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_4048866 : Nat := 118140960795 + 4048866 * 2 ^ 59
def prefixEnd_4048866 : Nat := 4983230072969 + 3 ^ 40 * 4048866 * 2
def baseEnd_4048866 : Nat := 2079014363647061026854611

theorem tailTrace_4048866 : CollatzResearch.WordTrace tailWord_4048866 prefixEnd_4048866 2079014363647061026854611 := by
  unfold tailWord_4048866
  simp only [CollatzResearch.WordTrace]
  refine ⟨36918568737414362026369613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98449516633104965403652301 36918568737414362026369613)
  ·
    refine ⟨13844463276530385759888605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36918568737414362026369613 13844463276530385759888605)
    ·
      refine ⟨5191673728698894659958227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13844463276530385759888605 5191673728698894659958227)
      ·
        refine ⟨7787510593048341989937341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5191673728698894659958227 7787510593048341989937341)
        ·
          refine ⟨2920316472393128246226503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7787510593048341989937341 2920316472393128246226503)
          ·
            refine ⟨4380474708589692369339755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920316472393128246226503 4380474708589692369339755)
            ·
              refine ⟨6570712062884538554009633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4380474708589692369339755 6570712062884538554009633)
              ·
                refine ⟨4928034047163403915507225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6570712062884538554009633 4928034047163403915507225)
                ·
                  refine ⟨3696025535372552936630419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4928034047163403915507225 3696025535372552936630419)
                  ·
                    refine ⟨5544038303058829404945629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3696025535372552936630419 5544038303058829404945629)
                    ·
                      refine ⟨2079014363647061026854611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5544038303058829404945629 2079014363647061026854611)
                      ·
                        rfl

theorem cell23_4048866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_4048866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048866 prefixEnd_4048866 := by exact prefixLift 4048866
  have htrace : WordTrace (prefixWord ++ tailWord_4048866) baseStart_4048866 baseEnd_4048866 := by
    simpa [prefixWord, tailWord_4048866, baseEnd_4048866] using wordTrace_append hprefix tailTrace_4048866
  have hstable : (prefixWord ++ tailWord_4048866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048866).length < 2 ^ (prefixWord ++ tailWord_4048866).sum := by decide
  have hdescent : baseEnd_4048866 < baseStart_4048866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048878 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 7]
def baseStart_4048878 : Nat := 118140960795 + 4048878 * 2 ^ 59
def prefixEnd_4048878 : Nat := 4983230072969 + 3 ^ 40 * 4048878 * 2
def baseEnd_4048878 : Nat := 231002280601657219989395

theorem tailTrace_4048878 : CollatzResearch.WordTrace tailWord_4048878 prefixEnd_4048878 231002280601657219989395 := by
  unfold tailWord_4048878
  simp only [CollatzResearch.WordTrace]
  refine ⟨18459339078201746769364411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98449808417075982769943525 18459339078201746769364411)
  ·
    refine ⟨27689008617302620154046617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18459339078201746769364411 27689008617302620154046617)
    ·
      refine ⟨20766756462976965115534963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27689008617302620154046617 20766756462976965115534963)
      ·
        refine ⟨31150134694465447673302445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20766756462976965115534963 31150134694465447673302445)
        ·
          refine ⟨11681300510424542877488417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31150134694465447673302445 11681300510424542877488417)
          ·
            refine ⟨8760975382818407158116313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11681300510424542877488417 8760975382818407158116313)
            ·
              refine ⟨6570731537113805368587235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8760975382818407158116313 6570731537113805368587235)
              ·
                refine ⟨9856097305670708052880853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6570731537113805368587235 9856097305670708052880853)
                ·
                  refine ⟨231002280601657219989395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9856097305670708052880853 231002280601657219989395)
                  ·
                    rfl

theorem cell23_4048878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_4048878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048878 prefixEnd_4048878 := by exact prefixLift 4048878
  have htrace : WordTrace (prefixWord ++ tailWord_4048878) baseStart_4048878 baseEnd_4048878 := by
    simpa [prefixWord, tailWord_4048878, baseEnd_4048878] using wordTrace_append hprefix tailTrace_4048878
  have hstable : (prefixWord ++ tailWord_4048878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048878).length < 2 ^ (prefixWord ++ tailWord_4048878).sum := by decide
  have hdescent : baseEnd_4048878 < baseStart_4048878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048935 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_4048935 : Nat := 118140960795 + 4048935 * 2 ^ 59
def prefixEnd_4048935 : Nat := 4983230072969 + 3 ^ 40 * 4048935 * 2
def baseEnd_4048935 : Nat := 2079049793812221256891793

theorem tailTrace_4048935 : CollatzResearch.WordTrace tailWord_4048935 prefixEnd_4048935 2079049793812221256891793 := by
  unfold tailWord_4048935
  simp only [CollatzResearch.WordTrace]
  refine ⟨147676791586407472889740259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98451194390938315259826839 147676791586407472889740259)
  ·
    refine ⟨221515187379611209334610389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147676791586407472889740259 221515187379611209334610389)
    ·
      refine ⟨5191762204209637718779931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 221515187379611209334610389 5191762204209637718779931)
      ·
        refine ⟨7787643306314456578169897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5191762204209637718779931 7787643306314456578169897)
        ·
          refine ⟨5840732479735842433627423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7787643306314456578169897 5840732479735842433627423)
          ·
            refine ⟨8761098719603763650441135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5840732479735842433627423 8761098719603763650441135)
            ·
              refine ⟨13141648079405645475661703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8761098719603763650441135 13141648079405645475661703)
              ·
                refine ⟨19712472119108468213492555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13141648079405645475661703 19712472119108468213492555)
                ·
                  refine ⟨29568708178662702320238833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19712472119108468213492555 29568708178662702320238833)
                  ·
                    refine ⟨22176531133997026740179125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29568708178662702320238833 22176531133997026740179125)
                    ·
                      refine ⟨2079049793812221256891793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22176531133997026740179125 2079049793812221256891793)
                      ·
                        rfl

theorem cell23_4048935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_4048935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048935 prefixEnd_4048935 := by exact prefixLift 4048935
  have htrace : WordTrace (prefixWord ++ tailWord_4048935) baseStart_4048935 baseEnd_4048935 := by
    simpa [prefixWord, tailWord_4048935, baseEnd_4048935] using wordTrace_append hprefix tailTrace_4048935
  have hstable : (prefixWord ++ tailWord_4048935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048935).length < 2 ^ (prefixWord ++ tailWord_4048935).sum := by decide
  have hdescent : baseEnd_4048935 < baseStart_4048935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048989 : List Nat := [1, 4, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_4048989 : Nat := 118140960795 + 4048989 * 2 ^ 59
def prefixEnd_4048989 : Nat := 4983230072969 + 3 ^ 40 * 4048989 * 2
def baseEnd_4048989 : Nat := 693025840589188015205515

theorem tailTrace_4048989 : CollatzResearch.WordTrace tailWord_4048989 prefixEnd_4048989 693025840589188015205515 := by
  unfold tailWord_4048989
  simp only [CollatzResearch.WordTrace]
  refine ⟨147678761128211840112206021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98452507418807893408137347 147678761128211840112206021)
  ·
    refine ⟨27689767711539720021038629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147678761128211840112206021 27689767711539720021038629)
    ·
      refine ⟨5191831445913697503944743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27689767711539720021038629 5191831445913697503944743)
      ·
        refine ⟨7787747168870546255917115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5191831445913697503944743 7787747168870546255917115)
        ·
          refine ⟨11681620753305819383875673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7787747168870546255917115 11681620753305819383875673)
          ·
            refine ⟨8761215564979364537906755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11681620753305819383875673 8761215564979364537906755)
            ·
              refine ⟨13141823347469046806860133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8761215564979364537906755 13141823347469046806860133)
              ·
                refine ⟨2464091877650446276286275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13141823347469046806860133 2464091877650446276286275)
                ·
                  refine ⟨3696137816475669414429413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464091877650446276286275 3696137816475669414429413)
                  ·
                    refine ⟨693025840589188015205515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3696137816475669414429413 693025840589188015205515)
                    ·
                      rfl

theorem cell23_4048989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_4048989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4048989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4048989 prefixEnd_4048989 := by exact prefixLift 4048989
  have htrace : WordTrace (prefixWord ++ tailWord_4048989) baseStart_4048989 baseEnd_4048989 := by
    simpa [prefixWord, tailWord_4048989, baseEnd_4048989] using wordTrace_append hprefix tailTrace_4048989
  have hstable : (prefixWord ++ tailWord_4048989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048989).length < 2 ^ (prefixWord ++ tailWord_4048989).sum := by decide
  have hdescent : baseEnd_4048989 < baseStart_4048989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049005 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_4049005 : Nat := 118140960795 + 4049005 * 2 ^ 59
def prefixEnd_4049005 : Nat := 4983230072969 + 3 ^ 40 * 4049005 * 2
def baseEnd_4049005 : Nat := 2079085737458035983016471

theorem tailTrace_4049005 : CollatzResearch.WordTrace tailWord_4049005 prefixEnd_4049005 2079085737458035983016471 := by
  unfold tailWord_4049005
  simp only [CollatzResearch.WordTrace]
  refine ⟨147679344696153874844788469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98452896464102583229858979 147679344696153874844788469)
  ·
    refine ⟨13844938565264425766698919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147679344696153874844788469 13844938565264425766698919)
    ·
      refine ⟨20767407847896638650048379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13844938565264425766698919 20767407847896638650048379)
      ·
        refine ⟨31151111771844957975072569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20767407847896638650048379 31151111771844957975072569)
        ·
          refine ⟨23363333828883718481304427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31151111771844957975072569 23363333828883718481304427)
          ·
            refine ⟨35045000743325577721956641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23363333828883718481304427 35045000743325577721956641)
            ·
              refine ⟨26283750557494183291467481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35045000743325577721956641 26283750557494183291467481)
              ·
                refine ⟨19712812918120637468600611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26283750557494183291467481 19712812918120637468600611)
                ·
                  refine ⟨29569219377180956202900917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19712812918120637468600611 29569219377180956202900917)
                  ·
                    refine ⟨2772114316610714644021961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29569219377180956202900917 2772114316610714644021961)
                    ·
                      refine ⟨2079085737458035983016471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2772114316610714644021961 2079085737458035983016471)
                      ·
                        rfl

theorem cell23_4049005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_4049005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049005 prefixEnd_4049005 := by exact prefixLift 4049005
  have htrace : WordTrace (prefixWord ++ tailWord_4049005) baseStart_4049005 baseEnd_4049005 := by
    simpa [prefixWord, tailWord_4049005, baseEnd_4049005] using wordTrace_append hprefix tailTrace_4049005
  have hstable : (prefixWord ++ tailWord_4049005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049005).length < 2 ^ (prefixWord ++ tailWord_4049005).sum := by decide
  have hdescent : baseEnd_4049005 < baseStart_4049005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049028 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_4049028 : Nat := 118140960795 + 4049028 * 2 ^ 59
def prefixEnd_4049028 : Nat := 4983230072969 + 3 ^ 40 * 4049028 * 2
def baseEnd_4049028 : Nat := 693032515837696464342955

theorem tailTrace_4049028 : CollatzResearch.WordTrace tailWord_4049028 prefixEnd_4049028 693032515837696464342955 := by
  unfold tailWord_4049028
  simp only [CollatzResearch.WordTrace]
  refine ⟨73840091787535274886437869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98453455716713699848583825 73840091787535274886437869)
  ·
    refine ⟨27690034420325728082414201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73840091787535274886437869 27690034420325728082414201)
    ·
      refine ⟨20767525815244296061810651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27690034420325728082414201 20767525815244296061810651)
      ·
        refine ⟨31151288722866444092715977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20767525815244296061810651 31151288722866444092715977)
        ·
          refine ⟨23363466542149833069536983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31151288722866444092715977 23363466542149833069536983)
          ·
            refine ⟨35045199813224749604305475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23363466542149833069536983 35045199813224749604305475)
            ·
              refine ⟨52567799719837124406458213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35045199813224749604305475 52567799719837124406458213)
              ·
                refine ⟨9856462447469460826210915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52567799719837124406458213 9856462447469460826210915)
                ·
                  refine ⟨14784693671204191239316373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9856462447469460826210915 14784693671204191239316373)
                  ·
                    refine ⟨693032515837696464342955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14784693671204191239316373 693032515837696464342955)
                    ·
                      rfl

theorem cell23_4049028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_4049028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049028 prefixEnd_4049028 := by exact prefixLift 4049028
  have htrace : WordTrace (prefixWord ++ tailWord_4049028) baseStart_4049028 baseEnd_4049028 := by
    simpa [prefixWord, tailWord_4049028, baseEnd_4049028] using wordTrace_append hprefix tailTrace_4049028
  have hstable : (prefixWord ++ tailWord_4049028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049028).length < 2 ^ (prefixWord ++ tailWord_4049028).sum := by decide
  have hdescent : baseEnd_4049028 < baseStart_4049028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049029 : List Nat := [1, 3, 1, 1, 5, 2, 2, 3, 1, 1, 3]
def baseStart_4049029 : Nat := 118140960795 + 4049029 * 2 ^ 59
def prefixEnd_4049029 : Nat := 4983230072969 + 3 ^ 40 * 4049029 * 2
def baseEnd_4049029 : Nat := 2079098060993743889116361

theorem tailTrace_4049029 : CollatzResearch.WordTrace tailWord_4049029 prefixEnd_4049029 2079098060993743889116361 := by
  unfold tailWord_4049029
  simp only [CollatzResearch.WordTrace]
  refine ⟨147680220048066926943662141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98453480032044617962441427 147680220048066926943662141)
  ·
    refine ⟨55380082518025097603873303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147680220048066926943662141 55380082518025097603873303)
    ·
      refine ⟨83070123777037646405809955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55380082518025097603873303 83070123777037646405809955)
      ·
        refine ⟨124605185665556469608714933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83070123777037646405809955 124605185665556469608714933)
        ·
          refine ⟨11681736156145919025817025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124605185665556469608714933 11681736156145919025817025)
          ·
            refine ⟨8761302117109439269362769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11681736156145919025817025 8761302117109439269362769)
            ·
              refine ⟨6570976587832079452022077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8761302117109439269362769 6570976587832079452022077)
              ·
                refine ⟨2464116220437029794508279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6570976587832079452022077 2464116220437029794508279)
                ·
                  refine ⟨3696174330655544691762419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464116220437029794508279 3696174330655544691762419)
                  ·
                    refine ⟨5544261495983317037643629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3696174330655544691762419 5544261495983317037643629)
                    ·
                      refine ⟨2079098060993743889116361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5544261495983317037643629 2079098060993743889116361)
                      ·
                        rfl

theorem cell23_4049029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 1, 1, 3].length) (baseStart_4049029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049029 prefixEnd_4049029 := by exact prefixLift 4049029
  have htrace : WordTrace (prefixWord ++ tailWord_4049029) baseStart_4049029 baseEnd_4049029 := by
    simpa [prefixWord, tailWord_4049029, baseEnd_4049029] using wordTrace_append hprefix tailTrace_4049029
  have hstable : (prefixWord ++ tailWord_4049029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049029).length < 2 ^ (prefixWord ++ tailWord_4049029).sum := by decide
  have hdescent : baseEnd_4049029 < baseStart_4049029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049032 : List Nat := [2, 1, 3, 4, 1, 1, 4, 1, 1, 5]
def baseStart_4049032 : Nat := 118140960795 + 4049032 * 2 ^ 59
def prefixEnd_4049032 : Nat := 4983230072969 + 3 ^ 40 * 4049032 * 2
def baseEnd_4049032 : Nat := 693033200478569125792949

theorem tailTrace_4049032 : CollatzResearch.WordTrace tailWord_4049032 prefixEnd_4049032 693033200478569125792949 := by
  unfold tailWord_4049032
  simp only [CollatzResearch.WordTrace]
  refine ⟨73840164733528029228010675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98453552978037372304014233 73840164733528029228010675)
  ·
    refine ⟨110760247100292043842016013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73840164733528029228010675 110760247100292043842016013)
    ·
      refine ⟨41535092662609516440756005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110760247100292043842016013 41535092662609516440756005)
      ·
        refine ⟨7787829874239284332641751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41535092662609516440756005 7787829874239284332641751)
        ·
          refine ⟨11681744811358926498962627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7787829874239284332641751 11681744811358926498962627)
          ·
            refine ⟨17522617217038389748443941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11681744811358926498962627 17522617217038389748443941)
            ·
              refine ⟨3285490728194698077833239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17522617217038389748443941 3285490728194698077833239)
              ·
                refine ⟨4928236092292047116749859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3285490728194698077833239 4928236092292047116749859)
                ·
                  refine ⟨7392354138438070675124789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4928236092292047116749859 7392354138438070675124789)
                  ·
                    refine ⟨693033200478569125792949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7392354138438070675124789 693033200478569125792949)
                    ·
                      rfl

theorem cell23_4049032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_4049032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049032 prefixEnd_4049032 := by exact prefixLift 4049032
  have htrace : WordTrace (prefixWord ++ tailWord_4049032) baseStart_4049032 baseEnd_4049032 := by
    simpa [prefixWord, tailWord_4049032, baseEnd_4049032] using wordTrace_append hprefix tailTrace_4049032
  have hstable : (prefixWord ++ tailWord_4049032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049032).length < 2 ^ (prefixWord ++ tailWord_4049032).sum := by decide
  have hdescent : baseEnd_4049032 < baseStart_4049032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049055 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4049055 : Nat := 118140960795 + 4049055 * 2 ^ 59
def prefixEnd_4049055 : Nat := 4983230072969 + 3 ^ 40 * 4049055 * 2
def baseEnd_4049055 : Nat := 2079111411490760787391241

theorem tailTrace_4049055 : CollatzResearch.WordTrace tailWord_4049055 prefixEnd_4049055 2079111411490760787391241 := by
  unfold tailWord_4049055
  simp only [CollatzResearch.WordTrace]
  refine ⟨147681168345972733384108619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98454112230648488922739079 147681168345972733384108619)
  ·
    refine ⟨221521752518959100076162929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147681168345972733384108619 221521752518959100076162929)
    ·
      refine ⟨166141314389219325057122197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221521752518959100076162929 166141314389219325057122197)
      ·
        refine ⟨7787874111994655862052603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166141314389219325057122197 7787874111994655862052603)
        ·
          refine ⟨11681811167991983793078905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7787874111994655862052603 11681811167991983793078905)
          ·
            refine ⟨8761358375993987844809179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11681811167991983793078905 8761358375993987844809179)
            ·
              refine ⟨13142037563990981767213769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8761358375993987844809179 13142037563990981767213769)
              ·
                refine ⟨9856528172993236325410327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13142037563990981767213769 9856528172993236325410327)
                ·
                  refine ⟨14784792259489854488115491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9856528172993236325410327 14784792259489854488115491)
                  ·
                    refine ⟨22177188389234781732173237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14784792259489854488115491 22177188389234781732173237)
                    ·
                      refine ⟨2079111411490760787391241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22177188389234781732173237 2079111411490760787391241)
                      ·
                        rfl

theorem cell23_4049055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4049055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049055 prefixEnd_4049055 := by exact prefixLift 4049055
  have htrace : WordTrace (prefixWord ++ tailWord_4049055) baseStart_4049055 baseEnd_4049055 := by
    simpa [prefixWord, tailWord_4049055, baseEnd_4049055] using wordTrace_append hprefix tailTrace_4049055
  have hstable : (prefixWord ++ tailWord_4049055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049055).length < 2 ^ (prefixWord ++ tailWord_4049055).sum := by decide
  have hdescent : baseEnd_4049055 < baseStart_4049055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049069 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_4049069 : Nat := 118140960795 + 4049069 * 2 ^ 59
def prefixEnd_4049069 : Nat := 4983230072969 + 3 ^ 40 * 4049069 * 2
def baseEnd_4049069 : Nat := 2079118600219923732616177

theorem tailTrace_4049069 : CollatzResearch.WordTrace tailWord_4049069 prefixEnd_4049069 2079118600219923732616177 := by
  unfold tailWord_4049069
  simp only [CollatzResearch.WordTrace]
  refine ⟨147681678967922013775118261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98454452645281342516745507 147681678967922013775118261)
  ·
    refine ⟨13845157403242688791417337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147681678967922013775118261 13845157403242688791417337)
    ·
      refine ⟨10383868052432016593563003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13845157403242688791417337 10383868052432016593563003)
      ·
        refine ⟨15575802078648024890344505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10383868052432016593563003 15575802078648024890344505)
        ·
          refine ⟨11681851558986018667758379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15575802078648024890344505 11681851558986018667758379)
          ·
            refine ⟨17522777338479028001637569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11681851558986018667758379 17522777338479028001637569)
            ·
              refine ⟨13142083003859271001228177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17522777338479028001637569 13142083003859271001228177)
              ·
                refine ⟨9856562252894453250921133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13142083003859271001228177 9856562252894453250921133)
                ·
                  refine ⟨3696210844835419969095425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9856562252894453250921133 3696210844835419969095425)
                  ·
                    refine ⟨2772158133626564976821569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3696210844835419969095425 2772158133626564976821569)
                    ·
                      refine ⟨2079118600219923732616177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2772158133626564976821569 2079118600219923732616177)
                      ·
                        rfl

theorem cell23_4049069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_4049069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049069 prefixEnd_4049069 := by exact prefixLift 4049069
  have htrace : WordTrace (prefixWord ++ tailWord_4049069) baseStart_4049069 baseEnd_4049069 := by
    simpa [prefixWord, tailWord_4049069, baseEnd_4049069] using wordTrace_append hprefix tailTrace_4049069
  have hstable : (prefixWord ++ tailWord_4049069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049069).length < 2 ^ (prefixWord ++ tailWord_4049069).sum := by decide
  have hdescent : baseEnd_4049069 < baseStart_4049069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049095 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 7, 3, 2]
def baseStart_4049095 : Nat := 118140960795 + 4049095 * 2 ^ 59
def prefixEnd_4049095 : Nat := 4983230072969 + 3 ^ 40 * 4049095 * 2
def baseEnd_4049095 : Nat := 2079131950716940630891057

theorem tailTrace_4049095 : CollatzResearch.WordTrace tailWord_4049095 prefixEnd_4049095 2079131950716940630891057 := by
  unfold tailWord_4049095
  simp only [CollatzResearch.WordTrace]
  refine ⟨147682627265827820215564739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98455084843885213477043159 147682627265827820215564739)
  ·
    refine ⟨221523940898741730323347109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147682627265827820215564739 221523940898741730323347109)
    ·
      refine ⟨41535738918514074435627583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221523940898741730323347109 41535738918514074435627583)
      ·
        refine ⟨62303608377771111653441375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41535738918514074435627583 62303608377771111653441375)
        ·
          refine ⟨93455412566656667480162063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62303608377771111653441375 93455412566656667480162063)
          ·
            refine ⟨140183118849985001220243095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93455412566656667480162063 140183118849985001220243095)
            ·
              refine ⟨210274678274977501830364643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140183118849985001220243095 210274678274977501830364643)
              ·
                refine ⟨315412017412466252745546965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210274678274977501830364643 315412017412466252745546965)
                ·
                  refine ⟨7392469158104677798723757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 315412017412466252745546965 7392469158104677798723757)
                  ·
                    refine ⟨2772175934289254174521409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7392469158104677798723757 2772175934289254174521409)
                    ·
                      refine ⟨2079131950716940630891057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2772175934289254174521409 2079131950716940630891057)
                      ·
                        rfl

theorem cell23_4049095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_4049095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049095 prefixEnd_4049095 := by exact prefixLift 4049095
  have htrace : WordTrace (prefixWord ++ tailWord_4049095) baseStart_4049095 baseEnd_4049095 := by
    simpa [prefixWord, tailWord_4049095, baseEnd_4049095] using wordTrace_append hprefix tailTrace_4049095
  have hstable : (prefixWord ++ tailWord_4049095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049095).length < 2 ^ (prefixWord ++ tailWord_4049095).sum := by decide
  have hdescent : baseEnd_4049095 < baseStart_4049095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049098 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_4049098 : Nat := 118140960795 + 4049098 * 2 ^ 59
def prefixEnd_4049098 : Nat := 4983230072969 + 3 ^ 40 * 4049098 * 2
def baseEnd_4049098 : Nat := 2079133491158904119153543

theorem tailTrace_4049098 : CollatzResearch.WordTrace tailWord_4049098 prefixEnd_4049098 2079133491158904119153543 := by
  unfold tailWord_4049098
  simp only [CollatzResearch.WordTrace]
  refine ⟨36920684171204237931980987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98455157789877967818615965 36920684171204237931980987)
  ·
    refine ⟨55381026256806356897971481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36920684171204237931980987 55381026256806356897971481)
    ·
      refine ⟨41535769692604767673478611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55381026256806356897971481 41535769692604767673478611)
      ·
        refine ⟨62303654538907151510217917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41535769692604767673478611 62303654538907151510217917)
        ·
          refine ⟨23363870452090181816331719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62303654538907151510217917 23363870452090181816331719)
          ·
            refine ⟨35045805678135272724497579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23363870452090181816331719 35045805678135272724497579)
            ·
              refine ⟨52568708517202909086746369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35045805678135272724497579 52568708517202909086746369)
              ·
                refine ⟨39426531387902181815059777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52568708517202909086746369 39426531387902181815059777)
                ·
                  refine ⟨29569898540926636361294833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39426531387902181815059777 29569898540926636361294833)
                  ·
                    refine ⟨22177423905694977270971125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29569898540926636361294833 22177423905694977270971125)
                    ·
                      refine ⟨2079133491158904119153543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22177423905694977270971125 2079133491158904119153543)
                      ·
                        rfl

theorem cell23_4049098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_4049098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049098 prefixEnd_4049098 := by exact prefixLift 4049098
  have htrace : WordTrace (prefixWord ++ tailWord_4049098) baseStart_4049098 baseEnd_4049098 := by
    simpa [prefixWord, tailWord_4049098, baseEnd_4049098] using wordTrace_append hprefix tailTrace_4049098
  have hstable : (prefixWord ++ tailWord_4049098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049098).length < 2 ^ (prefixWord ++ tailWord_4049098).sum := by decide
  have hdescent : baseEnd_4049098 < baseStart_4049098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049102 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_4049102 : Nat := 118140960795 + 4049102 * 2 ^ 59
def prefixEnd_4049102 : Nat := 4983230072969 + 3 ^ 40 * 4049102 * 2
def baseEnd_4049102 : Nat := 2079135545081522103503525

theorem tailTrace_4049102 : CollatzResearch.WordTrace tailWord_4049102 prefixEnd_4049102 2079135545081522103503525 := by
  unfold tailWord_4049102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18460360322100307551383695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98455255051201640274046373 18460360322100307551383695)
  ·
    refine ⟨27690540483150461327075543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18460360322100307551383695 27690540483150461327075543)
    ·
      refine ⟨41535810724725691990613315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27690540483150461327075543 41535810724725691990613315)
      ·
        refine ⟨62303716087088537985919973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41535810724725691990613315 62303716087088537985919973)
        ·
          refine ⟨11681946766329100872359995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62303716087088537985919973 11681946766329100872359995)
          ·
            refine ⟨17522920149493651308539993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11681946766329100872359995 17522920149493651308539993)
            ·
              refine ⟨13142190112120238481404995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17522920149493651308539993 13142190112120238481404995)
              ·
                refine ⟨19713285168180357722107493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13142190112120238481404995 19713285168180357722107493)
                ·
                  refine ⟨3696240969033817072895155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19713285168180357722107493 3696240969033817072895155)
                  ·
                    refine ⟨5544361453550725609342733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3696240969033817072895155 5544361453550725609342733)
                    ·
                      refine ⟨2079135545081522103503525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5544361453550725609342733 2079135545081522103503525)
                      ·
                        rfl

theorem cell23_4049102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_4049102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049102 prefixEnd_4049102 := by exact prefixLift 4049102
  have htrace : WordTrace (prefixWord ++ tailWord_4049102) baseStart_4049102 baseEnd_4049102 := by
    simpa [prefixWord, tailWord_4049102, baseEnd_4049102] using wordTrace_append hprefix tailTrace_4049102
  have hstable : (prefixWord ++ tailWord_4049102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049102).length < 2 ^ (prefixWord ++ tailWord_4049102).sum := by decide
  have hdescent : baseEnd_4049102 < baseStart_4049102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049142 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_4049142 : Nat := 118140960795 + 4049142 * 2 ^ 59
def prefixEnd_4049142 : Nat := 4983230072969 + 3 ^ 40 * 4049142 * 2
def baseEnd_4049142 : Nat := 2079156084307701947003341

theorem tailTrace_4049142 : CollatzResearch.WordTrace tailWord_4049142 prefixEnd_4049142 2079156084307701947003341 := by
  unfold tailWord_4049142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9230271343541096702657855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98456227664438364828350453 9230271343541096702657855)
  ·
    refine ⟨13845407015311645053986783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9230271343541096702657855 13845407015311645053986783)
    ·
      refine ⟨20768110522967467580980175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13845407015311645053986783 20768110522967467580980175)
      ·
        refine ⟨31152165784451201371470263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20768110522967467580980175 31152165784451201371470263)
        ·
          refine ⟨46728248676676802057205395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31152165784451201371470263 46728248676676802057205395)
          ·
            refine ⟨70092373015015203085808093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46728248676676802057205395 70092373015015203085808093)
            ·
              refine ⟨26284639880630701157178035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70092373015015203085808093 26284639880630701157178035)
              ·
                refine ⟨39426959820946051735767053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26284639880630701157178035 39426959820946051735767053)
                ·
                  refine ⟨14785109932854769400912645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39426959820946051735767053 14785109932854769400912645)
                  ·
                    refine ⟨2772208112410269262671121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14785109932854769400912645 2772208112410269262671121)
                    ·
                      refine ⟨2079156084307701947003341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2772208112410269262671121 2079156084307701947003341)
                      ·
                        rfl

theorem cell23_4049142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_4049142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049142 prefixEnd_4049142 := by exact prefixLift 4049142
  have htrace : WordTrace (prefixWord ++ tailWord_4049142) baseStart_4049142 baseEnd_4049142 := by
    simpa [prefixWord, tailWord_4049142, baseEnd_4049142] using wordTrace_append hprefix tailTrace_4049142
  have hstable : (prefixWord ++ tailWord_4049142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049142).length < 2 ^ (prefixWord ++ tailWord_4049142).sum := by decide
  have hdescent : baseEnd_4049142 < baseStart_4049142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049175 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 3]
def baseStart_4049175 : Nat := 118140960795 + 4049175 * 2 ^ 59
def prefixEnd_4049175 : Nat := 4983230072969 + 3 ^ 40 * 4049175 * 2
def baseEnd_4049175 : Nat := 2079173029169300317890689

theorem tailTrace_4049175 : CollatzResearch.WordTrace tailWord_4049175 prefixEnd_4049175 2079173029169300317890689 := by
  unfold tailWord_4049175
  simp only [CollatzResearch.WordTrace]
  refine ⟨147685545105537993878476979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98457030070358662585651319 147685545105537993878476979)
  ·
    refine ⟨221528317658306990817715469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147685545105537993878476979 221528317658306990817715469)
    ·
      refine ⟨83073119121865121556643301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221528317658306990817715469 83073119121865121556643301)
      ·
        refine ⟨15576209835349710291870619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83073119121865121556643301 15576209835349710291870619)
        ·
          refine ⟨23364314753024565437805929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15576209835349710291870619 23364314753024565437805929)
          ·
            refine ⟨17523236064768424078354447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23364314753024565437805929 17523236064768424078354447)
            ·
              refine ⟨26284854097152636117531671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17523236064768424078354447 26284854097152636117531671)
              ·
                refine ⟨39427281145728954176297507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26284854097152636117531671 39427281145728954176297507)
                ·
                  refine ⟨59140921718593431264446261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39427281145728954176297507 59140921718593431264446261)
                  ·
                    refine ⟨5544461411118134181041837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59140921718593431264446261 5544461411118134181041837)
                    ·
                      refine ⟨2079173029169300317890689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5544461411118134181041837 2079173029169300317890689)
                      ·
                        rfl

theorem cell23_4049175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_4049175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049175 prefixEnd_4049175 := by exact prefixLift 4049175
  have htrace : WordTrace (prefixWord ++ tailWord_4049175) baseStart_4049175 baseEnd_4049175 := by
    simpa [prefixWord, tailWord_4049175, baseEnd_4049175] using wordTrace_append hprefix tailTrace_4049175
  have hstable : (prefixWord ++ tailWord_4049175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049175).length < 2 ^ (prefixWord ++ tailWord_4049175).sum := by decide
  have hdescent : baseEnd_4049175 < baseStart_4049175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049182 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 9]
def baseStart_4049182 : Nat := 118140960795 + 4049182 * 2 ^ 59
def prefixEnd_4049182 : Nat := 4983230072969 + 3 ^ 40 * 4049182 * 2
def baseEnd_4049182 : Nat := 231019624837097976722573

theorem tailTrace_4049182 : CollatzResearch.WordTrace tailWord_4049182 prefixEnd_4049182 231019624837097976722573 := by
  unfold tailWord_4049182
  simp only [CollatzResearch.WordTrace]
  refine ⟨18460725052064079259247725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98457200277675089382654533 18460725052064079259247725)
  ·
    refine ⟨6922771894524029722217897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18460725052064079259247725 6922771894524029722217897)
    ·
      refine ⟨5192078920893022291663423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6922771894524029722217897 5192078920893022291663423)
      ·
        refine ⟨7788118381339533437495135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5192078920893022291663423 7788118381339533437495135)
        ·
          refine ⟨11682177572009300156242703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7788118381339533437495135 11682177572009300156242703)
          ·
            refine ⟨17523266358013950234364055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11682177572009300156242703 17523266358013950234364055)
            ·
              refine ⟨26284899537020925351546083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17523266358013950234364055 26284899537020925351546083)
              ·
                refine ⟨39427349305531388027319125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26284899537020925351546083 39427349305531388027319125)
                ·
                  refine ⟨231019624837097976722573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39427349305531388027319125 231019624837097976722573)
                  ·
                    rfl

theorem cell23_4049182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_4049182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049182 prefixEnd_4049182 := by exact prefixLift 4049182
  have htrace : WordTrace (prefixWord ++ tailWord_4049182) baseStart_4049182 baseEnd_4049182 := by
    simpa [prefixWord, tailWord_4049182, baseEnd_4049182] using wordTrace_append hprefix tailTrace_4049182
  have hstable : (prefixWord ++ tailWord_4049182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049182).length < 2 ^ (prefixWord ++ tailWord_4049182).sum := by decide
  have hdescent : baseEnd_4049182 < baseStart_4049182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049215 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 4]
def baseStart_4049215 : Nat := 118140960795 + 4049215 * 2 ^ 59
def prefixEnd_4049215 : Nat := 4983230072969 + 3 ^ 40 * 4049215 * 2
def baseEnd_4049215 : Nat := 2079193568395480161390505

theorem tailTrace_4049215 : CollatzResearch.WordTrace tailWord_4049215 prefixEnd_4049215 2079193568395480161390505 := by
  unfold tailWord_4049215
  simp only [CollatzResearch.WordTrace]
  refine ⟨147687004025393080709933099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98458002683595387139955399 147687004025393080709933099)
  ·
    refine ⟨221530506038089621064899649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147687004025393080709933099 221530506038089621064899649)
    ·
      refine ⟨166147879528567215798674737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221530506038089621064899649 166147879528567215798674737)
      ·
        refine ⟨124610909646425411849006053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166147879528567215798674737 124610909646425411849006053)
        ·
          refine ⟨23364545558704764721688635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124610909646425411849006053 23364545558704764721688635)
          ·
            refine ⟨35046818338057147082532953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23364545558704764721688635 35046818338057147082532953)
            ·
              refine ⟨26285113753542860311899715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35046818338057147082532953 26285113753542860311899715)
              ·
                refine ⟨39427670630314290467849573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26285113753542860311899715 39427670630314290467849573)
                ·
                  refine ⟨7392688243183929462721795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39427670630314290467849573 7392688243183929462721795)
                  ·
                    refine ⟨11089032364775894194082693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7392688243183929462721795 11089032364775894194082693)
                    ·
                      refine ⟨2079193568395480161390505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11089032364775894194082693 2079193568395480161390505)
                      ·
                        rfl

theorem cell23_4049215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_4049215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049215 prefixEnd_4049215 := by exact prefixLift 4049215
  have htrace : WordTrace (prefixWord ++ tailWord_4049215) baseStart_4049215 baseEnd_4049215 := by
    simpa [prefixWord, tailWord_4049215, baseEnd_4049215] using wordTrace_append hprefix tailTrace_4049215
  have hstable : (prefixWord ++ tailWord_4049215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049215).length < 2 ^ (prefixWord ++ tailWord_4049215).sum := by decide
  have hdescent : baseEnd_4049215 < baseStart_4049215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049232 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 2, 4, 2]
def baseStart_4049232 : Nat := 118140960795 + 4049232 * 2 ^ 59
def prefixEnd_4049232 : Nat := 4983230072969 + 3 ^ 40 * 4049232 * 2
def baseEnd_4049232 : Nat := 2079202297566606594877927

theorem tailTrace_4049232 : CollatzResearch.WordTrace tailWord_4049232 prefixEnd_4049232 2079202297566606594877927 := by
  unfold tailWord_4049232
  simp only [CollatzResearch.WordTrace]
  refine ⟨73843812033165746306650975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98458416044220995075534633 73843812033165746306650975)
  ·
    refine ⟨110765718049748619459976463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73843812033165746306650975 110765718049748619459976463)
    ·
      refine ⟨166148577074622929189964695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110765718049748619459976463 166148577074622929189964695)
      ·
        refine ⟨249222865611934393784947043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166148577074622929189964695 249222865611934393784947043)
        ·
          refine ⟨373834298417901590677420565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249222865611934393784947043 373834298417901590677420565)
          ·
            refine ⟨17523482738339137063004089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 373834298417901590677420565 17523482738339137063004089)
            ·
              refine ⟨13142612053754352797253067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17523482738339137063004089 13142612053754352797253067)
              ·
                refine ⟨19713918080631529195879601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13142612053754352797253067 19713918080631529195879601)
                ·
                  refine ⟨14785438560473646896909701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19713918080631529195879601 14785438560473646896909701)
                  ·
                    refine ⟨2772269730088808793170569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14785438560473646896909701 2772269730088808793170569)
                    ·
                      refine ⟨2079202297566606594877927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2772269730088808793170569 2079202297566606594877927)
                      ·
                        rfl

theorem cell23_4049232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 4, 2].length) (baseStart_4049232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049232 prefixEnd_4049232 := by exact prefixLift 4049232
  have htrace : WordTrace (prefixWord ++ tailWord_4049232) baseStart_4049232 baseEnd_4049232 := by
    simpa [prefixWord, tailWord_4049232, baseEnd_4049232] using wordTrace_append hprefix tailTrace_4049232
  have hstable : (prefixWord ++ tailWord_4049232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049232).length < 2 ^ (prefixWord ++ tailWord_4049232).sum := by decide
  have hdescent : baseEnd_4049232 < baseStart_4049232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049235 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 3]
def baseStart_4049235 : Nat := 118140960795 + 4049235 * 2 ^ 59
def prefixEnd_4049235 : Nat := 4983230072969 + 3 ^ 40 * 4049235 * 2
def baseEnd_4049235 : Nat := 2079203838008570083140413

theorem tailTrace_4049235 : CollatzResearch.WordTrace tailWord_4049235 prefixEnd_4049235 2079203838008570083140413 := by
  unfold tailWord_4049235
  simp only [CollatzResearch.WordTrace]
  refine ⟨147687733485320624125661159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98458488990213749417107439 147687733485320624125661159)
  ·
    refine ⟨221531600227980936188491739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147687733485320624125661159 221531600227980936188491739)
    ·
      refine ⟨332297400341971404282737609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221531600227980936188491739 332297400341971404282737609)
      ·
        refine ⟨249223050256478553212053207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332297400341971404282737609 249223050256478553212053207)
        ·
          refine ⟨373834575384717829818079811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249223050256478553212053207 373834575384717829818079811)
          ·
            refine ⟨560751863077076744727119717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373834575384717829818079811 560751863077076744727119717)
            ·
              refine ⟨105140974326951889636334947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 560751863077076744727119717 105140974326951889636334947)
              ·
                refine ⟨157711461490427834454502421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105140974326951889636334947 157711461490427834454502421)
                ·
                  refine ⟨7392724757363804740054801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157711461490427834454502421 7392724757363804740054801)
                  ·
                    refine ⟨5544543568022853555041101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7392724757363804740054801 5544543568022853555041101)
                    ·
                      refine ⟨2079203838008570083140413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5544543568022853555041101 2079203838008570083140413)
                      ·
                        rfl

theorem cell23_4049235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 3].length) (baseStart_4049235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049235 prefixEnd_4049235 := by exact prefixLift 4049235
  have htrace : WordTrace (prefixWord ++ tailWord_4049235) baseStart_4049235 baseEnd_4049235 := by
    simpa [prefixWord, tailWord_4049235, baseEnd_4049235] using wordTrace_append hprefix tailTrace_4049235
  have hstable : (prefixWord ++ tailWord_4049235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049235).length < 2 ^ (prefixWord ++ tailWord_4049235).sum := by decide
  have hdescent : baseEnd_4049235 < baseStart_4049235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049252 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_4049252 : Nat := 118140960795 + 4049252 * 2 ^ 59
def prefixEnd_4049252 : Nat := 4983230072969 + 3 ^ 40 * 4049252 * 2
def baseEnd_4049252 : Nat := 2079212567179696516627835

theorem tailTrace_4049252 : CollatzResearch.WordTrace tailWord_4049252 prefixEnd_4049252 2079212567179696516627835 := by
  unfold tailWord_4049252
  simp only [CollatzResearch.WordTrace]
  refine ⟨73844176763129518014515005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98458902350839357352686673 73844176763129518014515005)
  ·
    refine ⟨27691566286173569255443127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73844176763129518014515005 27691566286173569255443127)
    ·
      refine ⟨41537349429260353883164691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27691566286173569255443127 41537349429260353883164691)
      ·
        refine ⟨62306024143890530824747037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41537349429260353883164691 62306024143890530824747037)
        ·
          refine ⟨23364759053958949059280139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62306024143890530824747037 23364759053958949059280139)
          ·
            refine ⟨35047138580938423588920209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23364759053958949059280139 35047138580938423588920209)
            ·
              refine ⟨26285353935703817691690157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35047138580938423588920209 26285353935703817691690157)
              ·
                refine ⟨9857007725888931634383809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26285353935703817691690157 9857007725888931634383809)
                ·
                  refine ⟨7392755794416698725787857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9857007725888931634383809 7392755794416698725787857)
                  ·
                    refine ⟨5544566845812524044340893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7392755794416698725787857 5544566845812524044340893)
                    ·
                      refine ⟨2079212567179696516627835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5544566845812524044340893 2079212567179696516627835)
                      ·
                        rfl

theorem cell23_4049252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_4049252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049252 prefixEnd_4049252 := by exact prefixLift 4049252
  have htrace : WordTrace (prefixWord ++ tailWord_4049252) baseStart_4049252 baseEnd_4049252 := by
    simpa [prefixWord, tailWord_4049252, baseEnd_4049252] using wordTrace_append hprefix tailTrace_4049252
  have hstable : (prefixWord ++ tailWord_4049252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049252).length < 2 ^ (prefixWord ++ tailWord_4049252).sum := by decide
  have hdescent : baseEnd_4049252 < baseStart_4049252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049255 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 8]
def baseStart_4049255 : Nat := 118140960795 + 4049255 * 2 ^ 59
def prefixEnd_4049255 : Nat := 4983230072969 + 3 ^ 40 * 4049255 * 2
def baseEnd_4049255 : Nat := 231023789735740000543369

theorem tailTrace_4049255 : CollatzResearch.WordTrace tailWord_4049255 prefixEnd_4049255 231023789735740000543369 := by
  unfold tailWord_4049255
  simp only [CollatzResearch.WordTrace]
  refine ⟨147688462945248167541389219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98458975296832111694259479 147688462945248167541389219)
  ·
    refine ⟨221532694417872251312083829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147688462945248167541389219 221532694417872251312083829)
    ·
      refine ⟨20768690101675523560507859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221532694417872251312083829 20768690101675523560507859)
      ·
        refine ⟨31153035152513285340761789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20768690101675523560507859 31153035152513285340761789)
        ·
          refine ⟨11682388182192482002785671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31153035152513285340761789 11682388182192482002785671)
          ·
            refine ⟨17523582273288723004178507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11682388182192482002785671 17523582273288723004178507)
            ·
              refine ⟨26285373409933084506267761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17523582273288723004178507 26285373409933084506267761)
              ·
                refine ⟨19714030057449813379700821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26285373409933084506267761 19714030057449813379700821)
                ·
                  refine ⟨231023789735740000543369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19714030057449813379700821 231023789735740000543369)
                  ·
                    rfl

theorem cell23_4049255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 8].length) (baseStart_4049255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049255 prefixEnd_4049255 := by exact prefixLift 4049255
  have htrace : WordTrace (prefixWord ++ tailWord_4049255) baseStart_4049255 baseEnd_4049255 := by
    simpa [prefixWord, tailWord_4049255, baseEnd_4049255] using wordTrace_append hprefix tailTrace_4049255
  have hstable : (prefixWord ++ tailWord_4049255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049255).length < 2 ^ (prefixWord ++ tailWord_4049255).sum := by decide
  have hdescent : baseEnd_4049255 < baseStart_4049255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049269 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_4049269 : Nat := 118140960795 + 4049269 * 2 ^ 59
def prefixEnd_4049269 : Nat := 4983230072969 + 3 ^ 40 * 4049269 * 2
def baseEnd_4049269 : Nat := 2079221296350822950115257

theorem tailTrace_4049269 : CollatzResearch.WordTrace tailWord_4049269 prefixEnd_4049269 2079221296350822950115257 := by
  unfold tailWord_4049269
  simp only [CollatzResearch.WordTrace]
  refine ⟨147688973567197447932398861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98459315711464965288265907 147688973567197447932398861)
  ·
    refine ⟨55383365087699042974649573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147688973567197447932398861 55383365087699042974649573)
    ·
      refine ⟨10384380953943570557746795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55383365087699042974649573 10384380953943570557746795)
      ·
        refine ⟨15576571430915355836620193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10384380953943570557746795 15576571430915355836620193)
        ·
          refine ⟨11682428573186516877465145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15576571430915355836620193 11682428573186516877465145)
          ·
            refine ⟨8761821429889887658098859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11682428573186516877465145 8761821429889887658098859)
            ·
              refine ⟨13142732144834831487148289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8761821429889887658098859 13142732144834831487148289)
              ·
                refine ⟨9857049108626123615361217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13142732144834831487148289 9857049108626123615361217)
                ·
                  refine ⟨7392786831469592711520913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9857049108626123615361217 7392786831469592711520913)
                  ·
                    refine ⟨5544590123602194533640685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7392786831469592711520913 5544590123602194533640685)
                    ·
                      refine ⟨2079221296350822950115257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5544590123602194533640685 2079221296350822950115257)
                      ·
                        rfl

theorem cell23_4049269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_4049269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049269 prefixEnd_4049269 := by exact prefixLift 4049269
  have htrace : WordTrace (prefixWord ++ tailWord_4049269) baseStart_4049269 baseEnd_4049269 := by
    simpa [prefixWord, tailWord_4049269, baseEnd_4049269] using wordTrace_append hprefix tailTrace_4049269
  have hstable : (prefixWord ++ tailWord_4049269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049269).length < 2 ^ (prefixWord ++ tailWord_4049269).sum := by decide
  have hdescent : baseEnd_4049269 < baseStart_4049269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049285 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 3, 5]
def baseStart_4049285 : Nat := 118140960795 + 4049285 * 2 ^ 59
def prefixEnd_4049285 : Nat := 4983230072969 + 3 ^ 40 * 4049285 * 2
def baseEnd_4049285 : Nat := 693076504013764962505061

theorem tailTrace_4049285 : CollatzResearch.WordTrace tailWord_4049285 prefixEnd_4049285 693076504013764962505061 := by
  unfold tailWord_4049285
  simp only [CollatzResearch.WordTrace]
  refine ⟨147689557135139482664981309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98459704756759655109987539 147689557135139482664981309)
  ·
    refine ⟨55383583925677305999367991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147689557135139482664981309 55383583925677305999367991)
    ·
      refine ⟨83075375888515958999051987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55383583925677305999367991 83075375888515958999051987)
      ·
        refine ⟨124613063832773938498577981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83075375888515958999051987 124613063832773938498577981)
        ·
          refine ⟨46729898937290226936966743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124613063832773938498577981 46729898937290226936966743)
          ·
            refine ⟨70094848405935340405450115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46729898937290226936966743 70094848405935340405450115)
            ·
              refine ⟨105142272608903010608175173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70094848405935340405450115 105142272608903010608175173)
              ·
                refine ⟨19714176114169314489032845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105142272608903010608175173 19714176114169314489032845)
                ·
                  refine ⟨7392816042813492933387317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19714176114169314489032845 7392816042813492933387317)
                  ·
                    refine ⟨693076504013764962505061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7392816042813492933387317 693076504013764962505061)
                    ·
                      rfl

theorem cell23_4049285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_4049285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049285 prefixEnd_4049285 := by exact prefixLift 4049285
  have htrace : WordTrace (prefixWord ++ tailWord_4049285) baseStart_4049285 baseEnd_4049285 := by
    simpa [prefixWord, tailWord_4049285, baseEnd_4049285] using wordTrace_append hprefix tailTrace_4049285
  have hstable : (prefixWord ++ tailWord_4049285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049285).length < 2 ^ (prefixWord ++ tailWord_4049285).sum := by decide
  have hdescent : baseEnd_4049285 < baseStart_4049285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049289 : List Nat := [1, 2, 1, 1, 6, 3, 2, 1, 6]
def baseStart_4049289 : Nat := 118140960795 + 4049289 * 2 ^ 59
def prefixEnd_4049289 : Nat := 4983230072969 + 3 ^ 40 * 4049289 * 2
def baseEnd_4049289 : Nat := 231025729551545874651685

theorem tailTrace_4049289 : CollatzResearch.WordTrace tailWord_4049289 prefixEnd_4049289 231025729551545874651685 := by
  unfold tailWord_4049289
  simp only [CollatzResearch.WordTrace]
  refine ⟨147689703027124991348126921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98459802018083327565417947 147689703027124991348126921)
  ·
    refine ⟨110767277270343743511095191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147689703027124991348126921 110767277270343743511095191)
    ·
      refine ⟨166150915905515615266642787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110767277270343743511095191 166150915905515615266642787)
      ·
        refine ⟨249226373858273422899964181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166150915905515615266642787 249226373858273422899964181)
        ·
          refine ⟨11682486274606566698435821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 249226373858273422899964181 11682486274606566698435821)
          ·
            refine ⟨4380932352977462511913433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11682486274606566698435821 4380932352977462511913433)
            ·
              refine ⟨3285699264733096883935075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4380932352977462511913433 3285699264733096883935075)
              ·
                refine ⟨4928548897099645325902613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3285699264733096883935075 4928548897099645325902613)
                ·
                  refine ⟨231025729551545874651685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4928548897099645325902613 231025729551545874651685)
                  ·
                    rfl

theorem cell23_4049289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 6].length) (baseStart_4049289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049289 prefixEnd_4049289 := by exact prefixLift 4049289
  have htrace : WordTrace (prefixWord ++ tailWord_4049289) baseStart_4049289 baseEnd_4049289 := by
    simpa [prefixWord, tailWord_4049289, baseEnd_4049289] using wordTrace_append hprefix tailTrace_4049289
  have hstable : (prefixWord ++ tailWord_4049289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049289).length < 2 ^ (prefixWord ++ tailWord_4049289).sum := by decide
  have hdescent : baseEnd_4049289 < baseStart_4049289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049315 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 3, 6]
def baseStart_4049315 : Nat := 118140960795 + 4049315 * 2 ^ 59
def prefixEnd_4049315 : Nat := 4983230072969 + 3 ^ 40 * 4049315 * 2
def baseEnd_4049315 : Nat := 693081638820309923380015

theorem tailTrace_4049315 : CollatzResearch.WordTrace tailWord_4049315 prefixEnd_4049315 693081638820309923380015 := by
  unfold tailWord_4049315
  simp only [CollatzResearch.WordTrace]
  refine ⟨147690651325030797788573399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98460434216687198525715599 147690651325030797788573399)
  ·
    refine ⟨221535976987546196682860099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147690651325030797788573399 221535976987546196682860099)
    ·
      refine ⟨332303965481319295024290149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221535976987546196682860099 332303965481319295024290149)
      ·
        refine ⟨62306993527747367817054403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332303965481319295024290149 62306993527747367817054403)
        ·
          refine ⟨93460490291621051725581605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62306993527747367817054403 93460490291621051725581605)
          ·
            refine ⟨17523841929678947198546551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93460490291621051725581605 17523841929678947198546551)
            ·
              refine ⟨26285762894518420797819827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17523841929678947198546551 26285762894518420797819827)
              ·
                refine ⟨39428644341777631196729741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26285762894518420797819827 39428644341777631196729741)
                ·
                  refine ⟨14785741628166611698773653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39428644341777631196729741 14785741628166611698773653)
                  ·
                    refine ⟨693081638820309923380015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14785741628166611698773653 693081638820309923380015)
                    ·
                      rfl

theorem cell23_4049315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 6].length) (baseStart_4049315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049315 prefixEnd_4049315 := by exact prefixLift 4049315
  have htrace : WordTrace (prefixWord ++ tailWord_4049315) baseStart_4049315 baseEnd_4049315 := by
    simpa [prefixWord, tailWord_4049315, baseEnd_4049315] using wordTrace_append hprefix tailTrace_4049315
  have hstable : (prefixWord ++ tailWord_4049315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049315).length < 2 ^ (prefixWord ++ tailWord_4049315).sum := by decide
  have hdescent : baseEnd_4049315 < baseStart_4049315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049333 : List Nat := [1, 3, 3, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_4049333 : Nat := 118140960795 + 4049333 * 2 ^ 59
def prefixEnd_4049333 : Nat := 4983230072969 + 3 ^ 40 * 4049333 * 2
def baseEnd_4049333 : Nat := 2079254159112710699714963

theorem tailTrace_4049333 : CollatzResearch.WordTrace tailWord_4049333 prefixEnd_4049333 2079254159112710699714963 := by
  unfold tailWord_4049333
  simp only [CollatzResearch.WordTrace]
  refine ⟨147691307838965586862728653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98460871892643724575152435 147691307838965586862728653)
  ·
    refine ⟨55384240439612095073523245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147691307838965586862728653 55384240439612095073523245)
    ·
      refine ⟨20769090164854535652571217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55384240439612095073523245 20769090164854535652571217)
      ·
        refine ⟨15576817623640901739428413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20769090164854535652571217 15576817623640901739428413)
        ·
          refine ⟨5841306608865338152285655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15576817623640901739428413 5841306608865338152285655)
          ·
            refine ⟨8761959913298007228428483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841306608865338152285655 8761959913298007228428483)
            ·
              refine ⟨13142939869947010842642725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8761959913298007228428483 13142939869947010842642725)
              ·
                refine ⟨2464301225615064532995511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13142939869947010842642725 2464301225615064532995511)
                ·
                  refine ⟨3696451838422596799493267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464301225615064532995511 3696451838422596799493267)
                  ·
                    refine ⟨5544677757633895199239901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3696451838422596799493267 5544677757633895199239901)
                    ·
                      refine ⟨2079254159112710699714963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5544677757633895199239901 2079254159112710699714963)
                      ·
                        rfl

theorem cell23_4049333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_4049333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049333 prefixEnd_4049333 := by exact prefixLift 4049333
  have htrace : WordTrace (prefixWord ++ tailWord_4049333) baseStart_4049333 baseEnd_4049333 := by
    simpa [prefixWord, tailWord_4049333, baseEnd_4049333] using wordTrace_append hprefix tailTrace_4049333
  have hstable : (prefixWord ++ tailWord_4049333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049333).length < 2 ^ (prefixWord ++ tailWord_4049333).sum := by decide
  have hdescent : baseEnd_4049333 < baseStart_4049333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049342 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_4049342 : Nat := 118140960795 + 4049342 * 2 ^ 59
def prefixEnd_4049342 : Nat := 4983230072969 + 3 ^ 40 * 4049342 * 2
def baseEnd_4049342 : Nat := 2079258780438601164502421

theorem tailTrace_4049342 : CollatzResearch.WordTrace tailWord_4049342 prefixEnd_4049342 2079258780438601164502421 := by
  unfold tailWord_4049342
  simp only [CollatzResearch.WordTrace]
  refine ⟨18461454511991622674975785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98461090730621987599870853 18461454511991622674975785)
  ·
    refine ⟨13846090883993717006231839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18461454511991622674975785 13846090883993717006231839)
    ·
      refine ⟨20769136325990575509347759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13846090883993717006231839 20769136325990575509347759)
      ·
        refine ⟨31153704488985863264021639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20769136325990575509347759 31153704488985863264021639)
        ·
          refine ⟨46730556733478794896032459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31153704488985863264021639 46730556733478794896032459)
          ·
            refine ⟨70095835100218192344048689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46730556733478794896032459 70095835100218192344048689)
            ·
              refine ⟨52571876325163644258036517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70095835100218192344048689 52571876325163644258036517)
              ·
                refine ⟨9857226810968183298381847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52571876325163644258036517 9857226810968183298381847)
                ·
                  refine ⟨14785840216452274947572771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9857226810968183298381847 14785840216452274947572771)
                  ·
                    refine ⟨22178760324678412421359157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14785840216452274947572771 22178760324678412421359157)
                    ·
                      refine ⟨2079258780438601164502421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22178760324678412421359157 2079258780438601164502421)
                      ·
                        rfl

theorem cell23_4049342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_4049342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049342 prefixEnd_4049342 := by exact prefixLift 4049342
  have htrace : WordTrace (prefixWord ++ tailWord_4049342) baseStart_4049342 baseEnd_4049342 := by
    simpa [prefixWord, tailWord_4049342, baseEnd_4049342] using wordTrace_append hprefix tailTrace_4049342
  have hstable : (prefixWord ++ tailWord_4049342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049342).length < 2 ^ (prefixWord ++ tailWord_4049342).sum := by decide
  have hdescent : baseEnd_4049342 < baseStart_4049342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049352 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_4049352 : Nat := 118140960795 + 4049352 * 2 ^ 59
def prefixEnd_4049352 : Nat := 4983230072969 + 3 ^ 40 * 4049352 * 2
def baseEnd_4049352 : Nat := 2079263915245146125377375

theorem tailTrace_4049352 : CollatzResearch.WordTrace tailWord_4049352 prefixEnd_4049352 2079263915245146125377375 := by
  unfold tailWord_4049352
  simp only [CollatzResearch.WordTrace]
  refine ⟨73846000412948376553835155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98461333883931168738446873 73846000412948376553835155)
  ·
    refine ⟨110769000619422564830752733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73846000412948376553835155 110769000619422564830752733)
    ·
      refine ⟨41538375232283461811532275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110769000619422564830752733 41538375232283461811532275)
      ·
        refine ⟨62307562848425192717298413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41538375232283461811532275 62307562848425192717298413)
        ·
          refine ⟨23365336068159447268986905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62307562848425192717298413 23365336068159447268986905)
          ·
            refine ⟨17524002051119585451740179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23365336068159447268986905 17524002051119585451740179)
            ·
              refine ⟨26286003076679378177610269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17524002051119585451740179 26286003076679378177610269)
              ·
                refine ⟨9857251153754766816603851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26286003076679378177610269 9857251153754766816603851)
                ·
                  refine ⟨14785876730632150224905777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9857251153754766816603851 14785876730632150224905777)
                  ·
                    refine ⟨11089407547974112668679333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14785876730632150224905777 11089407547974112668679333)
                    ·
                      refine ⟨2079263915245146125377375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11089407547974112668679333 2079263915245146125377375)
                      ·
                        rfl

theorem cell23_4049352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_4049352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049352 prefixEnd_4049352 := by exact prefixLift 4049352
  have htrace : WordTrace (prefixWord ++ tailWord_4049352) baseStart_4049352 baseEnd_4049352 := by
    simpa [prefixWord, tailWord_4049352, baseEnd_4049352] using wordTrace_append hprefix tailTrace_4049352
  have hstable : (prefixWord ++ tailWord_4049352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049352).length < 2 ^ (prefixWord ++ tailWord_4049352).sum := by decide
  have hdescent : baseEnd_4049352 < baseStart_4049352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049385 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 5]
def baseStart_4049385 : Nat := 118140960795 + 4049385 * 2 ^ 59
def prefixEnd_4049385 : Nat := 4983230072969 + 3 ^ 40 * 4049385 * 2
def baseEnd_4049385 : Nat := 2079280860106744496264723

theorem tailTrace_4049385 : CollatzResearch.WordTrace tailWord_4049385 prefixEnd_4049385 2079280860106744496264723 := by
  unfold tailWord_4049385
  simp only [CollatzResearch.WordTrace]
  refine ⟨147693204434777199743621609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98462136289851466495747739 147693204434777199743621609)
  ·
    refine ⟨110769903326082899807716207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147693204434777199743621609 110769903326082899807716207)
    ·
      refine ⟨166154854989124349711574311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110769903326082899807716207 166154854989124349711574311)
      ·
        refine ⟨249232282483686524567361467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166154854989124349711574311 249232282483686524567361467)
        ·
          refine ⟨373848423725529786851042201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249232282483686524567361467 373848423725529786851042201)
          ·
            refine ⟨280386317794147340138281651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373848423725529786851042201 280386317794147340138281651)
            ·
              refine ⟨420579476691221010207422477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280386317794147340138281651 420579476691221010207422477)
              ·
                refine ⟨157717303759207878827783429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420579476691221010207422477 157717303759207878827783429)
                ·
                  refine ⟨29571994454851477280209393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157717303759207878827783429 29571994454851477280209393)
                  ·
                    refine ⟨22178995841138607960157045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29571994454851477280209393 22178995841138607960157045)
                    ·
                      refine ⟨2079280860106744496264723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22178995841138607960157045 2079280860106744496264723)
                      ·
                        rfl

theorem cell23_4049385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_4049385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049385 prefixEnd_4049385 := by exact prefixLift 4049385
  have htrace : WordTrace (prefixWord ++ tailWord_4049385) baseStart_4049385 baseEnd_4049385 := by
    simpa [prefixWord, tailWord_4049385, baseEnd_4049385] using wordTrace_append hprefix tailTrace_4049385
  have hstable : (prefixWord ++ tailWord_4049385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049385).length < 2 ^ (prefixWord ++ tailWord_4049385).sum := by decide
  have hdescent : baseEnd_4049385 < baseStart_4049385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049429 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 3, 4, 2]
def baseStart_4049429 : Nat := 118140960795 + 4049429 * 2 ^ 59
def prefixEnd_4049429 : Nat := 4983230072969 + 3 ^ 40 * 4049429 * 2
def baseEnd_4049429 : Nat := 2079303453255542324114521

theorem tailTrace_4049429 : CollatzResearch.WordTrace tailWord_4049429 prefixEnd_4049429 2079303453255542324114521 := by
  unfold tailWord_4049429
  simp only [CollatzResearch.WordTrace]
  refine ⟨147694809246617795258223341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98463206164411863505482227 147694809246617795258223341)
  ·
    refine ⟨55385553467481673221833753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147694809246617795258223341 55385553467481673221833753)
    ·
      refine ⟨41539165100611254916375315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55385553467481673221833753 41539165100611254916375315)
      ·
        refine ⟨62308747650916882374562973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41539165100611254916375315 62308747650916882374562973)
        ·
          refine ⟨23365780369093830890461115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62308747650916882374562973 23365780369093830890461115)
          ·
            refine ⟨35048670553640746335691673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23365780369093830890461115 35048670553640746335691673)
            ·
              refine ⟨26286502915230559751768755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35048670553640746335691673 26286502915230559751768755)
              ·
                refine ⟨39429754372845839627653133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26286502915230559751768755 39429754372845839627653133)
                ·
                  refine ⟨14786157889817189860369925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39429754372845839627653133 14786157889817189860369925)
                  ·
                    refine ⟨2772404604340723098819361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14786157889817189860369925 2772404604340723098819361)
                    ·
                      refine ⟨2079303453255542324114521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2772404604340723098819361 2079303453255542324114521)
                      ·
                        rfl

theorem cell23_4049429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_4049429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049429 prefixEnd_4049429 := by exact prefixLift 4049429
  have htrace : WordTrace (prefixWord ++ tailWord_4049429) baseStart_4049429 baseEnd_4049429 := by
    simpa [prefixWord, tailWord_4049429, baseEnd_4049429] using wordTrace_append hprefix tailTrace_4049429
  have hstable : (prefixWord ++ tailWord_4049429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049429).length < 2 ^ (prefixWord ++ tailWord_4049429).sum := by decide
  have hdescent : baseEnd_4049429 < baseStart_4049429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049432 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_4049432 : Nat := 118140960795 + 4049432 * 2 ^ 59
def prefixEnd_4049432 : Nat := 4983230072969 + 3 ^ 40 * 4049432 * 2
def baseEnd_4049432 : Nat := 2079304993697505812377007

theorem tailTrace_4049432 : CollatzResearch.WordTrace tailWord_4049432 prefixEnd_4049432 2079304993697505812377007 := by
  unfold tailWord_4049432
  simp only [CollatzResearch.WordTrace]
  refine ⟨73847459332803463385291275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98463279110404617847055033 73847459332803463385291275)
  ·
    refine ⟨110771188999205195077936913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73847459332803463385291275 110771188999205195077936913)
    ·
      refine ⟨83078391749403896308452685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110771188999205195077936913 83078391749403896308452685)
      ·
        refine ⟨31154396906026461115669757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83078391749403896308452685 31154396906026461115669757)
        ·
          refine ⟨11682898839759922918376159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31154396906026461115669757 11682898839759922918376159)
          ·
            refine ⟨17524348259639884377564239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11682898839759922918376159 17524348259639884377564239)
            ·
              refine ⟨26286522389459826566346359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17524348259639884377564239 26286522389459826566346359)
              ·
                refine ⟨39429783584189739849519539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26286522389459826566346359 39429783584189739849519539)
                ·
                  refine ⟨59144675376284609774279309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39429783584189739849519539 59144675376284609774279309)
                  ·
                    refine ⟨22179253266106728665354741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59144675376284609774279309 22179253266106728665354741)
                    ·
                      refine ⟨2079304993697505812377007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22179253266106728665354741 2079304993697505812377007)
                      ·
                        rfl

theorem cell23_4049432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_4049432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049432 prefixEnd_4049432 := by exact prefixLift 4049432
  have htrace : WordTrace (prefixWord ++ tailWord_4049432) baseStart_4049432 baseEnd_4049432 := by
    simpa [prefixWord, tailWord_4049432, baseEnd_4049432] using wordTrace_append hprefix tailTrace_4049432
  have hstable : (prefixWord ++ tailWord_4049432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049432).length < 2 ^ (prefixWord ++ tailWord_4049432).sum := by decide
  have hdescent : baseEnd_4049432 < baseStart_4049432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049519 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 1, 6, 2]
def baseStart_4049519 : Nat := 118140960795 + 4049519 * 2 ^ 59
def prefixEnd_4049519 : Nat := 4983230072969 + 3 ^ 40 * 4049519 * 2
def baseEnd_4049519 : Nat := 2079349666514446971989107

theorem tailTrace_4049519 : CollatzResearch.WordTrace tailWord_4049519 prefixEnd_4049519 2079349666514446971989107 := by
  unfold tailWord_4049519
  simp only [CollatzResearch.WordTrace]
  refine ⟨147698091816291740628999611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98465394544194493752666407 147698091816291740628999611)
  ·
    refine ⟨221547137724437610943499417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147698091816291740628999611 221547137724437610943499417)
    ·
      refine ⟨166160353293328208207624563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221547137724437610943499417 166160353293328208207624563)
      ·
        refine ⟨249240529939992312311436845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166160353293328208207624563 249240529939992312311436845)
        ·
          refine ⟨93465198727497117116788817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249240529939992312311436845 93465198727497117116788817)
          ·
            refine ⟨70098899045622837837591613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93465198727497117116788817 70098899045622837837591613)
            ·
              refine ⟨26287087142108564189096855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70098899045622837837591613 26287087142108564189096855)
              ·
                refine ⟨39430630713162846283645283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26287087142108564189096855 39430630713162846283645283)
                ·
                  refine ⟨59145946069744269425467925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39430630713162846283645283 59145946069744269425467925)
                  ·
                    refine ⟨2772466222019262629318809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59145946069744269425467925 2772466222019262629318809)
                    ·
                      refine ⟨2079349666514446971989107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2772466222019262629318809 2079349666514446971989107)
                      ·
                        rfl

theorem cell23_4049519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 6, 2].length) (baseStart_4049519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049519 prefixEnd_4049519 := by exact prefixLift 4049519
  have htrace : WordTrace (prefixWord ++ tailWord_4049519) baseStart_4049519 baseEnd_4049519 := by
    simpa [prefixWord, tailWord_4049519, baseEnd_4049519] using wordTrace_append hprefix tailTrace_4049519
  have hstable : (prefixWord ++ tailWord_4049519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049519).length < 2 ^ (prefixWord ++ tailWord_4049519).sum := by decide
  have hdescent : baseEnd_4049519 < baseStart_4049519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049529 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 5, 4]
def baseStart_4049529 : Nat := 118140960795 + 4049529 * 2 ^ 59
def prefixEnd_4049529 : Nat := 4983230072969 + 3 ^ 40 * 4049529 * 2
def baseEnd_4049529 : Nat := 693118267106997310954687

theorem tailTrace_4049529 : CollatzResearch.WordTrace tailWord_4049529 prefixEnd_4049529 693118267106997310954687 := by
  unfold tailWord_4049529
  simp only [CollatzResearch.WordTrace]
  refine ⟨147698456546255512336863641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98465637697503674891242427 147698456546255512336863641)
  ·
    refine ⟨110773842409691634252647731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147698456546255512336863641 110773842409691634252647731)
    ·
      refine ⟨166160763614537451378971597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110773842409691634252647731 166160763614537451378971597)
      ·
        refine ⟨62310286355451544267114349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166160763614537451378971597 62310286355451544267114349)
        ·
          refine ⟨23366357383294329100167881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62310286355451544267114349 23366357383294329100167881)
          ·
            refine ⟨17524768037470746825125911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23366357383294329100167881 17524768037470746825125911)
            ·
              refine ⟨26287152056206120237688867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17524768037470746825125911 26287152056206120237688867)
              ·
                refine ⟨39430728084309180356533301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26287152056206120237688867 39430728084309180356533301)
                ·
                  refine ⟨3696630757903985658424997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39430728084309180356533301 3696630757903985658424997)
                  ·
                    refine ⟨693118267106997310954687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3696630757903985658424997 693118267106997310954687)
                    ·
                      rfl

theorem cell23_4049529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 4].length) (baseStart_4049529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049529 prefixEnd_4049529 := by exact prefixLift 4049529
  have htrace : WordTrace (prefixWord ++ tailWord_4049529) baseStart_4049529 baseEnd_4049529 := by
    simpa [prefixWord, tailWord_4049529, baseEnd_4049529] using wordTrace_append hprefix tailTrace_4049529
  have hstable : (prefixWord ++ tailWord_4049529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049529).length < 2 ^ (prefixWord ++ tailWord_4049529).sum := by decide
  have hdescent : baseEnd_4049529 < baseStart_4049529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049533 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_4049533 : Nat := 118140960795 + 4049533 * 2 ^ 59
def prefixEnd_4049533 : Nat := 4983230072969 + 3 ^ 40 * 4049533 * 2
def baseEnd_4049533 : Nat := 693118951747869972404681

theorem tailTrace_4049533 : CollatzResearch.WordTrace tailWord_4049533 prefixEnd_4049533 693118951747869972404681 := by
  unfold tailWord_4049533
  simp only [CollatzResearch.WordTrace]
  refine ⟨147698602438241021020009253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98465734958827347346672835 147698602438241021020009253)
  ·
    refine ⟨27693487957170191441251735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147698602438241021020009253 27693487957170191441251735)
    ·
      refine ⟨41540231935755287161877603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27693487957170191441251735 41540231935755287161877603)
      ·
        refine ⟨62310347903632930742816405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41540231935755287161877603 62310347903632930742816405)
        ·
          refine ⟨2920797557982793628569519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62310347903632930742816405 2920797557982793628569519)
          ·
            refine ⟨4381196336974190442854279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920797557982793628569519 4381196336974190442854279)
            ·
              refine ⟨6571794505461285664281419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4381196336974190442854279 6571794505461285664281419)
              ·
                refine ⟨9857691758191928496422129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6571794505461285664281419 9857691758191928496422129)
                ·
                  refine ⟨7393268818643946372316597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9857691758191928496422129 7393268818643946372316597)
                  ·
                    refine ⟨693118951747869972404681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7393268818643946372316597 693118951747869972404681)
                    ·
                      rfl

theorem cell23_4049533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_4049533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049533 prefixEnd_4049533 := by exact prefixLift 4049533
  have htrace : WordTrace (prefixWord ++ tailWord_4049533) baseStart_4049533 baseEnd_4049533 := by
    simpa [prefixWord, tailWord_4049533, baseEnd_4049533] using wordTrace_append hprefix tailTrace_4049533
  have hstable : (prefixWord ++ tailWord_4049533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049533).length < 2 ^ (prefixWord ++ tailWord_4049533).sum := by decide
  have hdescent : baseEnd_4049533 < baseStart_4049533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049536 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 4]
def baseStart_4049536 : Nat := 118140960795 + 4049536 * 2 ^ 59
def prefixEnd_4049536 : Nat := 4983230072969 + 3 ^ 40 * 4049536 * 2
def baseEnd_4049536 : Nat := 2079358395685573405476529

theorem tailTrace_4049536 : CollatzResearch.WordTrace tailWord_4049536 prefixEnd_4049536 2079358395685573405476529 := by
  unfold tailWord_4049536
  simp only [CollatzResearch.WordTrace]
  refine ⟨73849355928615076266184231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98465807904820101688245641 73849355928615076266184231)
  ·
    refine ⟨110774033892922614399276347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73849355928615076266184231 110774033892922614399276347)
    ·
      refine ⟨166161050839383921598914521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110774033892922614399276347 166161050839383921598914521)
      ·
        refine ⟨124620788129537941199185891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166161050839383921598914521 124620788129537941199185891)
        ·
          refine ⟨186931182194306911798778837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124620788129537941199185891 186931182194306911798778837)
          ·
            refine ⟨4381199582679068245283879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 186931182194306911798778837 4381199582679068245283879)
            ·
              refine ⟨6571799374018602367925819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4381199582679068245283879 6571799374018602367925819)
              ·
                refine ⟨9857699061027903551888729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6571799374018602367925819 9857699061027903551888729)
                ·
                  refine ⟨7393274295770927663916547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9857699061027903551888729 7393274295770927663916547)
                  ·
                    refine ⟨11089911443656391495874821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7393274295770927663916547 11089911443656391495874821)
                    ·
                      refine ⟨2079358395685573405476529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11089911443656391495874821 2079358395685573405476529)
                      ·
                        rfl

theorem cell23_4049536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_4049536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049536 prefixEnd_4049536 := by exact prefixLift 4049536
  have htrace : WordTrace (prefixWord ++ tailWord_4049536) baseStart_4049536 baseEnd_4049536 := by
    simpa [prefixWord, tailWord_4049536, baseEnd_4049536] using wordTrace_append hprefix tailTrace_4049536
  have hstable : (prefixWord ++ tailWord_4049536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049536).length < 2 ^ (prefixWord ++ tailWord_4049536).sum := by decide
  have hdescent : baseEnd_4049536 < baseStart_4049536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049596 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 1, 5, 2]
def baseStart_4049596 : Nat := 118140960795 + 4049596 * 2 ^ 59
def prefixEnd_4049596 : Nat := 4983230072969 + 3 ^ 40 * 4049596 * 2
def baseEnd_4049596 : Nat := 2079389204524843170726253

theorem tailTrace_4049596 : CollatzResearch.WordTrace tailWord_4049596 prefixEnd_4049596 2079389204524843170726253 := by
  unfold tailWord_4049596
  simp only [CollatzResearch.WordTrace]
  refine ⟨73850450118506391389776321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98467266824675188519701761 73850450118506391389776321)
  ·
    refine ⟨55387837588879793542332241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73850450118506391389776321 55387837588879793542332241)
    ·
      refine ⟨41540878191659845156749181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55387837588879793542332241 41540878191659845156749181)
      ·
        refine ⟨15577829321872441933780943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41540878191659845156749181 15577829321872441933780943)
        ·
          refine ⟨23366743982808662900671415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15577829321872441933780943 23366743982808662900671415)
          ·
            refine ⟨35050115974212994351007123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23366743982808662900671415 35050115974212994351007123)
            ·
              refine ⟨52575173961319491526510685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35050115974212994351007123 52575173961319491526510685)
              ·
                refine ⟨19715690235494809322441507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52575173961319491526510685 19715690235494809322441507)
                ·
                  refine ⟨29573535353242213983662261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19715690235494809322441507 29573535353242213983662261)
                  ·
                    refine ⟨2772518939366457560968337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29573535353242213983662261 2772518939366457560968337)
                    ·
                      refine ⟨2079389204524843170726253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2772518939366457560968337 2079389204524843170726253)
                      ·
                        rfl

theorem cell23_4049596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_4049596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049596 prefixEnd_4049596 := by exact prefixLift 4049596
  have htrace : WordTrace (prefixWord ++ tailWord_4049596) baseStart_4049596 baseEnd_4049596 := by
    simpa [prefixWord, tailWord_4049596, baseEnd_4049596] using wordTrace_append hprefix tailTrace_4049596
  have hstable : (prefixWord ++ tailWord_4049596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049596).length < 2 ^ (prefixWord ++ tailWord_4049596).sum := by decide
  have hdescent : baseEnd_4049596 < baseStart_4049596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049640 : List Nat := [2, 1, 4, 1, 5, 1, 1, 2, 1, 5]
def baseStart_4049640 : Nat := 118140960795 + 4049640 * 2 ^ 59
def prefixEnd_4049640 : Nat := 4983230072969 + 3 ^ 40 * 4049640 * 2
def baseEnd_4049640 : Nat := 693137265891213666192017

theorem tailTrace_4049640 : CollatzResearch.WordTrace tailWord_4049640 prefixEnd_4049640 693137265891213666192017 := by
  unfold tailWord_4049640
  simp only [CollatzResearch.WordTrace]
  refine ⟨73851252524426689147077187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98468336699235585529436249 73851252524426689147077187)
  ·
    refine ⟨110776878786640033720615781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73851252524426689147077187 110776878786640033720615781)
    ·
      refine ⟨20770664772495006322615459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110776878786640033720615781 20770664772495006322615459)
      ·
        refine ⟨31155997158742509483923189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20770664772495006322615459 31155997158742509483923189)
        ·
          refine ⟨2920874733632110264117799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31155997158742509483923189 2920874733632110264117799)
          ·
            refine ⟨4381312100448165396176699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920874733632110264117799 4381312100448165396176699)
            ·
              refine ⟨6571968150672248094265049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4381312100448165396176699 6571968150672248094265049)
              ·
                refine ⟨4928976113004186070698787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6571968150672248094265049 4928976113004186070698787)
                ·
                  refine ⟨7393464169506279106048181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4928976113004186070698787 7393464169506279106048181)
                  ·
                    refine ⟨693137265891213666192017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7393464169506279106048181 693137265891213666192017)
                    ·
                      rfl

theorem cell23_4049640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_4049640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049640 prefixEnd_4049640 := by exact prefixLift 4049640
  have htrace : WordTrace (prefixWord ++ tailWord_4049640) baseStart_4049640 baseEnd_4049640 := by
    simpa [prefixWord, tailWord_4049640, baseEnd_4049640] using wordTrace_append hprefix tailTrace_4049640
  have hstable : (prefixWord ++ tailWord_4049640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049640).length < 2 ^ (prefixWord ++ tailWord_4049640).sum := by decide
  have hdescent : baseEnd_4049640 < baseStart_4049640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049699 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 4]
def baseStart_4049699 : Nat := 118140960795 + 4049699 * 2 ^ 59
def prefixEnd_4049699 : Nat := 4983230072969 + 3 ^ 40 * 4049699 * 2
def baseEnd_4049699 : Nat := 2079442093032256267738279

theorem tailTrace_4049699 : CollatzResearch.WordTrace tailWord_4049699 prefixEnd_4049699 2079442093032256267738279 := by
  unfold tailWord_4049699
  simp only [CollatzResearch.WordTrace]
  refine ⟨147704656955639631370552151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98469771303759754247034767 147704656955639631370552151)
  ·
    refine ⟨221556985433459447055828227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147704656955639631370552151 221556985433459447055828227)
    ·
      refine ⟨332335478150189170583742341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221556985433459447055828227 332335478150189170583742341)
      ·
        refine ⟨62312902153160469484451689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332335478150189170583742341 62312902153160469484451689)
        ·
          refine ⟨46734676614870352113338767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62312902153160469484451689 46734676614870352113338767)
          ·
            refine ⟨70102014922305528170008151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46734676614870352113338767 70102014922305528170008151)
            ·
              refine ⟨105153022383458292255012227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70102014922305528170008151 105153022383458292255012227)
              ·
                refine ⟨157729533575187438382518341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105153022383458292255012227 157729533575187438382518341)
                ·
                  refine ⟨29574287545347644696722189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157729533575187438382518341 29574287545347644696722189)
                  ·
                    refine ⟨11090357829505366761270821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29574287545347644696722189 11090357829505366761270821)
                    ·
                      refine ⟨2079442093032256267738279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11090357829505366761270821 2079442093032256267738279)
                      ·
                        rfl

theorem cell23_4049699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_4049699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049699 prefixEnd_4049699 := by exact prefixLift 4049699
  have htrace : WordTrace (prefixWord ++ tailWord_4049699) baseStart_4049699 baseEnd_4049699 := by
    simpa [prefixWord, tailWord_4049699, baseEnd_4049699] using wordTrace_append hprefix tailTrace_4049699
  have hstable : (prefixWord ++ tailWord_4049699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049699).length < 2 ^ (prefixWord ++ tailWord_4049699).sum := by decide
  have hdescent : baseEnd_4049699 < baseStart_4049699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049719 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_4049719 : Nat := 118140960795 + 4049719 * 2 ^ 59
def prefixEnd_4049719 : Nat := 4983230072969 + 3 ^ 40 * 4049719 * 2
def baseEnd_4049719 : Nat := 2079452362645346189488187

theorem tailTrace_4049719 : CollatzResearch.WordTrace tailWord_4049719 prefixEnd_4049719 2079452362645346189488187 := by
  unfold tailWord_4049719
  simp only [CollatzResearch.WordTrace]
  refine ⟨147705386415567174786280211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98470257610378116524186807 147705386415567174786280211)
  ·
    refine ⟨221558079623350762179420317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147705386415567174786280211 221558079623350762179420317)
    ·
      refine ⟨83084279858756535817282619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221558079623350762179420317 83084279858756535817282619)
      ·
        refine ⟨124626419788134803725923929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83084279858756535817282619 124626419788134803725923929)
        ·
          refine ⟨93469814841101102794442947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124626419788134803725923929 93469814841101102794442947)
          ·
            refine ⟨140204722261651654191664421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93469814841101102794442947 140204722261651654191664421)
            ·
              refine ⟨26288385424059685160937079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140204722261651654191664421 26288385424059685160937079)
              ·
                refine ⟨39432578136089527741405619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26288385424059685160937079 39432578136089527741405619)
                ·
                  refine ⟨59148867204134291612108429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39432578136089527741405619 59148867204134291612108429)
                  ·
                    refine ⟨22180825201550359354540661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59148867204134291612108429 22180825201550359354540661)
                    ·
                      refine ⟨2079452362645346189488187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22180825201550359354540661 2079452362645346189488187)
                      ·
                        rfl

theorem cell23_4049719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_4049719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049719 prefixEnd_4049719 := by exact prefixLift 4049719
  have htrace : WordTrace (prefixWord ++ tailWord_4049719) baseStart_4049719 baseEnd_4049719 := by
    simpa [prefixWord, tailWord_4049719, baseEnd_4049719] using wordTrace_append hprefix tailTrace_4049719
  have hstable : (prefixWord ++ tailWord_4049719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049719).length < 2 ^ (prefixWord ++ tailWord_4049719).sum := by decide
  have hdescent : baseEnd_4049719 < baseStart_4049719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049746 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_4049746 : Nat := 118140960795 + 4049746 * 2 ^ 59
def prefixEnd_4049746 : Nat := 4983230072969 + 3 ^ 40 * 4049746 * 2
def baseEnd_4049746 : Nat := 2079466226623017583850563

theorem tailTrace_4049746 : CollatzResearch.WordTrace tailWord_4049746 prefixEnd_4049746 2079466226623017583850563 := by
  unfold tailWord_4049746
  simp only [CollatzResearch.WordTrace]
  refine ⟨36926592796617339599378273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98470914124312905598342061 36926592796617339599378273)
  ·
    refine ⟨27694944597463004699533705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36926592796617339599378273 27694944597463004699533705)
    ·
      refine ⟨20771208448097253524650279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27694944597463004699533705 20771208448097253524650279)
      ·
        refine ⟨31156812672145880286975419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20771208448097253524650279 31156812672145880286975419)
        ·
          refine ⟨46735219008218820430463129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31156812672145880286975419 46735219008218820430463129)
          ·
            refine ⟨35051414256164115322847347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46735219008218820430463129 35051414256164115322847347)
            ·
              refine ⟨52577121384246172984271021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35051414256164115322847347 52577121384246172984271021)
              ·
                refine ⟨19716420519092314869101633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52577121384246172984271021 19716420519092314869101633)
                ·
                  refine ⟨14787315389319236151826225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19716420519092314869101633 14787315389319236151826225)
                  ·
                    refine ⟨11090486541989427113869669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14787315389319236151826225 11090486541989427113869669)
                    ·
                      refine ⟨2079466226623017583850563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11090486541989427113869669 2079466226623017583850563)
                      ·
                        rfl

theorem cell23_4049746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_4049746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049746 prefixEnd_4049746 := by exact prefixLift 4049746
  have htrace : WordTrace (prefixWord ++ tailWord_4049746) baseStart_4049746 baseEnd_4049746 := by
    simpa [prefixWord, tailWord_4049746, baseEnd_4049746] using wordTrace_append hprefix tailTrace_4049746
  have hstable : (prefixWord ++ tailWord_4049746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049746).length < 2 ^ (prefixWord ++ tailWord_4049746).sum := by decide
  have hdescent : baseEnd_4049746 < baseStart_4049746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049820 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 2, 5]
def baseStart_4049820 : Nat := 118140960795 + 4049820 * 2 ^ 59
def prefixEnd_4049820 : Nat := 4983230072969 + 3 ^ 40 * 4049820 * 2
def baseEnd_4049820 : Nat := 693168074730483431441741

theorem tailTrace_4049820 : CollatzResearch.WordTrace tailWord_4049820 prefixEnd_4049820 693168074730483431441741 := by
  unfold tailWord_4049820
  simp only [CollatzResearch.WordTrace]
  refine ⟨73854535094100634517853457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98472713458800846023804609 73854535094100634517853457)
  ·
    refine ⟨55390901320575475888390093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73854535094100634517853457 55390901320575475888390093)
    ·
      refine ⟨20771587995215803458146285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55390901320575475888390093 20771587995215803458146285)
      ·
        refine ⟨7789345498205926296804857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20771587995215803458146285 7789345498205926296804857)
        ·
          refine ⟨5842009123654444722603643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7789345498205926296804857 5842009123654444722603643)
          ·
            refine ⟨8763013685481667083905465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5842009123654444722603643 8763013685481667083905465)
            ·
              refine ⟨6572260264111250312929099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8763013685481667083905465 6572260264111250312929099)
              ·
                refine ⟨9858390396166875469393649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6572260264111250312929099 9858390396166875469393649)
                ·
                  refine ⟨7393792797125156602045237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9858390396166875469393649 7393792797125156602045237)
                  ·
                    refine ⟨693168074730483431441741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7393792797125156602045237 693168074730483431441741)
                    ·
                      rfl

theorem cell23_4049820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_4049820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049820 prefixEnd_4049820 := by exact prefixLift 4049820
  have htrace : WordTrace (prefixWord ++ tailWord_4049820) baseStart_4049820 baseEnd_4049820 := by
    simpa [prefixWord, tailWord_4049820, baseEnd_4049820] using wordTrace_append hprefix tailTrace_4049820
  have hstable : (prefixWord ++ tailWord_4049820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049820).length < 2 ^ (prefixWord ++ tailWord_4049820).sum := by decide
  have hdescent : baseEnd_4049820 < baseStart_4049820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049823 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 4]
def baseStart_4049823 : Nat := 118140960795 + 4049823 * 2 ^ 59
def prefixEnd_4049823 : Nat := 4983230072969 + 3 ^ 40 * 4049823 * 2
def baseEnd_4049823 : Nat := 2079505764633413782587709

theorem tailTrace_4049823 : CollatzResearch.WordTrace tailWord_4049823 prefixEnd_4049823 2079505764633413782587709 := by
  unfold tailWord_4049823
  simp only [CollatzResearch.WordTrace]
  refine ⟨147709179607190400548066123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98472786404793600365377415 147709179607190400548066123)
  ·
    refine ⟨221563769410785600822099185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147709179607190400548066123 221563769410785600822099185)
    ·
      refine ⟨166172827058089200616574389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221563769410785600822099185 166172827058089200616574389)
      ·
        refine ⟨15578702536695862557803849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166172827058089200616574389 15578702536695862557803849)
        ·
          refine ⟨11684026902521896918352887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15578702536695862557803849 11684026902521896918352887)
          ·
            refine ⟨17526040353782845377529331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11684026902521896918352887 17526040353782845377529331)
            ·
              refine ⟨26289060530674268066293997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17526040353782845377529331 26289060530674268066293997)
              ·
                refine ⟨9858397699002850524860249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26289060530674268066293997 9858397699002850524860249)
                ·
                  refine ⟨7393798274252137893645187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9858397699002850524860249 7393798274252137893645187)
                  ·
                    refine ⟨11090697411378206840467781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7393798274252137893645187 11090697411378206840467781)
                    ·
                      refine ⟨2079505764633413782587709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11090697411378206840467781 2079505764633413782587709)
                      ·
                        rfl

theorem cell23_4049823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_4049823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049823 prefixEnd_4049823 := by exact prefixLift 4049823
  have htrace : WordTrace (prefixWord ++ tailWord_4049823) baseStart_4049823 baseEnd_4049823 := by
    simpa [prefixWord, tailWord_4049823, baseEnd_4049823] using wordTrace_append hprefix tailTrace_4049823
  have hstable : (prefixWord ++ tailWord_4049823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049823).length < 2 ^ (prefixWord ++ tailWord_4049823).sum := by decide
  have hdescent : baseEnd_4049823 < baseStart_4049823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049850 : List Nat := [3, 1, 1, 1, 2, 1, 5, 4, 1, 4]
def baseStart_4049850 : Nat := 118140960795 + 4049850 * 2 ^ 59
def prefixEnd_4049850 : Nat := 4983230072969 + 3 ^ 40 * 4049850 * 2
def baseEnd_4049850 : Nat := 693173209537028392316695

theorem tailTrace_4049850 : CollatzResearch.WordTrace tailWord_4049850 prefixEnd_4049850 693173209537028392316695 := by
  unfold tailWord_4049850
  simp only [CollatzResearch.WordTrace]
  refine ⟨36927541094523146039824751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98473442918728389439532669 36927541094523146039824751)
  ·
    refine ⟨55391311641784719059737127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36927541094523146039824751 55391311641784719059737127)
    ·
      refine ⟨83086967462677078589605691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55391311641784719059737127 83086967462677078589605691)
      ·
        refine ⟨124630451194015617884408537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83086967462677078589605691 124630451194015617884408537)
        ·
          refine ⟨93472838395511713413306403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124630451194015617884408537 93472838395511713413306403)
          ·
            refine ⟨140209257593267570119959605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93472838395511713413306403 140209257593267570119959605)
            ·
              refine ⟨13144617899368834698746213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140209257593267570119959605 13144617899368834698746213)
              ·
                refine ⟨2464615856131656506014915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13144617899368834698746213 2464615856131656506014915)
                ·
                  refine ⟨3696923784197484759022373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464615856131656506014915 3696923784197484759022373)
                  ·
                    refine ⟨693173209537028392316695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3696923784197484759022373 693173209537028392316695)
                    ·
                      rfl

theorem cell23_4049850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_4049850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049850 prefixEnd_4049850 := by exact prefixLift 4049850
  have htrace : WordTrace (prefixWord ++ tailWord_4049850) baseStart_4049850 baseEnd_4049850 := by
    simpa [prefixWord, tailWord_4049850, baseEnd_4049850] using wordTrace_append hprefix tailTrace_4049850
  have hstable : (prefixWord ++ tailWord_4049850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049850).length < 2 ^ (prefixWord ++ tailWord_4049850).sum := by decide
  have hdescent : baseEnd_4049850 < baseStart_4049850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049877 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_4049877 : Nat := 118140960795 + 4049877 * 2 ^ 59
def prefixEnd_4049877 : Nat := 4983230072969 + 3 ^ 40 * 4049877 * 2
def baseEnd_4049877 : Nat := 2079533492588756571312461

theorem tailTrace_4049877 : CollatzResearch.WordTrace tailWord_4049877 prefixEnd_4049877 2079533492588756571312461 := by
  unfold tailWord_4049877
  simp only [CollatzResearch.WordTrace]
  refine ⟨147711149148994767770531885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98474099432663178513687923 147711149148994767770531885)
  ·
    refine ⟨55391680930873037913949457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147711149148994767770531885 55391680930873037913949457)
    ·
      refine ⟨41543760698154778435462093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55391680930873037913949457 41543760698154778435462093)
      ·
        refine ⟨15578910261808041913298285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41543760698154778435462093 15578910261808041913298285)
        ·
          refine ⟨5842091348178015717486857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15578910261808041913298285 5842091348178015717486857)
          ·
            refine ⟨4381568511133511788115143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5842091348178015717486857 4381568511133511788115143)
            ·
              refine ⟨6572352766700267682172715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4381568511133511788115143 6572352766700267682172715)
              ·
                refine ⟨9858529150050401523259073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6572352766700267682172715 9858529150050401523259073)
                ·
                  refine ⟨7393896862537801142444305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9858529150050401523259073 7393896862537801142444305)
                  ·
                    refine ⟨5545422646903350856833229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7393896862537801142444305 5545422646903350856833229)
                    ·
                      refine ⟨2079533492588756571312461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5545422646903350856833229 2079533492588756571312461)
                      ·
                        rfl

theorem cell23_4049877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_4049877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049877 prefixEnd_4049877 := by exact prefixLift 4049877
  have htrace : WordTrace (prefixWord ++ tailWord_4049877) baseStart_4049877 baseEnd_4049877 := by
    simpa [prefixWord, tailWord_4049877, baseEnd_4049877] using wordTrace_append hprefix tailTrace_4049877
  have hstable : (prefixWord ++ tailWord_4049877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049877).length < 2 ^ (prefixWord ++ tailWord_4049877).sum := by decide
  have hdescent : baseEnd_4049877 < baseStart_4049877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049930 : List Nat := [3, 1, 2, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_4049930 : Nat := 118140960795 + 4049930 * 2 ^ 59
def prefixEnd_4049930 : Nat := 4983230072969 + 3 ^ 40 * 4049930 * 2
def baseEnd_4049930 : Nat := 2079560707063444863949717

theorem tailTrace_4049930 : CollatzResearch.WordTrace tailWord_4049930 prefixEnd_4049930 2079560707063444863949717 := by
  unfold tailWord_4049930
  simp only [CollatzResearch.WordTrace]
  refine ⟨36928270554450689455552811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98475388145201838548140829 36928270554450689455552811)
  ·
    refine ⟨55392405831676034183329217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36928270554450689455552811 55392405831676034183329217)
    ·
      refine ⟨41544304373757025637496913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55392405831676034183329217 41544304373757025637496913)
      ·
        refine ⟨31158228280317769228122685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41544304373757025637496913 31158228280317769228122685)
        ·
          refine ⟨11684335605119163460546007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31158228280317769228122685 11684335605119163460546007)
          ·
            refine ⟨17526503407678745190819011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11684335605119163460546007 17526503407678745190819011)
            ·
              refine ⟨26289755111518117786228517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17526503407678745190819011 26289755111518117786228517)
              ·
                refine ⟨4929329083409647084917847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26289755111518117786228517 4929329083409647084917847)
                ·
                  refine ⟨7393993625114470627376771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929329083409647084917847 7393993625114470627376771)
                  ·
                    refine ⟨11090990437671705941065157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7393993625114470627376771 11090990437671705941065157)
                    ·
                      refine ⟨2079560707063444863949717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11090990437671705941065157 2079560707063444863949717)
                      ·
                        rfl

theorem cell23_4049930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_4049930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049930 prefixEnd_4049930 := by exact prefixLift 4049930
  have htrace : WordTrace (prefixWord ++ tailWord_4049930) baseStart_4049930 baseEnd_4049930 := by
    simpa [prefixWord, tailWord_4049930, baseEnd_4049930] using wordTrace_append hprefix tailTrace_4049930
  have hstable : (prefixWord ++ tailWord_4049930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049930).length < 2 ^ (prefixWord ++ tailWord_4049930).sum := by decide
  have hdescent : baseEnd_4049930 < baseStart_4049930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049953 : List Nat := [1, 2, 3, 2, 3, 3, 9]
def baseStart_4049953 : Nat := 118140960795 + 4049953 * 2 ^ 59
def prefixEnd_4049953 : Nat := 4983230072969 + 3 ^ 40 * 4049953 * 2
def baseEnd_4049953 : Nat := 25673734779240719431631

theorem tailTrace_4049953 : CollatzResearch.WordTrace tailWord_4049953 prefixEnd_4049953 25673734779240719431631 := by
  unfold tailWord_4049953
  simp only [CollatzResearch.WordTrace]
  refine ⟨147713921096719432750298513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98475947397812955166865675 147713921096719432750298513)
  ·
    refine ⟨110785440822539574562723885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147713921096719432750298513 110785440822539574562723885)
    ·
      refine ⟨41544540308452340461021457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110785440822539574562723885 41544540308452340461021457)
      ·
        refine ⟨31158405231339255345766093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41544540308452340461021457 31158405231339255345766093)
        ·
          refine ⟨11684401961752220754662285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31158405231339255345766093 11684401961752220754662285)
          ·
            refine ⟨4381650735657082782998357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11684401961752220754662285 4381650735657082782998357)
            ·
              refine ⟨25673734779240719431631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4381650735657082782998357 25673734779240719431631)
              ·
                rfl

theorem cell23_4049953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 9].length) (baseStart_4049953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049953 prefixEnd_4049953 := by exact prefixLift 4049953
  have htrace : WordTrace (prefixWord ++ tailWord_4049953) baseStart_4049953 baseEnd_4049953 := by
    simpa [prefixWord, tailWord_4049953, baseEnd_4049953] using wordTrace_append hprefix tailTrace_4049953
  have hstable : (prefixWord ++ tailWord_4049953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049953).length < 2 ^ (prefixWord ++ tailWord_4049953).sum := by decide
  have hdescent : baseEnd_4049953 < baseStart_4049953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049974 : List Nat := [5, 1, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_4049974 : Nat := 118140960795 + 4049974 * 2 ^ 59
def prefixEnd_4049974 : Nat := 4983230072969 + 3 ^ 40 * 4049974 * 2
def baseEnd_4049974 : Nat := 693194433404080897266505

theorem tailTrace_4049974 : CollatzResearch.WordTrace tailWord_4049974 prefixEnd_4049974 693194433404080897266505 := by
  unfold tailWord_4049974
  simp only [CollatzResearch.WordTrace]
  refine ⟨9232167939352709583550811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98476458019762235557875317 9232167939352709583550811)
  ·
    refine ⟨13848251909029064375326217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9232167939352709583550811 13848251909029064375326217)
    ·
      refine ⟨10386188931771798281494663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13848251909029064375326217 10386188931771798281494663)
      ·
        refine ⟨15579283397657697422241995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10386188931771798281494663 15579283397657697422241995)
        ·
          refine ⟨23368925096486546133362993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15579283397657697422241995 23368925096486546133362993)
          ·
            refine ⟨17526693822364909600022245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23368925096486546133362993 17526693822364909600022245)
            ·
              refine ⟨3286255091693420550004171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17526693822364909600022245 3286255091693420550004171)
              ·
                refine ⟨4929382637540130825006257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286255091693420550004171 4929382637540130825006257)
                ·
                  refine ⟨3697036978155098118754693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4929382637540130825006257 3697036978155098118754693)
                  ·
                    refine ⟨693194433404080897266505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3697036978155098118754693 693194433404080897266505)
                    ·
                      rfl

theorem cell23_4049974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_4049974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049974 prefixEnd_4049974 := by exact prefixLift 4049974
  have htrace : WordTrace (prefixWord ++ tailWord_4049974) baseStart_4049974 baseEnd_4049974 := by
    simpa [prefixWord, tailWord_4049974, baseEnd_4049974] using wordTrace_append hprefix tailTrace_4049974
  have hstable : (prefixWord ++ tailWord_4049974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049974).length < 2 ^ (prefixWord ++ tailWord_4049974).sum := by decide
  have hdescent : baseEnd_4049974 < baseStart_4049974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049997 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_4049997 : Nat := 118140960795 + 4049997 * 2 ^ 59
def prefixEnd_4049997 : Nat := 4983230072969 + 3 ^ 40 * 4049997 * 2
def baseEnd_4049997 : Nat := 2079595110267296101811909

theorem tailTrace_4049997 : CollatzResearch.WordTrace tailWord_4049997 prefixEnd_4049997 2079595110267296101811909 := by
  unfold tailWord_4049997
  simp only [CollatzResearch.WordTrace]
  refine ⟨147715525908560028264900245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98477017272373352176600163 147715525908560028264900245)
  ·
    refine ⟨6924165276963751324917199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 147715525908560028264900245 6924165276963751324917199)
    ·
      refine ⟨10386247915445626987375799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6924165276963751324917199 10386247915445626987375799)
      ·
        refine ⟨15579371873168440481063699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10386247915445626987375799 15579371873168440481063699)
        ·
          refine ⟨23369057809752660721595549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15579371873168440481063699 23369057809752660721595549)
          ·
            refine ⟨8763396678657247770598331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23369057809752660721595549 8763396678657247770598331)
            ·
              refine ⟨13145095017985871655897497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8763396678657247770598331 13145095017985871655897497)
              ·
                refine ⟨9858821263489403741923123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13145095017985871655897497 9858821263489403741923123)
                ·
                  refine ⟨14788231895234105612884685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9858821263489403741923123 14788231895234105612884685)
                  ·
                    refine ⟨5545586960712789604831757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14788231895234105612884685 5545586960712789604831757)
                    ·
                      refine ⟨2079595110267296101811909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5545586960712789604831757 2079595110267296101811909)
                      ·
                        rfl

theorem cell23_4049997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_4049997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4049997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4049997 prefixEnd_4049997 := by exact prefixLift 4049997
  have htrace : WordTrace (prefixWord ++ tailWord_4049997) baseStart_4049997 baseEnd_4049997 := by
    simpa [prefixWord, tailWord_4049997, baseEnd_4049997] using wordTrace_append hprefix tailTrace_4049997
  have hstable : (prefixWord ++ tailWord_4049997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049997).length < 2 ^ (prefixWord ++ tailWord_4049997).sum := by decide
  have hdescent : baseEnd_4049997 < baseStart_4049997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050020 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 5, 4, 2]
def baseStart_4050020 : Nat := 118140960795 + 4050020 * 2 ^ 59
def prefixEnd_4050020 : Nat := 4983230072969 + 3 ^ 40 * 4050020 * 2
def baseEnd_4050020 : Nat := 2079606920322349511824303

theorem tailTrace_4050020 : CollatzResearch.WordTrace tailWord_4050020 prefixEnd_4050020 2079606920322349511824303 := by
  unfold tailWord_4050020
  simp only [CollatzResearch.WordTrace]
  refine ⟨73858182393738351596493757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98477576524984468795325009 73858182393738351596493757)
  ·
    refine ⟨27696818397651881848685159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73858182393738351596493757 27696818397651881848685159)
    ·
      refine ⟨41545227596477822773027739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27696818397651881848685159 41545227596477822773027739)
      ·
        refine ⟨62317841394716734159541609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41545227596477822773027739 62317841394716734159541609)
        ·
          refine ⟨46738381046037550619656207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62317841394716734159541609 46738381046037550619656207)
          ·
            refine ⟨70107571569056325929484311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46738381046037550619656207 70107571569056325929484311)
            ·
              refine ⟨105161357353584488894226467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70107571569056325929484311 105161357353584488894226467)
              ·
                refine ⟨157742036030376733341339701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105161357353584488894226467 157742036030376733341339701)
                ·
                  refine ⟨14788315877847818750750597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157742036030376733341339701 14788315877847818750750597)
                  ·
                    refine ⟨2772809227096466015765737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14788315877847818750750597 2772809227096466015765737)
                    ·
                      refine ⟨2079606920322349511824303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2772809227096466015765737 2079606920322349511824303)
                      ·
                        rfl

theorem cell23_4050020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_4050020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050020 prefixEnd_4050020 := by exact prefixLift 4050020
  have htrace : WordTrace (prefixWord ++ tailWord_4050020) baseStart_4050020 baseEnd_4050020 := by
    simpa [prefixWord, tailWord_4050020, baseEnd_4050020] using wordTrace_append hprefix tailTrace_4050020
  have hstable : (prefixWord ++ tailWord_4050020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050020).length < 2 ^ (prefixWord ++ tailWord_4050020).sum := by decide
  have hdescent : baseEnd_4050020 < baseStart_4050020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050030 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_4050030 : Nat := 118140960795 + 4050030 * 2 ^ 59
def prefixEnd_4050030 : Nat := 4983230072969 + 3 ^ 40 * 4050030 * 2
def baseEnd_4050030 : Nat := 693204018376298157566419

theorem tailTrace_4050030 : CollatzResearch.WordTrace tailWord_4050030 prefixEnd_4050030 693204018376298157566419 := by
  unfold tailWord_4050030
  simp only [CollatzResearch.WordTrace]
  refine ⟨18464591189680059362606443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98477819678293649933901029 18464591189680059362606443)
  ·
    refine ⟨27696886784520089043909665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18464591189680059362606443 27696886784520089043909665)
    ·
      refine ⟨20772665088390066782932249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27696886784520089043909665 20772665088390066782932249)
      ·
        refine ⟨15579498816292550087199187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20772665088390066782932249 15579498816292550087199187)
        ·
          refine ⟨23369248224438825130798781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15579498816292550087199187 23369248224438825130798781)
          ·
            refine ⟨8763468084164559424049543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23369248224438825130798781 8763468084164559424049543)
            ·
              refine ⟨13145202126246839136074315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8763468084164559424049543 13145202126246839136074315)
              ·
                refine ⟨19717803189370258704111473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13145202126246839136074315 19717803189370258704111473)
                ·
                  refine ⟨14788352392027694028083605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19717803189370258704111473 14788352392027694028083605)
                  ·
                    refine ⟨693204018376298157566419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14788352392027694028083605 693204018376298157566419)
                    ·
                      rfl

theorem cell23_4050030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_4050030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050030 prefixEnd_4050030 := by exact prefixLift 4050030
  have htrace : WordTrace (prefixWord ++ tailWord_4050030) baseStart_4050030 baseEnd_4050030 := by
    simpa [prefixWord, tailWord_4050030, baseEnd_4050030] using wordTrace_append hprefix tailTrace_4050030
  have hstable : (prefixWord ++ tailWord_4050030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050030).length < 2 ^ (prefixWord ++ tailWord_4050030).sum := by decide
  have hdescent : baseEnd_4050030 < baseStart_4050030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050071 : List Nat := [1, 1, 3, 3, 3, 3, 1, 2, 2, 2, 2]
def baseStart_4050071 : Nat := 118140960795 + 4050071 * 2 ^ 59
def prefixEnd_4050071 : Nat := 4983230072969 + 3 ^ 40 * 4050071 * 2
def baseEnd_4050071 : Nat := 2079633107835728812286569

theorem tailTrace_4050071 : CollatzResearch.WordTrace tailWord_4050071 prefixEnd_4050071 2079633107835728812286569 := by
  unfold tailWord_4050071
  simp only [CollatzResearch.WordTrace]
  refine ⟨147718224910291938903094067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98478816606861292602062711 147718224910291938903094067)
  ·
    refine ⟨221577337365437908354641101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147718224910291938903094067 221577337365437908354641101)
    ·
      refine ⟨83091501512039215632990413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221577337365437908354641101 83091501512039215632990413)
      ·
        refine ⟨31159313067014705862371405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83091501512039215632990413 31159313067014705862371405)
        ·
          refine ⟨11684742400130514698389277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31159313067014705862371405 11684742400130514698389277)
          ·
            refine ⟨4381778400048943011895979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11684742400130514698389277 4381778400048943011895979)
            ·
              refine ⟨6572667600073414517843969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4381778400048943011895979 6572667600073414517843969)
              ·
                refine ⟨4929500700055060888382977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6572667600073414517843969 4929500700055060888382977)
                ·
                  refine ⟨3697125525041295666287233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4929500700055060888382977 3697125525041295666287233)
                  ·
                    refine ⟨2772844143780971749715425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3697125525041295666287233 2772844143780971749715425)
                    ·
                      refine ⟨2079633107835728812286569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2772844143780971749715425 2079633107835728812286569)
                      ·
                        rfl

theorem cell23_4050071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_4050071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050071 prefixEnd_4050071 := by exact prefixLift 4050071
  have htrace : WordTrace (prefixWord ++ tailWord_4050071) baseStart_4050071 baseEnd_4050071 := by
    simpa [prefixWord, tailWord_4050071, baseEnd_4050071] using wordTrace_append hprefix tailTrace_4050071
  have hstable : (prefixWord ++ tailWord_4050071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050071).length < 2 ^ (prefixWord ++ tailWord_4050071).sum := by decide
  have hdescent : baseEnd_4050071 < baseStart_4050071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050083 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 5]
def baseStart_4050083 : Nat := 118140960795 + 4050083 * 2 ^ 59
def prefixEnd_4050083 : Nat := 4983230072969 + 3 ^ 40 * 4050083 * 2
def baseEnd_4050083 : Nat := 2079639269603582765336513

theorem tailTrace_4050083 : CollatzResearch.WordTrace tailWord_4050083 prefixEnd_4050083 2079639269603582765336513 := by
  unfold tailWord_4050083
  simp only [CollatzResearch.WordTrace]
  refine ⟨147718662586248464952530903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98479108390832309968353935 147718662586248464952530903)
  ·
    refine ⟨221577993879372697428796355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147718662586248464952530903 221577993879372697428796355)
    ·
      refine ⟨332366990819059046143194533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221577993879372697428796355 332366990819059046143194533)
      ·
        refine ⟨62318810778573571151848975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332366990819059046143194533 62318810778573571151848975)
        ·
          refine ⟨93478216167860356727773463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62318810778573571151848975 93478216167860356727773463)
          ·
            refine ⟨140217324251790535091660195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93478216167860356727773463 140217324251790535091660195)
            ·
              refine ⟨210325986377685802637490293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140217324251790535091660195 210325986377685802637490293)
              ·
                refine ⟨19718061222908043997264715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210325986377685802637490293 19718061222908043997264715)
                ·
                  refine ⟨29577091834362065995897073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19718061222908043997264715 29577091834362065995897073)
                  ·
                    refine ⟨22182818875771549496922805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29577091834362065995897073 22182818875771549496922805)
                    ·
                      refine ⟨2079639269603582765336513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22182818875771549496922805 2079639269603582765336513)
                      ·
                        rfl

theorem cell23_4050083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_4050083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050083 prefixEnd_4050083 := by exact prefixLift 4050083
  have htrace : WordTrace (prefixWord ++ tailWord_4050083) baseStart_4050083 baseEnd_4050083 := by
    simpa [prefixWord, tailWord_4050083, baseEnd_4050083] using wordTrace_append hprefix tailTrace_4050083
  have hstable : (prefixWord ++ tailWord_4050083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050083).length < 2 ^ (prefixWord ++ tailWord_4050083).sum := by decide
  have hdescent : baseEnd_4050083 < baseStart_4050083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050087 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_4050087 : Nat := 118140960795 + 4050087 * 2 ^ 59
def prefixEnd_4050087 : Nat := 4983230072969 + 3 ^ 40 * 4050087 * 2
def baseEnd_4050087 : Nat := 2079641323526200749686495

theorem tailTrace_4050087 : CollatzResearch.WordTrace tailWord_4050087 prefixEnd_4050087 2079641323526200749686495 := by
  unfold tailWord_4050087
  simp only [CollatzResearch.WordTrace]
  refine ⟨147718808478233973635676515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98479205652155982423784343 147718808478233973635676515)
  ·
    refine ⟨221578212717350960453514773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147718808478233973635676515 221578212717350960453514773)
    ·
      refine ⟨10386478721125826271258505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 221578212717350960453514773 10386478721125826271258505)
      ·
        refine ⟨7789859040844369703443879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10386478721125826271258505 7789859040844369703443879)
        ·
          refine ⟨11684788561266554555165819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7789859040844369703443879 11684788561266554555165819)
          ·
            refine ⟨17527182841899831832748729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11684788561266554555165819 17527182841899831832748729)
            ·
              refine ⟨13145387131424873874561547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17527182841899831832748729 13145387131424873874561547)
              ·
                refine ⟨19718080697137310811842321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13145387131424873874561547 19718080697137310811842321)
                ·
                  refine ⟨14788560522852983108881741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19718080697137310811842321 14788560522852983108881741)
                  ·
                    refine ⟨5545710196069868665830653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14788560522852983108881741 5545710196069868665830653)
                    ·
                      refine ⟨2079641323526200749686495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5545710196069868665830653 2079641323526200749686495)
                      ·
                        rfl

theorem cell23_4050087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_4050087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050087 prefixEnd_4050087 := by exact prefixLift 4050087
  have htrace : WordTrace (prefixWord ++ tailWord_4050087) baseStart_4050087 baseEnd_4050087 := by
    simpa [prefixWord, tailWord_4050087, baseEnd_4050087] using wordTrace_append hprefix tailTrace_4050087
  have hstable : (prefixWord ++ tailWord_4050087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050087).length < 2 ^ (prefixWord ++ tailWord_4050087).sum := by decide
  have hdescent : baseEnd_4050087 < baseStart_4050087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050103 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 2, 8]
def baseStart_4050103 : Nat := 118140960795 + 4050103 * 2 ^ 59
def prefixEnd_4050103 : Nat := 4983230072969 + 3 ^ 40 * 4050103 * 2
def baseEnd_4050103 : Nat := 693216513072224229028807

theorem tailTrace_4050103 : CollatzResearch.WordTrace tailWord_4050103 prefixEnd_4050103 693216513072224229028807 := by
  unfold tailWord_4050103
  simp only [CollatzResearch.WordTrace]
  refine ⟨147719392046176008368258963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98479594697450672245505975 147719392046176008368258963)
  ·
    refine ⟨221579088069264012552388445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147719392046176008368258963 221579088069264012552388445)
    ·
      refine ⟨83092158025974004707145667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221579088069264012552388445 83092158025974004707145667)
      ·
        refine ⟨124638237038961007060718501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83092158025974004707145667 124638237038961007060718501)
        ·
          refine ⟨23369669444805188823884719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124638237038961007060718501 23369669444805188823884719)
          ·
            refine ⟨35054504167207783235827079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23369669444805188823884719 35054504167207783235827079)
            ·
              refine ⟨52581756250811674853740619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35054504167207783235827079 52581756250811674853740619)
              ·
                refine ⟨78872634376217512280610929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52581756250811674853740619 78872634376217512280610929)
                ·
                  refine ⟨59154475782163134210458197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78872634376217512280610929 59154475782163134210458197)
                  ·
                    refine ⟨693216513072224229028807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59154475782163134210458197 693216513072224229028807)
                    ·
                      rfl

theorem cell23_4050103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_4050103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050103 prefixEnd_4050103 := by exact prefixLift 4050103
  have htrace : WordTrace (prefixWord ++ tailWord_4050103) baseStart_4050103 baseEnd_4050103 := by
    simpa [prefixWord, tailWord_4050103, baseEnd_4050103] using wordTrace_append hprefix tailTrace_4050103
  have hstable : (prefixWord ++ tailWord_4050103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050103).length < 2 ^ (prefixWord ++ tailWord_4050103).sum := by decide
  have hdescent : baseEnd_4050103 < baseStart_4050103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050120 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 5, 4]
def baseStart_4050120 : Nat := 118140960795 + 4050120 * 2 ^ 59
def prefixEnd_4050120 : Nat := 4983230072969 + 3 ^ 40 * 4050120 * 2
def baseEnd_4050120 : Nat := 693219422795933040191281

theorem tailTrace_4050120 : CollatzResearch.WordTrace tailWord_4050120 prefixEnd_4050120 693219422795933040191281 := by
  unfold tailWord_4050120
  simp only [CollatzResearch.WordTrace]
  refine ⟨73860006043557210135813907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98480008058076280181085209 73860006043557210135813907)
  ·
    refine ⟨110790009065335815203720861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73860006043557210135813907 110790009065335815203720861)
    ·
      refine ⟨41546253399500930701395323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110790009065335815203720861 41546253399500930701395323)
      ·
        refine ⟨62319380099251396052092985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41546253399500930701395323 62319380099251396052092985)
        ·
          refine ⟨46739535074438547039069739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62319380099251396052092985 46739535074438547039069739)
          ·
            refine ⟨70109302611657820558604609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46739535074438547039069739 70109302611657820558604609)
            ·
              refine ⟨52581976958743365418953457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70109302611657820558604609 52581976958743365418953457)
              ·
                refine ⟨39436482719057524064215093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52581976958743365418953457 39436482719057524064215093)
                ·
                  refine ⟨3697170254911642881020165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39436482719057524064215093 3697170254911642881020165)
                  ·
                    refine ⟨693219422795933040191281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3697170254911642881020165 693219422795933040191281)
                    ·
                      rfl

theorem cell23_4050120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_4050120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050120 prefixEnd_4050120 := by exact prefixLift 4050120
  have htrace : WordTrace (prefixWord ++ tailWord_4050120) baseStart_4050120 baseEnd_4050120 := by
    simpa [prefixWord, tailWord_4050120, baseEnd_4050120] using wordTrace_append hprefix tailTrace_4050120
  have hstable : (prefixWord ++ tailWord_4050120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050120).length < 2 ^ (prefixWord ++ tailWord_4050120).sum := by decide
  have hdescent : baseEnd_4050120 < baseStart_4050120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050123 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 6]
def baseStart_4050123 : Nat := 118140960795 + 4050123 * 2 ^ 59
def prefixEnd_4050123 : Nat := 4983230072969 + 3 ^ 40 * 4050123 * 2
def baseEnd_4050123 : Nat := 2079659808829762608836329

theorem tailTrace_4050123 : CollatzResearch.WordTrace tailWord_4050123 prefixEnd_4050123 2079659808829762608836329 := by
  unfold tailWord_4050123
  simp only [CollatzResearch.WordTrace]
  refine ⟨147720121506103551783987023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98480081004069034522658015 147720121506103551783987023)
  ·
    refine ⟨221580182259155327675980535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147720121506103551783987023 221580182259155327675980535)
    ·
      refine ⟨332370273388732991513970803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221580182259155327675980535 332370273388732991513970803)
      ·
        refine ⟨498555410083099487270956205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332370273388732991513970803 498555410083099487270956205)
        ·
          refine ⟨186958278781162307726608577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498555410083099487270956205 186958278781162307726608577)
          ·
            refine ⟨140218709085871730794956433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186958278781162307726608577 140218709085871730794956433)
            ·
              refine ⟨105164031814403798096217325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140218709085871730794956433 105164031814403798096217325)
              ·
                refine ⟨39436511930401424286081497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105164031814403798096217325 39436511930401424286081497)
                ·
                  refine ⟨29577383947801068214561123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39436511930401424286081497 29577383947801068214561123)
                  ·
                    refine ⟨44366075921701602321841685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29577383947801068214561123 44366075921701602321841685)
                    ·
                      refine ⟨2079659808829762608836329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44366075921701602321841685 2079659808829762608836329)
                      ·
                        rfl

theorem cell23_4050123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 6].length) (baseStart_4050123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050123 prefixEnd_4050123 := by exact prefixLift 4050123
  have htrace : WordTrace (prefixWord ++ tailWord_4050123) baseStart_4050123 baseEnd_4050123 := by
    simpa [prefixWord, tailWord_4050123, baseEnd_4050123] using wordTrace_append hprefix tailTrace_4050123
  have hstable : (prefixWord ++ tailWord_4050123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050123).length < 2 ^ (prefixWord ++ tailWord_4050123).sum := by decide
  have hdescent : baseEnd_4050123 < baseStart_4050123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050134 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_4050134 : Nat := 118140960795 + 4050134 * 2 ^ 59
def prefixEnd_4050134 : Nat := 4983230072969 + 3 ^ 40 * 4050134 * 2
def baseEnd_4050134 : Nat := 2079665457116962065798779

theorem tailTrace_4050134 : CollatzResearch.WordTrace tailWord_4050134 prefixEnd_4050134 2079665457116962065798779 := by
  unfold tailWord_4050134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9232532669316481291414841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98480348472709133775091637 9232532669316481291414841)
  ·
    refine ⟨6924399501987360968561131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9232532669316481291414841 6924399501987360968561131)
    ·
      refine ⟨10386599252981041452841697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6924399501987360968561131 10386599252981041452841697)
      ·
        refine ⟨7789949439735781089631273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10386599252981041452841697 7789949439735781089631273)
        ·
          refine ⟨5842462079801835817223455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7789949439735781089631273 5842462079801835817223455)
          ·
            refine ⟨8763693119702753725835183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5842462079801835817223455 8763693119702753725835183)
            ·
              refine ⟨13145539679554130588752775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8763693119702753725835183 13145539679554130588752775)
              ·
                refine ⟨19718309519331195883129163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13145539679554130588752775 19718309519331195883129163)
                ·
                  refine ⟨29577464278996793824693745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19718309519331195883129163 29577464278996793824693745)
                  ·
                    refine ⟨22183098209247595368520309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29577464278996793824693745 22183098209247595368520309)
                    ·
                      refine ⟨2079665457116962065798779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22183098209247595368520309 2079665457116962065798779)
                      ·
                        rfl

theorem cell23_4050134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_4050134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050134 prefixEnd_4050134 := by exact prefixLift 4050134
  have htrace : WordTrace (prefixWord ++ tailWord_4050134) baseStart_4050134 baseEnd_4050134 := by
    simpa [prefixWord, tailWord_4050134, baseEnd_4050134] using wordTrace_append hprefix tailTrace_4050134
  have hstable : (prefixWord ++ tailWord_4050134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050134).length < 2 ^ (prefixWord ++ tailWord_4050134).sum := by decide
  have hdescent : baseEnd_4050134 < baseStart_4050134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050221 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_4050221 : Nat := 118140960795 + 4050221 * 2 ^ 59
def prefixEnd_4050221 : Nat := 4983230072969 + 3 ^ 40 * 4050221 * 2
def baseEnd_4050221 : Nat := 2079710129933903225410879

theorem tailTrace_4050221 : CollatzResearch.WordTrace tailWord_4050221 prefixEnd_4050221 2079710129933903225410879 := by
  unfold tailWord_4050221
  simp only [CollatzResearch.WordTrace]
  refine ⟨147723695859748514521054517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98482463906499009680703011 147723695859748514521054517)
  ·
    refine ⟨13849096486851423236348861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147723695859748514521054517 13849096486851423236348861)
    ·
      refine ⟨5193411182569283713630823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13849096486851423236348861 5193411182569283713630823)
      ·
        refine ⟨7790116773853925570446235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5193411182569283713630823 7790116773853925570446235)
        ·
          refine ⟨11685175160780888355669353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7790116773853925570446235 11685175160780888355669353)
          ·
            refine ⟨8763881370585666266752015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11685175160780888355669353 8763881370585666266752015)
            ·
              refine ⟨13145822055878499400128023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8763881370585666266752015 13145822055878499400128023)
              ·
                refine ⟨19718733083817749100192035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13145822055878499400128023 19718733083817749100192035)
                ·
                  refine ⟨29578099625726623650288053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19718733083817749100192035 29578099625726623650288053)
                  ·
                    refine ⟨2772946839911870967214505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29578099625726623650288053 2772946839911870967214505)
                    ·
                      refine ⟨2079710129933903225410879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2772946839911870967214505 2079710129933903225410879)
                      ·
                        rfl

theorem cell23_4050221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_4050221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050221 prefixEnd_4050221 := by exact prefixLift 4050221
  have htrace : WordTrace (prefixWord ++ tailWord_4050221) baseStart_4050221 baseEnd_4050221 := by
    simpa [prefixWord, tailWord_4050221, baseEnd_4050221] using wordTrace_append hprefix tailTrace_4050221
  have hstable : (prefixWord ++ tailWord_4050221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050221).length < 2 ^ (prefixWord ++ tailWord_4050221).sum := by decide
  have hdescent : baseEnd_4050221 < baseStart_4050221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050228 : List Nat := [2, 5, 1, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_4050228 : Nat := 118140960795 + 4050228 * 2 ^ 59
def prefixEnd_4050228 : Nat := 4983230072969 + 3 ^ 40 * 4050228 * 2
def baseEnd_4050228 : Nat := 2079713724298484698023347

theorem tailTrace_4050228 : CollatzResearch.WordTrace tailWord_4050228 prefixEnd_4050228 2079713724298484698023347 := by
  unfold tailWord_4050228
  simp only [CollatzResearch.WordTrace]
  refine ⟨73861975585361577358279669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98482634113815436477706225 73861975585361577358279669)
  ·
    refine ⟨6924560211127647877338719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73861975585361577358279669 6924560211127647877338719)
    ·
      refine ⟨10386840316691471816008079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6924560211127647877338719 10386840316691471816008079)
      ·
        refine ⟨15580260475037207724012119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10386840316691471816008079 15580260475037207724012119)
        ·
          refine ⟨23370390712555811586018179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15580260475037207724012119 23370390712555811586018179)
          ·
            refine ⟨35055586068833717379027269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23370390712555811586018179 35055586068833717379027269)
            ·
              refine ⟨6572922387906322008567613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35055586068833717379027269 6572922387906322008567613)
              ·
                refine ⟨2464845895464870753212855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6572922387906322008567613 2464845895464870753212855)
                ·
                  refine ⟨3697268843197306129819283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464845895464870753212855 3697268843197306129819283)
                  ·
                    refine ⟨5545903264795959194728925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3697268843197306129819283 5545903264795959194728925)
                    ·
                      refine ⟨2079713724298484698023347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5545903264795959194728925 2079713724298484698023347)
                      ·
                        rfl

theorem cell23_4050228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_4050228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050228 prefixEnd_4050228 := by exact prefixLift 4050228
  have htrace : WordTrace (prefixWord ++ tailWord_4050228) baseStart_4050228 baseEnd_4050228 := by
    simpa [prefixWord, tailWord_4050228, baseEnd_4050228] using wordTrace_append hprefix tailTrace_4050228
  have hstable : (prefixWord ++ tailWord_4050228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050228).length < 2 ^ (prefixWord ++ tailWord_4050228).sum := by decide
  have hdescent : baseEnd_4050228 < baseStart_4050228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050234 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2]
def baseStart_4050234 : Nat := 118140960795 + 4050234 * 2 ^ 59
def prefixEnd_4050234 : Nat := 4983230072969 + 3 ^ 40 * 4050234 * 2
def baseEnd_4050234 : Nat := 2079716805182411674548319

theorem tailTrace_4050234 : CollatzResearch.WordTrace tailWord_4050234 prefixEnd_4050234 2079716805182411674548319 := by
  unfold tailWord_4050234
  simp only [CollatzResearch.WordTrace]
  refine ⟨36931042502175354435319439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98482780005800945160851837 36931042502175354435319439)
  ·
    refine ⟨55396563753263031652979159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36931042502175354435319439 55396563753263031652979159)
    ·
      refine ⟨83094845629894547479468739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55396563753263031652979159 83094845629894547479468739)
      ·
        refine ⟨124642268444841821219203109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83094845629894547479468739 124642268444841821219203109)
        ·
          refine ⟨23370425333407841478600583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124642268444841821219203109 23370425333407841478600583)
          ·
            refine ⟨35055638000111762217900875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23370425333407841478600583 35055638000111762217900875)
            ·
              refine ⟨52583457000167643326851313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35055638000111762217900875 52583457000167643326851313)
              ·
                refine ⟨39437592750125732495138485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52583457000167643326851313 39437592750125732495138485)
                ·
                  refine ⟨3697274320324287421419233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39437592750125732495138485 3697274320324287421419233)
                  ·
                    refine ⟨2772955740243215566064425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3697274320324287421419233 2772955740243215566064425)
                    ·
                      refine ⟨2079716805182411674548319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2772955740243215566064425 2079716805182411674548319)
                      ·
                        rfl

theorem cell23_4050234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2].length) (baseStart_4050234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050234 prefixEnd_4050234 := by exact prefixLift 4050234
  have htrace : WordTrace (prefixWord ++ tailWord_4050234) baseStart_4050234 baseEnd_4050234 := by
    simpa [prefixWord, tailWord_4050234, baseEnd_4050234] using wordTrace_append hprefix tailTrace_4050234
  have hstable : (prefixWord ++ tailWord_4050234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050234).length < 2 ^ (prefixWord ++ tailWord_4050234).sum := by decide
  have hdescent : baseEnd_4050234 < baseStart_4050234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050261 : List Nat := [1, 3, 2, 2, 3, 2, 3, 1, 2, 4]
def baseStart_4050261 : Nat := 118140960795 + 4050261 * 2 ^ 59
def prefixEnd_4050261 : Nat := 4983230072969 + 3 ^ 40 * 4050261 * 2
def baseEnd_4050261 : Nat := 693243556386694356303565

theorem tailTrace_4050261 : CollatzResearch.WordTrace tailWord_4050261 prefixEnd_4050261 693243556386694356303565 := by
  unfold tailWord_4050261
  simp only [CollatzResearch.WordTrace]
  refine ⟨147725154779603601352510637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98483436519735734235007091 147725154779603601352510637)
  ·
    refine ⟨55396933042351350507191489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147725154779603601352510637 55396933042351350507191489)
    ·
      refine ⟨41547699781763512880393617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55396933042351350507191489 41547699781763512880393617)
      ·
        refine ⟨31160774836322634660295213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41547699781763512880393617 31160774836322634660295213)
        ·
          refine ⟨11685290563620987997610705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31160774836322634660295213 11685290563620987997610705)
          ·
            refine ⟨8763967922715740998208029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11685290563620987997610705 8763967922715740998208029)
            ·
              refine ⟨3286487971018402874328011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8763967922715740998208029 3286487971018402874328011)
              ·
                refine ⟨4929731956527604311492017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286487971018402874328011 4929731956527604311492017)
                ·
                  refine ⟨3697298967395703233619013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4929731956527604311492017 3697298967395703233619013)
                  ·
                    refine ⟨693243556386694356303565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3697298967395703233619013 693243556386694356303565)
                    ·
                      rfl

theorem cell23_4050261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_4050261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050261 prefixEnd_4050261 := by exact prefixLift 4050261
  have htrace : WordTrace (prefixWord ++ tailWord_4050261) baseStart_4050261 baseEnd_4050261 := by
    simpa [prefixWord, tailWord_4050261, baseEnd_4050261] using wordTrace_append hprefix tailTrace_4050261
  have hstable : (prefixWord ++ tailWord_4050261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050261).length < 2 ^ (prefixWord ++ tailWord_4050261).sum := by decide
  have hdescent : baseEnd_4050261 < baseStart_4050261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050284 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 3]
def baseStart_4050284 : Nat := 118140960795 + 4050284 * 2 ^ 59
def prefixEnd_4050284 : Nat := 4983230072969 + 3 ^ 40 * 4050284 * 2
def baseEnd_4050284 : Nat := 2079742479215136478923089

theorem tailTrace_4050284 : CollatzResearch.WordTrace tailWord_4050284 prefixEnd_4050284 2079742479215136478923089 := by
  unfold tailWord_4050284
  simp only [CollatzResearch.WordTrace]
  refine ⟨73862996829260138140298953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98483995772346850853731937 73862996829260138140298953)
  ·
    refine ⟨55397247621945103605224215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73862996829260138140298953 55397247621945103605224215)
    ·
      refine ⟨83095871432917655407836323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55397247621945103605224215 83095871432917655407836323)
      ·
        refine ⟨124643807149376483111754485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83095871432917655407836323 124643807149376483111754485)
        ·
          refine ⟨11685356920254045291726983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124643807149376483111754485 11685356920254045291726983)
          ·
            refine ⟨17528035380381067937590475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11685356920254045291726983 17528035380381067937590475)
            ·
              refine ⟨26292053070571601906385713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17528035380381067937590475 26292053070571601906385713)
              ·
                refine ⟨19719039802928701429789285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26292053070571601906385713 19719039802928701429789285)
                ·
                  refine ⟨3697319963049131518085491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19719039802928701429789285 3697319963049131518085491)
                  ·
                    refine ⟨5545979944573697277128237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3697319963049131518085491 5545979944573697277128237)
                    ·
                      refine ⟨2079742479215136478923089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5545979944573697277128237 2079742479215136478923089)
                      ·
                        rfl

theorem cell23_4050284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_4050284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050284 prefixEnd_4050284 := by exact prefixLift 4050284
  have htrace : WordTrace (prefixWord ++ tailWord_4050284) baseStart_4050284 baseEnd_4050284 := by
    simpa [prefixWord, tailWord_4050284, baseEnd_4050284] using wordTrace_append hprefix tailTrace_4050284
  have hstable : (prefixWord ++ tailWord_4050284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050284).length < 2 ^ (prefixWord ++ tailWord_4050284).sum := by decide
  have hdescent : baseEnd_4050284 < baseStart_4050284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050285 : List Nat := [1, 5, 1, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_4050285 : Nat := 118140960795 + 4050285 * 2 ^ 59
def prefixEnd_4050285 : Nat := 4983230072969 + 3 ^ 40 * 4050285 * 2
def baseEnd_4050285 : Nat := 2079742992695790975010585

theorem tailTrace_4050285 : CollatzResearch.WordTrace tailWord_4050285 prefixEnd_4050285 2079742992695790975010585 := by
  unfold tailWord_4050285
  simp only [CollatzResearch.WordTrace]
  refine ⟨147726030131516653451384309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98484020087677768967589539 147726030131516653451384309)
  ·
    refine ⟨13849315324829686261067279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147726030131516653451384309 13849315324829686261067279)
    ·
      refine ⟨20773972987244529391600919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13849315324829686261067279 20773972987244529391600919)
      ·
        refine ⟨31160959480866794087401379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20773972987244529391600919 31160959480866794087401379)
        ·
          refine ⟨46741439221300191131102069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31160959480866794087401379 46741439221300191131102069)
          ·
            refine ⟨4382009926996892918540819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46741439221300191131102069 4382009926996892918540819)
            ·
              refine ⟨6573014890495339377811229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382009926996892918540819 6573014890495339377811229)
              ·
                refine ⟨2464880583935752266679211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6573014890495339377811229 2464880583935752266679211)
                ·
                  refine ⟨3697320875903628400018817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464880583935752266679211 3697320875903628400018817)
                  ·
                    refine ⟨2772990656927721300014113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3697320875903628400018817 2772990656927721300014113)
                    ·
                      refine ⟨2079742992695790975010585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2772990656927721300014113 2079742992695790975010585)
                      ·
                        rfl

theorem cell23_4050285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_4050285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050285 prefixEnd_4050285 := by exact prefixLift 4050285
  have htrace : WordTrace (prefixWord ++ tailWord_4050285) baseStart_4050285 baseEnd_4050285 := by
    simpa [prefixWord, tailWord_4050285, baseEnd_4050285] using wordTrace_append hprefix tailTrace_4050285
  have hstable : (prefixWord ++ tailWord_4050285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050285).length < 2 ^ (prefixWord ++ tailWord_4050285).sum := by decide
  have hdescent : baseEnd_4050285 < baseStart_4050285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050302 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4050302 : Nat := 118140960795 + 4050302 * 2 ^ 59
def prefixEnd_4050302 : Nat := 4983230072969 + 3 ^ 40 * 4050302 * 2
def baseEnd_4050302 : Nat := 2079751721866917408498007

theorem tailTrace_4050302 : CollatzResearch.WordTrace tailWord_4050302 prefixEnd_4050302 2079751721866917408498007 := by
  unfold tailWord_4050302
  simp only [CollatzResearch.WordTrace]
  refine ⟨18465831271556883169344145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98484433448303376903168773 18465831271556883169344145)
  ·
    refine ⟨13849373453667662377008109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18465831271556883169344145 13849373453667662377008109)
    ·
      refine ⟨5193515045125373391378041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13849373453667662377008109 5193515045125373391378041)
      ·
        refine ⟨3895136283844030043533531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5193515045125373391378041 3895136283844030043533531)
        ·
          refine ⟨5842704425766045065300297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3895136283844030043533531 5842704425766045065300297)
          ·
            refine ⟨4382028319324533798975223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5842704425766045065300297 4382028319324533798975223)
            ·
              refine ⟨6573042478986800698462835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382028319324533798975223 6573042478986800698462835)
              ·
                refine ⟨9859563718480201047694253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6573042478986800698462835 9859563718480201047694253)
                ·
                  refine ⟨3697336394430075392885345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9859563718480201047694253 3697336394430075392885345)
                  ·
                    refine ⟨2773002295822556544664009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3697336394430075392885345 2773002295822556544664009)
                    ·
                      refine ⟨2079751721866917408498007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773002295822556544664009 2079751721866917408498007)
                      ·
                        rfl

theorem cell23_4050302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4050302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050302 prefixEnd_4050302 := by exact prefixLift 4050302
  have htrace : WordTrace (prefixWord ++ tailWord_4050302) baseStart_4050302 baseEnd_4050302 := by
    simpa [prefixWord, tailWord_4050302, baseEnd_4050302] using wordTrace_append hprefix tailTrace_4050302
  have hstable : (prefixWord ++ tailWord_4050302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050302).length < 2 ^ (prefixWord ++ tailWord_4050302).sum := by decide
  have hdescent : baseEnd_4050302 < baseStart_4050302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050318 : List Nat := [4, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_4050318 : Nat := 118140960795 + 4050318 * 2 ^ 59
def prefixEnd_4050318 : Nat := 4983230072969 + 3 ^ 40 * 4050318 * 2
def baseEnd_4050318 : Nat := 2079759937557389345897933

theorem tailTrace_4050318 : CollatzResearch.WordTrace tailWord_4050318 prefixEnd_4050318 2079759937557389345897933 := by
  unfold tailWord_4050318
  simp only [CollatzResearch.WordTrace]
  refine ⟨18465904217549637510916951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98484822493598066724890405 18465904217549637510916951)
  ·
    refine ⟨27698856326324456266375427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18465904217549637510916951 27698856326324456266375427)
    ·
      refine ⟨41548284489486684399563141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27698856326324456266375427 41548284489486684399563141)
      ·
        refine ⟨7790303341778753324918089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41548284489486684399563141 7790303341778753324918089)
        ·
          refine ⟨5842727506334064993688567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7790303341778753324918089 5842727506334064993688567)
          ·
            refine ⟨8764091259501097490532851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5842727506334064993688567 8764091259501097490532851)
            ·
              refine ⟨13146136889251646235799277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764091259501097490532851 13146136889251646235799277)
              ·
                refine ⟨4929801333469367338424729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13146136889251646235799277 4929801333469367338424729)
                ·
                  refine ⟨3697351000102025503818547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4929801333469367338424729 3697351000102025503818547)
                  ·
                    refine ⟨5546026500153038255727821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3697351000102025503818547 5546026500153038255727821)
                    ·
                      refine ⟨2079759937557389345897933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5546026500153038255727821 2079759937557389345897933)
                      ·
                        rfl

theorem cell23_4050318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_4050318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050318 prefixEnd_4050318 := by exact prefixLift 4050318
  have htrace : WordTrace (prefixWord ++ tailWord_4050318) baseStart_4050318 baseEnd_4050318 := by
    simpa [prefixWord, tailWord_4050318, baseEnd_4050318] using wordTrace_append hprefix tailTrace_4050318
  have hstable : (prefixWord ++ tailWord_4050318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050318).length < 2 ^ (prefixWord ++ tailWord_4050318).sum := by decide
  have hdescent : baseEnd_4050318 < baseStart_4050318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050394 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 2, 5]
def baseStart_4050394 : Nat := 118140960795 + 4050394 * 2 ^ 59
def prefixEnd_4050394 : Nat := 4983230072969 + 3 ^ 40 * 4050394 * 2
def baseEnd_4050394 : Nat := 693266320695710349515861

theorem tailTrace_4050394 : CollatzResearch.WordTrace tailWord_4050394 prefixEnd_4050394 693266320695710349515861 := by
  unfold tailWord_4050394
  simp only [CollatzResearch.WordTrace]
  refine ⟨36932501422030441266775559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98486670458747843378068157 36932501422030441266775559)
  ·
    refine ⟨55398752133045661900163339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36932501422030441266775559 55398752133045661900163339)
    ·
      refine ⟨83098128199568492850245009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55398752133045661900163339 83098128199568492850245009)
      ·
        refine ⟨62323596149676369637683757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83098128199568492850245009 62323596149676369637683757)
        ·
          refine ⟨23371348556128638614131409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62323596149676369637683757 23371348556128638614131409)
          ·
            refine ⟨17528511417096478960598557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23371348556128638614131409 17528511417096478960598557)
            ·
              refine ⟨6573191781411179610224459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17528511417096478960598557 6573191781411179610224459)
              ·
                refine ⟨9859787672116769415336689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6573191781411179610224459 9859787672116769415336689)
                ·
                  refine ⟨7394840754087577061502517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9859787672116769415336689 7394840754087577061502517)
                  ·
                    refine ⟨693266320695710349515861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7394840754087577061502517 693266320695710349515861)
                    ·
                      rfl

theorem cell23_4050394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_4050394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050394 prefixEnd_4050394 := by exact prefixLift 4050394
  have htrace : WordTrace (prefixWord ++ tailWord_4050394) baseStart_4050394 baseEnd_4050394 := by
    simpa [prefixWord, tailWord_4050394, baseEnd_4050394] using wordTrace_append hprefix tailTrace_4050394
  have hstable : (prefixWord ++ tailWord_4050394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050394).length < 2 ^ (prefixWord ++ tailWord_4050394).sum := by decide
  have hdescent : baseEnd_4050394 < baseStart_4050394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050414 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_4050414 : Nat := 118140960795 + 4050414 * 2 ^ 59
def prefixEnd_4050414 : Nat := 4983230072969 + 3 ^ 40 * 4050414 * 2
def baseEnd_4050414 : Nat := 2079809231700220970297491

theorem tailTrace_4050414 : CollatzResearch.WordTrace tailWord_4050414 prefixEnd_4050414 2079809231700220970297491 := by
  unfold tailWord_4050414
  simp only [CollatzResearch.WordTrace]
  refine ⟨18466341893506163560353787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98487156765366205655220197 18466341893506163560353787)
  ·
    refine ⟨27699512840259245340530681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18466341893506163560353787 27699512840259245340530681)
    ·
      refine ⟨20774634630194434005398011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27699512840259245340530681 20774634630194434005398011)
      ·
        refine ⟨31161951945291651008097017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20774634630194434005398011 31161951945291651008097017)
        ·
          refine ⟨23371463958968738256072763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31161951945291651008097017 23371463958968738256072763)
          ·
            refine ⟨35057195938453107384109145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23371463958968738256072763 35057195938453107384109145)
            ·
              refine ⟨26292896953839830538081859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35057195938453107384109145 26292896953839830538081859)
              ·
                refine ⟨39439345430759745807122789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26292896953839830538081859 39439345430759745807122789)
                ·
                  refine ⟨7394877268267452338835523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39439345430759745807122789 7394877268267452338835523)
                  ·
                    refine ⟨11092315902401178508253285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7394877268267452338835523 11092315902401178508253285)
                    ·
                      refine ⟨2079809231700220970297491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11092315902401178508253285 2079809231700220970297491)
                      ·
                        rfl

theorem cell23_4050414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_4050414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050414 prefixEnd_4050414 := by exact prefixLift 4050414
  have htrace : WordTrace (prefixWord ++ tailWord_4050414) baseStart_4050414 baseEnd_4050414 := by
    simpa [prefixWord, tailWord_4050414, baseEnd_4050414] using wordTrace_append hprefix tailTrace_4050414
  have hstable : (prefixWord ++ tailWord_4050414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050414).length < 2 ^ (prefixWord ++ tailWord_4050414).sum := by decide
  have hdescent : baseEnd_4050414 < baseStart_4050414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050424 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 3, 4]
def baseStart_4050424 : Nat := 118140960795 + 4050424 * 2 ^ 59
def prefixEnd_4050424 : Nat := 4983230072969 + 3 ^ 40 * 4050424 * 2
def baseEnd_4050424 : Nat := 693271455502255310390815

theorem tailTrace_4050424 : CollatzResearch.WordTrace tailWord_4050424 prefixEnd_4050424 693271455502255310390815 := by
  unfold tailWord_4050424
  simp only [CollatzResearch.WordTrace]
  refine ⟨73865549939006540095347163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98487399918675386793796217 73865549939006540095347163)
  ·
    refine ⟨110798324908509810143020745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73865549939006540095347163 110798324908509810143020745)
    ·
      refine ⟨83098743681382357607265559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110798324908509810143020745 83098743681382357607265559)
      ·
        refine ⟨124648115522073536410898339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83098743681382357607265559 124648115522073536410898339)
        ·
          refine ⟨186972173283110304616347509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124648115522073536410898339 186972173283110304616347509)
          ·
            refine ⟨17528641245291591057782579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186972173283110304616347509 17528641245291591057782579)
            ·
              refine ⟨26292961867937386586673869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17528641245291591057782579 26292961867937386586673869)
              ·
                refine ⟨9859860700476519970002701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26292961867937386586673869 9859860700476519970002701)
                ·
                  refine ⟨3697447762678694988751013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9859860700476519970002701 3697447762678694988751013)
                  ·
                    refine ⟨693271455502255310390815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3697447762678694988751013 693271455502255310390815)
                    ·
                      rfl

theorem cell23_4050424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_4050424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050424 prefixEnd_4050424 := by exact prefixLift 4050424
  have htrace : WordTrace (prefixWord ++ tailWord_4050424) baseStart_4050424 baseEnd_4050424 := by
    simpa [prefixWord, tailWord_4050424, baseEnd_4050424] using wordTrace_append hprefix tailTrace_4050424
  have hstable : (prefixWord ++ tailWord_4050424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050424).length < 2 ^ (prefixWord ++ tailWord_4050424).sum := by decide
  have hdescent : baseEnd_4050424 < baseStart_4050424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050508 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 2, 3, 2]
def baseStart_4050508 : Nat := 118140960795 + 4050508 * 2 ^ 59
def prefixEnd_4050508 : Nat := 4983230072969 + 3 ^ 40 * 4050508 * 2
def baseEnd_4050508 : Nat := 2079857498881743602522059

theorem tailTrace_4050508 : CollatzResearch.WordTrace tailWord_4050508 prefixEnd_4050508 2079857498881743602522059 := by
  unfold tailWord_4050508
  simp only [CollatzResearch.WordTrace]
  refine ⟨73867081804854381268376089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98489442406472508357834785 73867081804854381268376089)
  ·
    refine ⟨55400311353640785951282067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73867081804854381268376089 55400311353640785951282067)
    ·
      refine ⟨83100467030461178926923101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55400311353640785951282067 83100467030461178926923101)
      ·
        refine ⟨31162675136422942097596163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83100467030461178926923101 31162675136422942097596163)
        ·
          refine ⟨46744012704634413146394245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31162675136422942097596163 46744012704634413146394245)
          ·
            refine ⟨8764502382118952464948921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46744012704634413146394245 8764502382118952464948921)
            ·
              refine ⟨6573376786589214348711691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8764502382118952464948921 6573376786589214348711691)
              ·
                refine ⟨9860065179883821523067537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6573376786589214348711691 9860065179883821523067537)
                ·
                  refine ⟨7395048884912866142300653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9860065179883821523067537 7395048884912866142300653)
                  ·
                    refine ⟨2773143331842324803362745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7395048884912866142300653 2773143331842324803362745)
                    ·
                      refine ⟨2079857498881743602522059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773143331842324803362745 2079857498881743602522059)
                      ·
                        rfl

theorem cell23_4050508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_4050508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050508 prefixEnd_4050508 := by exact prefixLift 4050508
  have htrace : WordTrace (prefixWord ++ tailWord_4050508) baseStart_4050508 baseEnd_4050508 := by
    simpa [prefixWord, tailWord_4050508, baseEnd_4050508] using wordTrace_append hprefix tailTrace_4050508
  have hstable : (prefixWord ++ tailWord_4050508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050508).length < 2 ^ (prefixWord ++ tailWord_4050508).sum := by decide
  have hdescent : baseEnd_4050508 < baseStart_4050508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050514 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_4050514 : Nat := 118140960795 + 4050514 * 2 ^ 59
def prefixEnd_4050514 : Nat := 4983230072969 + 3 ^ 40 * 4050514 * 2
def baseEnd_4050514 : Nat := 693286859921890193015677

theorem tailTrace_4050514 : CollatzResearch.WordTrace tailWord_4050514 prefixEnd_4050514 693286859921890193015677 := by
  unfold tailWord_4050514
  simp only [CollatzResearch.WordTrace]
  refine ⟨36933595611921756390367649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98489588298458017040980397 36933595611921756390367649)
  ·
    refine ⟨27700196708941317292775737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36933595611921756390367649 27700196708941317292775737)
    ·
      refine ⟨20775147531705987969581803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27700196708941317292775737 20775147531705987969581803)
      ·
        refine ⟨31162721297558981954372705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20775147531705987969581803 31162721297558981954372705)
        ·
          refine ⟨23372040973169236465779529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31162721297558981954372705 23372040973169236465779529)
          ·
            refine ⟨17529030729876927349334647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23372040973169236465779529 17529030729876927349334647)
            ·
              refine ⟨26293546094815391024001971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17529030729876927349334647 26293546094815391024001971)
              ·
                refine ⟨39440319142223086536002957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26293546094815391024001971 39440319142223086536002957)
                ·
                  refine ⟨14790119678333657451001109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39440319142223086536002957 14790119678333657451001109)
                  ·
                    refine ⟨693286859921890193015677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14790119678333657451001109 693286859921890193015677)
                    ·
                      rfl

theorem cell23_4050514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_4050514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050514 prefixEnd_4050514 := by exact prefixLift 4050514
  have htrace : WordTrace (prefixWord ++ tailWord_4050514) baseStart_4050514 baseEnd_4050514 := by
    simpa [prefixWord, tailWord_4050514, baseEnd_4050514] using wordTrace_append hprefix tailTrace_4050514
  have hstable : (prefixWord ++ tailWord_4050514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050514).length < 2 ^ (prefixWord ++ tailWord_4050514).sum := by decide
  have hdescent : baseEnd_4050514 < baseStart_4050514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050531 : List Nat := [1, 1, 1, 5, 1, 3, 1, 4, 2, 4]
def baseStart_4050531 : Nat := 118140960795 + 4050531 * 2 ^ 59
def prefixEnd_4050531 : Nat := 4983230072969 + 3 ^ 40 * 4050531 * 2
def baseEnd_4050531 : Nat := 693289769645599004178151

theorem tailTrace_4050531 : CollatzResearch.WordTrace tailWord_4050531 prefixEnd_4050531 693289769645599004178151 := by
  unfold tailWord_4050531
  simp only [CollatzResearch.WordTrace]
  refine ⟨147735002488625437464839447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98490001659083624976559631 147735002488625437464839447)
  ·
    refine ⟨221602503732938156197259171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147735002488625437464839447 221602503732938156197259171)
    ·
      refine ⟨332403755599407234295888757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221602503732938156197259171 332403755599407234295888757)
      ·
        refine ⟨31162852087444428215239571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332403755599407234295888757 31162852087444428215239571)
        ·
          refine ⟨46744278131166642322859357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31162852087444428215239571 46744278131166642322859357)
          ·
            refine ⟨17529104299187490871072259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46744278131166642322859357 17529104299187490871072259)
            ·
              refine ⟨26293656448781236306608389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17529104299187490871072259 26293656448781236306608389)
              ·
                refine ⟨4930060584146481807489073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26293656448781236306608389 4930060584146481807489073)
                ·
                  refine ⟨3697545438109861355616805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4930060584146481807489073 3697545438109861355616805)
                  ·
                    refine ⟨693289769645599004178151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3697545438109861355616805 693289769645599004178151)
                    ·
                      rfl

theorem cell23_4050531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 4].length) (baseStart_4050531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050531 prefixEnd_4050531 := by exact prefixLift 4050531
  have htrace : WordTrace (prefixWord ++ tailWord_4050531) baseStart_4050531 baseEnd_4050531 := by
    simpa [prefixWord, tailWord_4050531, baseEnd_4050531] using wordTrace_append hprefix tailTrace_4050531
  have hstable : (prefixWord ++ tailWord_4050531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050531).length < 2 ^ (prefixWord ++ tailWord_4050531).sum := by decide
  have hdescent : baseEnd_4050531 < baseStart_4050531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050532 : List Nat := [2, 3, 1, 1, 2, 5, 2, 2, 1, 1, 3]
def baseStart_4050532 : Nat := 118140960795 + 4050532 * 2 ^ 59
def prefixEnd_4050532 : Nat := 4983230072969 + 3 ^ 40 * 4050532 * 2
def baseEnd_4050532 : Nat := 2079869822417451508621949

theorem tailTrace_4050532 : CollatzResearch.WordTrace tailWord_4050532 prefixEnd_4050532 2079869822417451508621949 := by
  unfold tailWord_4050532
  simp only [CollatzResearch.WordTrace]
  refine ⟨73867519480810907317812925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98490025974414543090417233 73867519480810907317812925)
  ·
    refine ⟨27700319805304090244179847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73867519480810907317812925 27700319805304090244179847)
    ·
      refine ⟨41550479707956135366269771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27700319805304090244179847 41550479707956135366269771)
      ·
        refine ⟨62325719561934203049404657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41550479707956135366269771 62325719561934203049404657)
        ·
          refine ⟨46744289671450652287053493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62325719561934203049404657 46744289671450652287053493)
          ·
            refine ⟨4382277156698498651911265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46744289671450652287053493 4382277156698498651911265)
            ·
              refine ⟨3286707867523873988933449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4382277156698498651911265 3286707867523873988933449)
              ·
                refine ⟨2465030900642905491700087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3286707867523873988933449 2465030900642905491700087)
                ·
                  refine ⟨3697546350964358237550131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465030900642905491700087 3697546350964358237550131)
                  ·
                    refine ⟨5546319526446537356325197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3697546350964358237550131 5546319526446537356325197)
                    ·
                      refine ⟨2079869822417451508621949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5546319526446537356325197 2079869822417451508621949)
                      ·
                        rfl

theorem cell23_4050532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_4050532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050532 prefixEnd_4050532 := by exact prefixLift 4050532
  have htrace : WordTrace (prefixWord ++ tailWord_4050532) baseStart_4050532 baseEnd_4050532 := by
    simpa [prefixWord, tailWord_4050532, baseEnd_4050532] using wordTrace_append hprefix tailTrace_4050532
  have hstable : (prefixWord ++ tailWord_4050532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050532).length < 2 ^ (prefixWord ++ tailWord_4050532).sum := by decide
  have hdescent : baseEnd_4050532 < baseStart_4050532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050544 : List Nat := [2, 1, 1, 1, 6, 1, 3, 8]
def baseStart_4050544 : Nat := 118140960795 + 4050544 * 2 ^ 59
def prefixEnd_4050544 : Nat := 4983230072969 + 3 ^ 40 * 4050544 * 2
def baseEnd_4050544 : Nat := 77032443858715017098959

theorem tailTrace_4050544 : CollatzResearch.WordTrace tailWord_4050544 prefixEnd_4050544 77032443858715017098959 := by
  unfold tailWord_4050544
  simp only [CollatzResearch.WordTrace]
  refine ⟨73867738318789170342531343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98490317758385560456708457 73867738318789170342531343)
  ·
    refine ⟨110801607478183755513797015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73867738318789170342531343 110801607478183755513797015)
    ·
      refine ⟨166202411217275633270695523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110801607478183755513797015 166202411217275633270695523)
      ·
        refine ⟨249303616825913449906043285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166202411217275633270695523 249303616825913449906043285)
        ·
          refine ⟨11686107038714692964345779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 249303616825913449906043285 11686107038714692964345779)
          ·
            refine ⟨17529160558072039446518669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11686107038714692964345779 17529160558072039446518669)
            ·
              refine ⟨6573435209277014792444501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17529160558072039446518669 6573435209277014792444501)
              ·
                refine ⟨77032443858715017098959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6573435209277014792444501 77032443858715017098959)
                ·
                  rfl

theorem cell23_4050544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 8].length) (baseStart_4050544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050544 prefixEnd_4050544 := by exact prefixLift 4050544
  have htrace : WordTrace (prefixWord ++ tailWord_4050544) baseStart_4050544 baseEnd_4050544 := by
    simpa [prefixWord, tailWord_4050544, baseEnd_4050544] using wordTrace_append hprefix tailTrace_4050544
  have hstable : (prefixWord ++ tailWord_4050544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050544).length < 2 ^ (prefixWord ++ tailWord_4050544).sum := by decide
  have hdescent : baseEnd_4050544 < baseStart_4050544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050561 : List Nat := [1, 2, 4, 2, 1, 3, 3, 7]
def baseStart_4050561 : Nat := 118140960795 + 4050561 * 2 ^ 59
def prefixEnd_4050561 : Nat := 4983230072969 + 3 ^ 40 * 4050561 * 2
def baseEnd_4050561 : Nat := 77032767161349329450345

theorem tailTrace_4050561 : CollatzResearch.WordTrace tailWord_4050561 prefixEnd_4050561 77032767161349329450345 := by
  unfold tailWord_4050561
  simp only [CollatzResearch.WordTrace]
  refine ⟨147736096678516752588431537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98490731119011168392287691 147736096678516752588431537)
  ·
    refine ⟨110802072508887564441323653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147736096678516752588431537 110802072508887564441323653)
    ·
      refine ⟨20775388595416418332748185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110802072508887564441323653 20775388595416418332748185)
      ·
        refine ⟨15581541446562313749561139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20775388595416418332748185 15581541446562313749561139)
        ·
          refine ⟨23372312169843470624341709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15581541446562313749561139 23372312169843470624341709)
          ·
            refine ⟨8764617063691301484128141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23372312169843470624341709 8764617063691301484128141)
            ·
              refine ⟨3286731398884238056548053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8764617063691301484128141 3286731398884238056548053)
              ·
                refine ⟨77032767161349329450345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3286731398884238056548053 77032767161349329450345)
                ·
                  rfl

theorem cell23_4050561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 7].length) (baseStart_4050561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050561 prefixEnd_4050561 := by exact prefixLift 4050561
  have htrace : WordTrace (prefixWord ++ tailWord_4050561) baseStart_4050561 baseEnd_4050561 := by
    simpa [prefixWord, tailWord_4050561, baseEnd_4050561] using wordTrace_append hprefix tailTrace_4050561
  have hstable : (prefixWord ++ tailWord_4050561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050561).length < 2 ^ (prefixWord ++ tailWord_4050561).sum := by decide
  have hdescent : baseEnd_4050561 < baseStart_4050561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050571 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 4, 1, 3]
def baseStart_4050571 : Nat := 118140960795 + 4050571 * 2 ^ 59
def prefixEnd_4050571 : Nat := 4983230072969 + 3 ^ 40 * 4050571 * 2
def baseEnd_4050571 : Nat := 2079889848162976856034269

theorem tailTrace_4050571 : CollatzResearch.WordTrace tailWord_4050571 prefixEnd_4050571 2079889848162976856034269 := by
  unfold tailWord_4050571
  simp only [CollatzResearch.WordTrace]
  refine ⟨147736461408480524296295567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98490974272320349530863711 147736461408480524296295567)
  ·
    refine ⟨221604692112720786444443351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147736461408480524296295567 221604692112720786444443351)
    ·
      refine ⟨332407038169081179666665027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221604692112720786444443351 332407038169081179666665027)
      ·
        refine ⟨498610557253621769499997541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332407038169081179666665027 498610557253621769499997541)
        ·
          refine ⟨93489479485054081781249539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 498610557253621769499997541 93489479485054081781249539)
          ·
            refine ⟨140234219227581122671874309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93489479485054081781249539 140234219227581122671874309)
            ·
              refine ⟨26293916105171460500976433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140234219227581122671874309 26293916105171460500976433)
              ·
                refine ⟨19720437078878595375732325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26293916105171460500976433 19720437078878595375732325)
                ·
                  refine ⟨3697581952289736632949811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19720437078878595375732325 3697581952289736632949811)
                  ·
                    refine ⟨5546372928434604949424717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3697581952289736632949811 5546372928434604949424717)
                    ·
                      refine ⟨2079889848162976856034269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5546372928434604949424717 2079889848162976856034269)
                      ·
                        rfl

theorem cell23_4050571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 1, 3].length) (baseStart_4050571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050571 prefixEnd_4050571 := by exact prefixLift 4050571
  have htrace : WordTrace (prefixWord ++ tailWord_4050571) baseStart_4050571 baseEnd_4050571 := by
    simpa [prefixWord, tailWord_4050571, baseEnd_4050571] using wordTrace_append hprefix tailTrace_4050571
  have hstable : (prefixWord ++ tailWord_4050571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050571).length < 2 ^ (prefixWord ++ tailWord_4050571).sum := by decide
  have hdescent : baseEnd_4050571 < baseStart_4050571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050615 : List Nat := [1, 1, 3, 1, 5, 2, 2, 2, 1, 3, 2]
def baseStart_4050615 : Nat := 118140960795 + 4050615 * 2 ^ 59
def prefixEnd_4050615 : Nat := 4983230072969 + 3 ^ 40 * 4050615 * 2
def baseEnd_4050615 : Nat := 2079912441311774683884067

theorem tailTrace_4050615 : CollatzResearch.WordTrace tailWord_4050615 prefixEnd_4050615 2079912441311774683884067 := by
  unfold tailWord_4050615
  simp only [CollatzResearch.WordTrace]
  refine ⟨147738066220321119810897299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98492044146880746540598199 147738066220321119810897299)
  ·
    refine ⟨221607099330481679716345949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147738066220321119810897299 221607099330481679716345949)
    ·
      refine ⟨83102662248930629893629731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221607099330481679716345949 83102662248930629893629731)
      ·
        refine ⟨124653993373395944840444597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83102662248930629893629731 124653993373395944840444597)
        ·
          refine ⟨11686311878755869828791681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124653993373395944840444597 11686311878755869828791681)
          ·
            refine ⟨8764733909066902371593761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11686311878755869828791681 8764733909066902371593761)
            ·
              refine ⟨6573550431800176778695321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8764733909066902371593761 6573550431800176778695321)
              ·
                refine ⟨4930162823850132584021491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6573550431800176778695321 4930162823850132584021491)
                ·
                  refine ⟨7395244235775198876032237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930162823850132584021491 7395244235775198876032237)
                  ·
                    refine ⟨2773216588415699578512089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7395244235775198876032237 2773216588415699578512089)
                    ·
                      refine ⟨2079912441311774683884067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773216588415699578512089 2079912441311774683884067)
                      ·
                        rfl

theorem cell23_4050615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 3, 2].length) (baseStart_4050615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050615 prefixEnd_4050615 := by exact prefixLift 4050615
  have htrace : WordTrace (prefixWord ++ tailWord_4050615) baseStart_4050615 baseEnd_4050615 := by
    simpa [prefixWord, tailWord_4050615, baseEnd_4050615] using wordTrace_append hprefix tailTrace_4050615
  have hstable : (prefixWord ++ tailWord_4050615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050615).length < 2 ^ (prefixWord ++ tailWord_4050615).sum := by decide
  have hdescent : baseEnd_4050615 < baseStart_4050615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050628 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_4050628 : Nat := 118140960795 + 4050628 * 2 ^ 59
def prefixEnd_4050628 : Nat := 4983230072969 + 3 ^ 40 * 4050628 * 2
def baseEnd_4050628 : Nat := 2079919116560283133021507

theorem tailTrace_4050628 : CollatzResearch.WordTrace tailWord_4050628 prefixEnd_4050628 2079919116560283133021507 := by
  unfold tailWord_4050628
  simp only [CollatzResearch.WordTrace]
  refine ⟨73869270184637011515560269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98492360246182682020747025 73869270184637011515560269)
  ·
    refine ⟨27700976319238879318335101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73869270184637011515560269 27700976319238879318335101)
    ·
      refine ⟨10387866119714579744375663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27700976319238879318335101 10387866119714579744375663)
      ·
        refine ⟨15581799179571869616563495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10387866119714579744375663 15581799179571869616563495)
        ·
          refine ⟨23372698769357804424845243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15581799179571869616563495 23372698769357804424845243)
          ·
            refine ⟨35059048154036706637267865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23372698769357804424845243 35059048154036706637267865)
            ·
              refine ⟨26294286115527529977950899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35059048154036706637267865 26294286115527529977950899)
              ·
                refine ⟨39441429173291294966926349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26294286115527529977950899 39441429173291294966926349)
                ·
                  refine ⟨14790535939984235612597381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39441429173291294966926349 14790535939984235612597381)
                  ·
                    refine ⟨2773225488747044177362009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14790535939984235612597381 2773225488747044177362009)
                    ·
                      refine ⟨2079919116560283133021507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773225488747044177362009 2079919116560283133021507)
                      ·
                        rfl

theorem cell23_4050628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_4050628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050628 prefixEnd_4050628 := by exact prefixLift 4050628
  have htrace : WordTrace (prefixWord ++ tailWord_4050628) baseStart_4050628 baseEnd_4050628 := by
    simpa [prefixWord, tailWord_4050628, baseEnd_4050628] using wordTrace_append hprefix tailTrace_4050628
  have hstable : (prefixWord ++ tailWord_4050628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050628).length < 2 ^ (prefixWord ++ tailWord_4050628).sum := by decide
  have hdescent : baseEnd_4050628 < baseStart_4050628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050661 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 1, 5, 3]
def baseStart_4050661 : Nat := 118140960795 + 4050661 * 2 ^ 59
def prefixEnd_4050661 : Nat := 4983230072969 + 3 ^ 40 * 4050661 * 2
def baseEnd_4050661 : Nat := 2079936061421881503908855

theorem tailTrace_4050661 : CollatzResearch.WordTrace tailWord_4050661 prefixEnd_4050661 2079936061421881503908855 := by
  unfold tailWord_4050661
  simp only [CollatzResearch.WordTrace]
  refine ⟨147739743978154469667071837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98493162652102979778047891 147739743978154469667071837)
  ·
    refine ⟨55402403991807926125151939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147739743978154469667071837 55402403991807926125151939)
    ·
      refine ⟨83103605987711889187727909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55402403991807926125151939 83103605987711889187727909)
      ·
        refine ⟨15581926122695979222698983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83103605987711889187727909 15581926122695979222698983)
        ·
          refine ⟨23372889184043968834048475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15581926122695979222698983 23372889184043968834048475)
          ·
            refine ⟨35059333776065953251072713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23372889184043968834048475 35059333776065953251072713)
            ·
              refine ⟨26294500332049464938304535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35059333776065953251072713 26294500332049464938304535)
              ·
                refine ⟨39441750498074197407456803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26294500332049464938304535 39441750498074197407456803)
                ·
                  refine ⟨59162625747111296111185205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39441750498074197407456803 59162625747111296111185205)
                  ·
                    refine ⟨5546496163791684010423613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59162625747111296111185205 5546496163791684010423613)
                    ·
                      refine ⟨2079936061421881503908855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5546496163791684010423613 2079936061421881503908855)
                      ·
                        rfl

theorem cell23_4050661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_4050661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050661 prefixEnd_4050661 := by exact prefixLift 4050661
  have htrace : WordTrace (prefixWord ++ tailWord_4050661) baseStart_4050661 baseEnd_4050661 := by
    simpa [prefixWord, tailWord_4050661, baseEnd_4050661] using wordTrace_append hprefix tailTrace_4050661
  have hstable : (prefixWord ++ tailWord_4050661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050661).length < 2 ^ (prefixWord ++ tailWord_4050661).sum := by decide
  have hdescent : baseEnd_4050661 < baseStart_4050661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050728 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 5, 4]
def baseStart_4050728 : Nat := 118140960795 + 4050728 * 2 ^ 59
def prefixEnd_4050728 : Nat := 4983230072969 + 3 ^ 40 * 4050728 * 2
def baseEnd_4050728 : Nat := 693323488208577580590349

theorem tailTrace_4050728 : CollatzResearch.WordTrace tailWord_4050728 prefixEnd_4050728 693323488208577580590349 := by
  unfold tailWord_4050728
  simp only [CollatzResearch.WordTrace]
  refine ⟨73871093834455870054880419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98494791779274493406507225 73871093834455870054880419)
  ·
    refine ⟨110806640751683805082320629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73871093834455870054880419 110806640751683805082320629)
    ·
      refine ⟨10388122570470356726467559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110806640751683805082320629 10388122570470356726467559)
      ·
        refine ⟨15582183855705535089701339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10388122570470356726467559 15582183855705535089701339)
        ·
          refine ⟨23373275783558302634552009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15582183855705535089701339 23373275783558302634552009)
          ·
            refine ⟨17529956837668726975914007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23373275783558302634552009 17529956837668726975914007)
            ·
              refine ⟨26294935256503090463871011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17529956837668726975914007 26294935256503090463871011)
              ·
                refine ⟨39442402884754635695806517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26294935256503090463871011 39442402884754635695806517)
                ·
                  refine ⟨3697725270445747096481861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39442402884754635695806517 3697725270445747096481861)
                  ·
                    refine ⟨693323488208577580590349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3697725270445747096481861 693323488208577580590349)
                    ·
                      rfl

theorem cell23_4050728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_4050728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050728 prefixEnd_4050728 := by exact prefixLift 4050728
  have htrace : WordTrace (prefixWord ++ tailWord_4050728) baseStart_4050728 baseEnd_4050728 := by
    simpa [prefixWord, tailWord_4050728, baseEnd_4050728] using wordTrace_append hprefix tailTrace_4050728
  have hstable : (prefixWord ++ tailWord_4050728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050728).length < 2 ^ (prefixWord ++ tailWord_4050728).sum := by decide
  have hdescent : baseEnd_4050728 < baseStart_4050728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050738 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_4050738 : Nat := 118140960795 + 4050738 * 2 ^ 59
def prefixEnd_4050738 : Nat := 4983230072969 + 3 ^ 40 * 4050738 * 2
def baseEnd_4050738 : Nat := 2079975599432277702646001

theorem tailTrace_4050738 : CollatzResearch.WordTrace tailWord_4050738 prefixEnd_4050738 2079975599432277702646001 := by
  unfold tailWord_4050738
  simp only [CollatzResearch.WordTrace]
  refine ⟨36935638099718877954406217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98495034932583674545083245 36935638099718877954406217)
  ·
    refine ⟨27701728574789158465804663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36935638099718877954406217 27701728574789158465804663)
    ·
      refine ⟨41552592862183737698706995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27701728574789158465804663 41552592862183737698706995)
      ·
        refine ⟨62328889293275606548060493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41552592862183737698706995 62328889293275606548060493)
        ·
          refine ⟨23373333484978352455522685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62328889293275606548060493 23373333484978352455522685)
          ·
            refine ⟨8765000056866882170821007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23373333484978352455522685 8765000056866882170821007)
            ·
              refine ⟨13147500085300323256231511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8765000056866882170821007 13147500085300323256231511)
              ·
                refine ⟨19721250127950484884347267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13147500085300323256231511 19721250127950484884347267)
                ·
                  refine ⟨29581875191925727326520901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19721250127950484884347267 29581875191925727326520901)
                  ·
                    refine ⟨5546601598486073873722669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29581875191925727326520901 5546601598486073873722669)
                    ·
                      refine ⟨2079975599432277702646001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5546601598486073873722669 2079975599432277702646001)
                      ·
                        rfl

theorem cell23_4050738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_4050738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050738 prefixEnd_4050738 := by exact prefixLift 4050738
  have htrace : WordTrace (prefixWord ++ tailWord_4050738) baseStart_4050738 baseEnd_4050738 := by
    simpa [prefixWord, tailWord_4050738, baseEnd_4050738] using wordTrace_append hprefix tailTrace_4050738
  have hstable : (prefixWord ++ tailWord_4050738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050738).length < 2 ^ (prefixWord ++ tailWord_4050738).sum := by decide
  have hdescent : baseEnd_4050738 < baseStart_4050738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050775 : List Nat := [1, 1, 3, 2, 5, 1, 3, 1, 6]
def baseStart_4050775 : Nat := 118140960795 + 4050775 * 2 ^ 59
def prefixEnd_4050775 : Nat := 4983230072969 + 3 ^ 40 * 4050775 * 2
def baseEnd_4050775 : Nat := 231110510912943784209259

theorem tailTrace_4050775 : CollatzResearch.WordTrace tailWord_4050775 prefixEnd_4050775 231110510912943784209259 := by
  unfold tailWord_4050775
  simp only [CollatzResearch.WordTrace]
  refine ⟨147743901899741467136721779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98495934599827644757814519 147743901899741467136721779)
  ·
    refine ⟨221615852849612200705082669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147743901899741467136721779 221615852849612200705082669)
    ·
      refine ⟨83105944818604575264406001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221615852849612200705082669 83105944818604575264406001)
      ·
        refine ⟨62329458613953431448304501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83105944818604575264406001 62329458613953431448304501)
        ·
          refine ⟨5843386745058134198278547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62329458613953431448304501 5843386745058134198278547)
          ·
            refine ⟨8765080117587201297417821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843386745058134198278547 8765080117587201297417821)
            ·
              refine ⟨3286905044095200486531683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8765080117587201297417821 3286905044095200486531683)
              ·
                refine ⟨4930357566142800729797525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286905044095200486531683 4930357566142800729797525)
                ·
                  refine ⟨231110510912943784209259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4930357566142800729797525 231110510912943784209259)
                  ·
                    rfl

theorem cell23_4050775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 6].length) (baseStart_4050775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050775 prefixEnd_4050775 := by exact prefixLift 4050775
  have htrace : WordTrace (prefixWord ++ tailWord_4050775) baseStart_4050775 baseEnd_4050775 := by
    simpa [prefixWord, tailWord_4050775, baseEnd_4050775] using wordTrace_append hprefix tailTrace_4050775
  have hstable : (prefixWord ++ tailWord_4050775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050775).length < 2 ^ (prefixWord ++ tailWord_4050775).sum := by decide
  have hdescent : baseEnd_4050775 < baseStart_4050775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050778 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2]
def baseStart_4050778 : Nat := 118140960795 + 4050778 * 2 ^ 59
def prefixEnd_4050778 : Nat := 4983230072969 + 3 ^ 40 * 4050778 * 2
def baseEnd_4050778 : Nat := 2079996138658457546145817

theorem tailTrace_4050778 : CollatzResearch.WordTrace tailWord_4050778 prefixEnd_4050778 2079996138658457546145817 := by
  unfold tailWord_4050778
  simp only [CollatzResearch.WordTrace]
  refine ⟨36936002829682649662270247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98496007545820399099387325 36936002829682649662270247)
  ·
    refine ⟨55404004244523974493405371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36936002829682649662270247 55404004244523974493405371)
    ·
      refine ⟨83106006366785961740108057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55404004244523974493405371 83106006366785961740108057)
      ·
        refine ⟨62329504775089471305081043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83106006366785961740108057 62329504775089471305081043)
        ·
          refine ⟨93494257162634206957621565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62329504775089471305081043 93494257162634206957621565)
          ·
            refine ⟨35060346435987827609108087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93494257162634206957621565 35060346435987827609108087)
            ·
              refine ⟨52590519653981741413662131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35060346435987827609108087 52590519653981741413662131)
              ·
                refine ⟨78885779480972612120493197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52590519653981741413662131 78885779480972612120493197)
                ·
                  refine ⟨29582167305364729545184949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78885779480972612120493197 29582167305364729545184949)
                  ·
                    refine ⟨2773328184877943394861089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29582167305364729545184949 2773328184877943394861089)
                    ·
                      refine ⟨2079996138658457546145817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2773328184877943394861089 2079996138658457546145817)
                      ·
                        rfl

theorem cell23_4050778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_4050778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050778 prefixEnd_4050778 := by exact prefixLift 4050778
  have htrace : WordTrace (prefixWord ++ tailWord_4050778) baseStart_4050778 baseEnd_4050778 := by
    simpa [prefixWord, tailWord_4050778, baseEnd_4050778] using wordTrace_append hprefix tailTrace_4050778
  have hstable : (prefixWord ++ tailWord_4050778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050778).length < 2 ^ (prefixWord ++ tailWord_4050778).sum := by decide
  have hdescent : baseEnd_4050778 < baseStart_4050778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050801 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 3, 6]
def baseStart_4050801 : Nat := 118140960795 + 4050801 * 2 ^ 59
def prefixEnd_4050801 : Nat := 4983230072969 + 3 ^ 40 * 4050801 * 2
def baseEnd_4050801 : Nat := 693335982904503652052737

theorem tailTrace_4050801 : CollatzResearch.WordTrace tailWord_4050801 prefixEnd_4050801 693335982904503652052737 := by
  unfold tailWord_4050801
  simp only [CollatzResearch.WordTrace]
  refine ⟨147744850197647273577168257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98496566798431515718112171 147744850197647273577168257)
  ·
    refine ⟨110808637648235455182876193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147744850197647273577168257 110808637648235455182876193)
    ·
      refine ⟨83106478236176591387157145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110808637648235455182876193 83106478236176591387157145)
      ·
        refine ⟨62329858677132443540367859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83106478236176591387157145 62329858677132443540367859)
        ·
          refine ⟨93494788015698665310551789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62329858677132443540367859 93494788015698665310551789)
          ·
            refine ⟨35060545505886999491456921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93494788015698665310551789 35060545505886999491456921)
            ·
              refine ⟨26295409129415249618592691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35060545505886999491456921 26295409129415249618592691)
              ·
                refine ⟨39443113694122874427889037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26295409129415249618592691 39443113694122874427889037)
                ·
                  refine ⟨14791167635296077910458389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39443113694122874427889037 14791167635296077910458389)
                  ·
                    refine ⟨693335982904503652052737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14791167635296077910458389 693335982904503652052737)
                    ·
                      rfl

theorem cell23_4050801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_4050801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050801 prefixEnd_4050801 := by exact prefixLift 4050801
  have htrace : WordTrace (prefixWord ++ tailWord_4050801) baseStart_4050801 baseEnd_4050801 := by
    simpa [prefixWord, tailWord_4050801, baseEnd_4050801] using wordTrace_append hprefix tailTrace_4050801
  have hstable : (prefixWord ++ tailWord_4050801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050801).length < 2 ^ (prefixWord ++ tailWord_4050801).sum := by decide
  have hdescent : baseEnd_4050801 < baseStart_4050801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050819 : List Nat := [1, 1, 1, 3, 4, 3, 3, 2, 1, 1, 3]
def baseStart_4050819 : Nat := 118140960795 + 4050819 * 2 ^ 59
def prefixEnd_4050819 : Nat := 4983230072969 + 3 ^ 40 * 4050819 * 2
def baseEnd_4050819 : Nat := 2080017191365291885733129

theorem tailTrace_4050819 : CollatzResearch.WordTrace tailWord_4050819 prefixEnd_4050819 2080017191365291885733129 := by
  unfold tailWord_4050819
  simp only [CollatzResearch.WordTrace]
  refine ⟨147745506711582062651323511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98497004474388041767549007 147745506711582062651323511)
  ·
    refine ⟨221618260067373093976985267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147745506711582062651323511 221618260067373093976985267)
    ·
      refine ⟨332427390101059640965477901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221618260067373093976985267 332427390101059640965477901)
      ·
        refine ⟨124660271287897365362054213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332427390101059640965477901 124660271287897365362054213)
        ·
          refine ⟨23373800866480756005385165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124660271287897365362054213 23373800866480756005385165)
          ·
            refine ⟨8765175324930283502019437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23373800866480756005385165 8765175324930283502019437)
            ·
              refine ⟨3286940746848856313257289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8765175324930283502019437 3286940746848856313257289)
              ·
                refine ⟨2465205560136642234942967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3286940746848856313257289 2465205560136642234942967)
                ·
                  refine ⟨3697808340204963352414451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465205560136642234942967 3697808340204963352414451)
                  ·
                    refine ⟨5546712510307445028621677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3697808340204963352414451 5546712510307445028621677)
                    ·
                      refine ⟨2080017191365291885733129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5546712510307445028621677 2080017191365291885733129)
                      ·
                        rfl

theorem cell23_4050819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 1, 1, 3].length) (baseStart_4050819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050819 prefixEnd_4050819 := by exact prefixLift 4050819
  have htrace : WordTrace (prefixWord ++ tailWord_4050819) baseStart_4050819 baseEnd_4050819 := by
    simpa [prefixWord, tailWord_4050819, baseEnd_4050819] using wordTrace_append hprefix tailTrace_4050819
  have hstable : (prefixWord ++ tailWord_4050819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050819).length < 2 ^ (prefixWord ++ tailWord_4050819).sum := by decide
  have hdescent : baseEnd_4050819 < baseStart_4050819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050821 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_4050821 : Nat := 118140960795 + 4050821 * 2 ^ 59
def prefixEnd_4050821 : Nat := 4983230072969 + 3 ^ 40 * 4050821 * 2
def baseEnd_4050821 : Nat := 2080018218326600877908119

theorem tailTrace_4050821 : CollatzResearch.WordTrace tailWord_4050821 prefixEnd_4050821 2080018218326600877908119 := by
  unfold tailWord_4050821
  simp only [CollatzResearch.WordTrace]
  refine ⟨147745579657574816992896317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98497053105049877995264211 147745579657574816992896317)
  ·
    refine ⟨55404592371590556372336119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147745579657574816992896317 55404592371590556372336119)
    ·
      refine ⟨83106888557385834558504179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55404592371590556372336119 83106888557385834558504179)
      ·
        refine ⟨124660332836078751837756269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83106888557385834558504179 124660332836078751837756269)
        ·
          refine ⟨46747624813529531939158601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124660332836078751837756269 46747624813529531939158601)
          ·
            refine ⟨35060718610147148954368951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46747624813529531939158601 35060718610147148954368951)
            ·
              refine ⟨52591077915220723431553427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35060718610147148954368951 52591077915220723431553427)
              ·
                refine ⟨78886616872831085147330141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52591077915220723431553427 78886616872831085147330141)
                ·
                  refine ⟨29582481327311656930248803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78886616872831085147330141 29582481327311656930248803)
                  ·
                    refine ⟨44373721990967485395373205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29582481327311656930248803 44373721990967485395373205)
                    ·
                      refine ⟨2080018218326600877908119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44373721990967485395373205 2080018218326600877908119)
                      ·
                        rfl

theorem cell23_4050821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_4050821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050821 prefixEnd_4050821 := by exact prefixLift 4050821
  have htrace : WordTrace (prefixWord ++ tailWord_4050821) baseStart_4050821 baseEnd_4050821 := by
    simpa [prefixWord, tailWord_4050821, baseEnd_4050821] using wordTrace_append hprefix tailTrace_4050821
  have hstable : (prefixWord ++ tailWord_4050821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050821).length < 2 ^ (prefixWord ++ tailWord_4050821).sum := by decide
  have hdescent : baseEnd_4050821 < baseStart_4050821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050828 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 3, 2, 3]
def baseStart_4050828 : Nat := 118140960795 + 4050828 * 2 ^ 59
def prefixEnd_4050828 : Nat := 4983230072969 + 3 ^ 40 * 4050828 * 2
def baseEnd_4050828 : Nat := 2080021812691182350520587

theorem tailTrace_4050828 : CollatzResearch.WordTrace tailWord_4050828 prefixEnd_4050828 2080021812691182350520587 := by
  unfold tailWord_4050828
  simp only [CollatzResearch.WordTrace]
  refine ⟨73872917484274728594200569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98497223312366304792267425 73872917484274728594200569)
  ·
    refine ⟨55404688113206046445650427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73872917484274728594200569 55404688113206046445650427)
    ·
      refine ⟨83107032169809069668475641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55404688113206046445650427 83107032169809069668475641)
      ·
        refine ⟨62330274127356802251356731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83107032169809069668475641 62330274127356802251356731)
        ·
          refine ⟨93495411191035203377035097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62330274127356802251356731 93495411191035203377035097)
          ·
            refine ⟨70121558393276402532776323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93495411191035203377035097 70121558393276402532776323)
            ·
              refine ⟨105182337589914603799164485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70121558393276402532776323 105182337589914603799164485)
              ·
                refine ⟨19721688298108988212343341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105182337589914603799164485 19721688298108988212343341)
                ·
                  refine ⟨7395633111790870579628753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19721688298108988212343341 7395633111790870579628753)
                  ·
                    refine ⟨5546724833843152934721565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7395633111790870579628753 5546724833843152934721565)
                    ·
                      refine ⟨2080021812691182350520587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5546724833843152934721565 2080021812691182350520587)
                      ·
                        rfl

theorem cell23_4050828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_4050828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050828 prefixEnd_4050828 := by exact prefixLift 4050828
  have htrace : WordTrace (prefixWord ++ tailWord_4050828) baseStart_4050828 baseEnd_4050828 := by
    simpa [prefixWord, tailWord_4050828, baseEnd_4050828] using wordTrace_append hprefix tailTrace_4050828
  have hstable : (prefixWord ++ tailWord_4050828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050828).length < 2 ^ (prefixWord ++ tailWord_4050828).sum := by decide
  have hdescent : baseEnd_4050828 < baseStart_4050828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050842 : List Nat := [3, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4]
def baseStart_4050842 : Nat := 118140960795 + 4050842 * 2 ^ 59
def prefixEnd_4050842 : Nat := 4983230072969 + 3 ^ 40 * 4050842 * 2
def baseEnd_4050842 : Nat := 2080029001420345295745523

theorem tailTrace_4050842 : CollatzResearch.WordTrace tailWord_4050842 prefixEnd_4050842 2080029001420345295745523 := by
  unfold tailWord_4050842
  simp only [CollatzResearch.WordTrace]
  refine ⟨36936586397624684394852695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98497563726999158386273853 36936586397624684394852695)
  ·
    refine ⟨55404879596437026592279043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36936586397624684394852695 55404879596437026592279043)
    ·
      refine ⟨83107319394655539888418565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55404879596437026592279043 83107319394655539888418565)
      ·
        refine ⟨15582622386497913729078481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83107319394655539888418565 15582622386497913729078481)
        ·
          refine ⟨11686966789873435296808861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15582622386497913729078481 11686966789873435296808861)
          ·
            refine ⟨4382612546202538236303323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11686966789873435296808861 4382612546202538236303323)
            ·
              refine ⟨6573918819303807354454985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382612546202538236303323 6573918819303807354454985)
              ·
                refine ⟨4930439114477855515841239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6573918819303807354454985 4930439114477855515841239)
                ·
                  refine ⟨7395658671716783273761859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930439114477855515841239 7395658671716783273761859)
                  ·
                    refine ⟨11093488007575174910642789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7395658671716783273761859 11093488007575174910642789)
                    ·
                      refine ⟨2080029001420345295745523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11093488007575174910642789 2080029001420345295745523)
                      ·
                        rfl

theorem cell23_4050842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_4050842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4050842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4050842 prefixEnd_4050842 := by exact prefixLift 4050842
  have htrace : WordTrace (prefixWord ++ tailWord_4050842) baseStart_4050842 baseEnd_4050842 := by
    simpa [prefixWord, tailWord_4050842, baseEnd_4050842] using wordTrace_append hprefix tailTrace_4050842
  have hstable : (prefixWord ++ tailWord_4050842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050842).length < 2 ^ (prefixWord ++ tailWord_4050842).sum := by decide
  have hdescent : baseEnd_4050842 < baseStart_4050842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
