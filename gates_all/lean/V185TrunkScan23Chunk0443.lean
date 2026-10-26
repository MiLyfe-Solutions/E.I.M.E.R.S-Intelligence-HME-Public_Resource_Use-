import V185TrunkScan23Chunk0442

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2618675 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 1, 4, 2]
def baseStart_2618675 : Nat := 118140960795 + 2618675 * 2 ^ 59
def prefixEnd_2618675 : Nat := 4983230072969 + 3 ^ 40 * 2618675 * 2
def baseEnd_2618675 : Nat := 1344638952912647155719439

theorem tailTrace_2618675 : CollatzResearch.WordTrace tailWord_2618675 prefixEnd_2618675 1344638952912647155719439 := by
  unfold tailWord_2618675
  simp only [CollatzResearch.WordTrace]
  refine ⟨95510923787995183928985479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63673949191996789285990319 95510923787995183928985479)
  ·
    refine ⟨143266385681992775893478219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95510923787995183928985479 143266385681992775893478219)
    ·
      refine ⟨214899578522989163840217329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143266385681992775893478219 214899578522989163840217329)
      ·
        refine ⟨161174683892241872880162997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214899578522989163840217329 161174683892241872880162997)
        ·
          refine ⟨15110126614897675582515281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161174683892241872880162997 15110126614897675582515281)
          ·
            refine ⟨11332594961173256686886461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15110126614897675582515281 11332594961173256686886461)
            ·
              refine ⟨4249723110439971257582423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11332594961173256686886461 4249723110439971257582423)
              ·
                refine ⟨6374584665659956886373635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4249723110439971257582423 6374584665659956886373635)
                ·
                  refine ⟨9561876998489935329560453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6374584665659956886373635 9561876998489935329560453)
                  ·
                    refine ⟨1792851937216862874292585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9561876998489935329560453 1792851937216862874292585)
                    ·
                      refine ⟨1344638952912647155719439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1792851937216862874292585 1344638952912647155719439)
                      ·
                        rfl

theorem cell23_2618675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 4, 2].length) (baseStart_2618675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618675 prefixEnd_2618675 := by exact prefixLift 2618675
  have htrace : WordTrace (prefixWord ++ tailWord_2618675) baseStart_2618675 baseEnd_2618675 := by
    simpa [prefixWord, tailWord_2618675, baseEnd_2618675] using wordTrace_append hprefix tailTrace_2618675
  have hstable : (prefixWord ++ tailWord_2618675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618675).length < 2 ^ (prefixWord ++ tailWord_2618675).sum := by decide
  have hdescent : baseEnd_2618675 < baseStart_2618675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618751 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 5]
def baseStart_2618751 : Nat := 118140960795 + 2618751 * 2 ^ 59
def prefixEnd_2618751 : Nat := 4983230072969 + 3 ^ 40 * 2618751 * 2
def baseEnd_2618751 : Nat := 1344677977442388858369089

theorem tailTrace_2618751 : CollatzResearch.WordTrace tailWord_2618751 prefixEnd_2618751 1344677977442388858369089 := by
  unfold tailWord_2618751
  simp only [CollatzResearch.WordTrace]
  refine ⟨95513695735719848908752107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63675797157146565939168071 95513695735719848908752107)
  ·
    refine ⟨143270543603579773363128161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95513695735719848908752107 143270543603579773363128161)
    ·
      refine ⟨107452907702684830022346121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143270543603579773363128161 107452907702684830022346121)
      ·
        refine ⟨80589680777013622516759591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107452907702684830022346121 80589680777013622516759591)
        ·
          refine ⟨120884521165520433775139387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80589680777013622516759591 120884521165520433775139387)
          ·
            refine ⟨181326781748280650662709081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120884521165520433775139387 181326781748280650662709081)
            ·
              refine ⟨135995086311210487997031811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181326781748280650662709081 135995086311210487997031811)
              ·
                refine ⟨203992629466815731995547717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135995086311210487997031811 203992629466815731995547717)
                ·
                  refine ⟨38248618025027949749165197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203992629466815731995547717 38248618025027949749165197)
                  ·
                    refine ⟨14343231759385481155936949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38248618025027949749165197 14343231759385481155936949)
                    ·
                      refine ⟨1344677977442388858369089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14343231759385481155936949 1344677977442388858369089)
                      ·
                        rfl

theorem cell23_2618751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_2618751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618751 prefixEnd_2618751 := by exact prefixLift 2618751
  have htrace : WordTrace (prefixWord ++ tailWord_2618751) baseStart_2618751 baseEnd_2618751 := by
    simpa [prefixWord, tailWord_2618751, baseEnd_2618751] using wordTrace_append hprefix tailTrace_2618751
  have hstable : (prefixWord ++ tailWord_2618751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618751).length < 2 ^ (prefixWord ++ tailWord_2618751).sum := by decide
  have hdescent : baseEnd_2618751 < baseStart_2618751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618766 : List Nat := [4, 1, 1, 4, 3, 1, 2, 2, 5]
def baseStart_2618766 : Nat := 118140960795 + 2618766 * 2 ^ 59
def prefixEnd_2618766 : Nat := 4983230072969 + 3 ^ 40 * 2618766 * 2
def baseEnd_2618766 : Nat := 149409519961356255520169

theorem tailTrace_2618766 : CollatzResearch.WordTrace tailWord_2618766 prefixEnd_2618766 149409519961356255520169 := by
  unfold tailWord_2618766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11939280353833188308818519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63676161887110337647032101 11939280353833188308818519)
  ·
    refine ⟨17908920530749782463227779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11939280353833188308818519 17908920530749782463227779)
    ·
      refine ⟨26863380796124673694841669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17908920530749782463227779 26863380796124673694841669)
      ·
        refine ⟨5036883899273376317782813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26863380796124673694841669 5036883899273376317782813)
        ·
          refine ⟨1888831462227516119168555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5036883899273376317782813 1888831462227516119168555)
          ·
            refine ⟨2833247193341274178752833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888831462227516119168555 2833247193341274178752833)
            ·
              refine ⟨2124935395005955634064625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2833247193341274178752833 2124935395005955634064625)
              ·
                refine ⟨1593701546254466725548469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2124935395005955634064625 1593701546254466725548469)
                ·
                  refine ⟨149409519961356255520169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1593701546254466725548469 149409519961356255520169)
                  ·
                    rfl

theorem cell23_2618766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_2618766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618766 prefixEnd_2618766 := by exact prefixLift 2618766
  have htrace : WordTrace (prefixWord ++ tailWord_2618766) baseStart_2618766 baseEnd_2618766 := by
    simpa [prefixWord, tailWord_2618766, baseEnd_2618766] using wordTrace_append hprefix tailTrace_2618766
  have hstable : (prefixWord ++ tailWord_2618766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618766).length < 2 ^ (prefixWord ++ tailWord_2618766).sum := by decide
  have hdescent : baseEnd_2618766 < baseStart_2618766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618809 : List Nat := [1, 2, 1, 4, 4, 1, 2, 3, 1, 4]
def baseStart_2618809 : Nat := 118140960795 + 2618809 * 2 ^ 59
def prefixEnd_2618809 : Nat := 4983230072969 + 3 ^ 40 * 2618809 * 2
def baseEnd_2618809 : Nat := 448235919773449877147941

theorem tailTrace_2618809 : CollatzResearch.WordTrace tailWord_2618809 prefixEnd_2618809 448235919773449877147941 := by
  unfold tailWord_2618809
  simp only [CollatzResearch.WordTrace]
  refine ⟨95515811169509724814363481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63677207446339816542908987 95515811169509724814363481)
  ·
    refine ⟨71636858377132293610772611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95515811169509724814363481 71636858377132293610772611)
    ·
      refine ⟨107455287565698440416158917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71636858377132293610772611 107455287565698440416158917)
      ·
        refine ⟨20147866418568457578029797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107455287565698440416158917 20147866418568457578029797)
        ·
          refine ⟨3777724953481585795880587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20147866418568457578029797 3777724953481585795880587)
          ·
            refine ⟨5666587430222378693820881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3777724953481585795880587 5666587430222378693820881)
            ·
              refine ⟨4249940572666784020365661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5666587430222378693820881 4249940572666784020365661)
              ·
                refine ⟨1593727714750044007637123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4249940572666784020365661 1593727714750044007637123)
                ·
                  refine ⟨2390591572125066011455685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593727714750044007637123 2390591572125066011455685)
                  ·
                    refine ⟨448235919773449877147941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2390591572125066011455685 448235919773449877147941)
                    ·
                      rfl

theorem cell23_2618809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 1, 4].length) (baseStart_2618809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618809 prefixEnd_2618809 := by exact prefixLift 2618809
  have htrace : WordTrace (prefixWord ++ tailWord_2618809) baseStart_2618809 baseEnd_2618809 := by
    simpa [prefixWord, tailWord_2618809, baseEnd_2618809] using wordTrace_append hprefix tailTrace_2618809
  have hstable : (prefixWord ++ tailWord_2618809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618809).length < 2 ^ (prefixWord ++ tailWord_2618809).sum := by decide
  have hdescent : baseEnd_2618809 < baseStart_2618809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618825 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 4, 3, 2]
def baseStart_2618825 : Nat := 118140960795 + 2618825 * 2 ^ 59
def prefixEnd_2618825 : Nat := 4983230072969 + 3 ^ 40 * 2618825 * 2
def baseEnd_2618825 : Nat := 1344715975010821568843749

theorem tailTrace_2618825 : CollatzResearch.WordTrace tailWord_2618825 prefixEnd_2618825 1344715975010821568843749 := by
  unfold tailWord_2618825
  simp only [CollatzResearch.WordTrace]
  refine ⟨95516394737451759546945929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63677596491634506364630619 95516394737451759546945929)
  ·
    refine ⟨71637296053088819660209447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95516394737451759546945929 71637296053088819660209447)
    ·
      refine ⟨107455944079633229490314171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71637296053088819660209447 107455944079633229490314171)
      ·
        refine ⟨161183916119449844235471257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107455944079633229490314171 161183916119449844235471257)
        ·
          refine ⟨120887937089587383176603443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161183916119449844235471257 120887937089587383176603443)
          ·
            refine ⟨181331905634381074764905165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120887937089587383176603443 181331905634381074764905165)
            ·
              refine ⟨67999464612892903036839437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181331905634381074764905165 67999464612892903036839437)
              ·
                refine ⟨25499799229834838638814789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67999464612892903036839437 25499799229834838638814789)
                ·
                  refine ⟨4781212355594032244777773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25499799229834838638814789 4781212355594032244777773)
                  ·
                    refine ⟨1792954633347762091791665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4781212355594032244777773 1792954633347762091791665)
                    ·
                      refine ⟨1344715975010821568843749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1792954633347762091791665 1344715975010821568843749)
                      ·
                        rfl

theorem cell23_2618825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 3, 2].length) (baseStart_2618825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618825 prefixEnd_2618825 := by exact prefixLift 2618825
  have htrace : WordTrace (prefixWord ++ tailWord_2618825) baseStart_2618825 baseEnd_2618825 := by
    simpa [prefixWord, tailWord_2618825, baseEnd_2618825] using wordTrace_append hprefix tailTrace_2618825
  have hstable : (prefixWord ++ tailWord_2618825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618825).length < 2 ^ (prefixWord ++ tailWord_2618825).sum := by decide
  have hdescent : baseEnd_2618825 < baseStart_2618825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618848 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 1, 6]
def baseStart_2618848 : Nat := 118140960795 + 2618848 * 2 ^ 59
def prefixEnd_2618848 : Nat := 4983230072969 + 3 ^ 40 * 2618848 * 2
def baseEnd_2618848 : Nat := 448242595021958326285381

theorem tailTrace_2618848 : CollatzResearch.WordTrace tailWord_2618848 prefixEnd_2618848 448242595021958326285381 := by
  unfold tailWord_2618848
  simp only [CollatzResearch.WordTrace]
  refine ⟨47758616808184217237516599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63678155744245622983355465 47758616808184217237516599)
  ·
    refine ⟨71637925212276325856274899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47758616808184217237516599 71637925212276325856274899)
    ·
      refine ⟨107456887818414488784412349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71637925212276325856274899 107456887818414488784412349)
      ·
        refine ⟨40296332931905433294154631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107456887818414488784412349 40296332931905433294154631)
        ·
          refine ⟨60444499397858149941231947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40296332931905433294154631 60444499397858149941231947)
          ·
            refine ⟨90666749096787224911847921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60444499397858149941231947 90666749096787224911847921)
            ·
              refine ⟨68000061822590418683885941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90666749096787224911847921 68000061822590418683885941)
              ·
                refine ⟨6375005795867851751614307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68000061822590418683885941 6375005795867851751614307)
                ·
                  refine ⟨9562508693801777627421461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6375005795867851751614307 9562508693801777627421461)
                  ·
                    refine ⟨448242595021958326285381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9562508693801777627421461 448242595021958326285381)
                    ·
                      rfl

theorem cell23_2618848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 6].length) (baseStart_2618848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618848 prefixEnd_2618848 := by exact prefixLift 2618848
  have htrace : WordTrace (prefixWord ++ tailWord_2618848) baseStart_2618848 baseEnd_2618848 := by
    simpa [prefixWord, tailWord_2618848, baseEnd_2618848] using wordTrace_append hprefix tailTrace_2618848
  have hstable : (prefixWord ++ tailWord_2618848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618848).length < 2 ^ (prefixWord ++ tailWord_2618848).sum := by decide
  have hdescent : baseEnd_2618848 < baseStart_2618848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618865 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 4, 4]
def baseStart_2618865 : Nat := 118140960795 + 2618865 * 2 ^ 59
def prefixEnd_2618865 : Nat := 4983230072969 + 3 ^ 40 * 2618865 * 2
def baseEnd_2618865 : Nat := 448245504745667137447855

theorem tailTrace_2618865 : CollatzResearch.WordTrace tailWord_2618865 prefixEnd_2618865 448245504745667137447855 := by
  unfold tailWord_2618865
  simp only [CollatzResearch.WordTrace]
  refine ⟨95517853657306846378402049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63678569104871230918934699 95517853657306846378402049)
  ·
    refine ⟨71638390242980134783801537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95517853657306846378402049 71638390242980134783801537)
    ·
      refine ⟨53728792682235101087851153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71638390242980134783801537 53728792682235101087851153)
      ·
        refine ⟨40296594511676325815888365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53728792682235101087851153 40296594511676325815888365)
        ·
          refine ⟨15111222941878622180958137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40296594511676325815888365 15111222941878622180958137)
          ·
            refine ⟨11333417206408966635718603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15111222941878622180958137 11333417206408966635718603)
            ·
              refine ⟨17000125809613449953577905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11333417206408966635718603 17000125809613449953577905)
              ·
                refine ⟨12750094357210087465183429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17000125809613449953577905 12750094357210087465183429)
                ·
                  refine ⟨2390642691976891399721893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12750094357210087465183429 2390642691976891399721893)
                  ·
                    refine ⟨448245504745667137447855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2390642691976891399721893 448245504745667137447855)
                    ·
                      rfl

theorem cell23_2618865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_2618865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618865 prefixEnd_2618865 := by exact prefixLift 2618865
  have htrace : WordTrace (prefixWord ++ tailWord_2618865) baseStart_2618865 baseEnd_2618865 := by
    simpa [prefixWord, tailWord_2618865, baseEnd_2618865] using wordTrace_append hprefix tailTrace_2618865
  have hstable : (prefixWord ++ tailWord_2618865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618865).length < 2 ^ (prefixWord ++ tailWord_2618865).sum := by decide
  have hdescent : baseEnd_2618865 < baseStart_2618865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618866 : List Nat := [3, 2, 1, 4, 1, 1, 3, 3, 1, 1, 3]
def baseStart_2618866 : Nat := 118140960795 + 2618866 * 2 ^ 59
def prefixEnd_2618866 : Nat := 4983230072969 + 3 ^ 40 * 2618866 * 2
def baseEnd_2618866 : Nat := 1344737027717655908431061

theorem tailTrace_2618866 : CollatzResearch.WordTrace tailWord_2618866 prefixEnd_2618866 1344737027717655908431061 := by
  unfold tailWord_2618866
  simp only [CollatzResearch.WordTrace]
  refine ⟨23879472532575805887297113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63678593420202149032792301 23879472532575805887297113)
  ·
    refine ⟨17909604399431854415472835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23879472532575805887297113 17909604399431854415472835)
    ·
      refine ⟨26864406599147781623209253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17909604399431854415472835 26864406599147781623209253)
      ·
        refine ⟨5037076237340209054351735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26864406599147781623209253 5037076237340209054351735)
        ·
          refine ⟨7555614356010313581527603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5037076237340209054351735 7555614356010313581527603)
          ·
            refine ⟨11333421534015470372291405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7555614356010313581527603 11333421534015470372291405)
            ·
              refine ⟨4250033075255801389609277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11333421534015470372291405 4250033075255801389609277)
              ·
                refine ⟨1593762403220925521103479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4250033075255801389609277 1593762403220925521103479)
                ·
                  refine ⟨2390643604831388281655219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593762403220925521103479 2390643604831388281655219)
                  ·
                    refine ⟨3585965407247082422482829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2390643604831388281655219 3585965407247082422482829)
                    ·
                      refine ⟨1344737027717655908431061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3585965407247082422482829 1344737027717655908431061)
                      ·
                        rfl

theorem cell23_2618866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_2618866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618866 prefixEnd_2618866 := by exact prefixLift 2618866
  have htrace : WordTrace (prefixWord ++ tailWord_2618866) baseStart_2618866 baseEnd_2618866 := by
    simpa [prefixWord, tailWord_2618866, baseEnd_2618866] using wordTrace_append hprefix tailTrace_2618866
  have hstable : (prefixWord ++ tailWord_2618866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618866).length < 2 ^ (prefixWord ++ tailWord_2618866).sum := by decide
  have hdescent : baseEnd_2618866 < baseStart_2618866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618899 : List Nat := [1, 1, 1, 2, 1, 8, 2, 1, 2, 4]
def baseStart_2618899 : Nat := 118140960795 + 2618899 * 2 ^ 59
def prefixEnd_2618899 : Nat := 4983230072969 + 3 ^ 40 * 2618899 * 2
def baseEnd_2618899 : Nat := 448251324193084759772803

theorem tailTrace_2618899 : CollatzResearch.WordTrace tailWord_2618899 prefixEnd_2618899 448251324193084759772803 := by
  unfold tailWord_2618899
  simp only [CollatzResearch.WordTrace]
  refine ⟨95519093739183670185139751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63679395826122446790093167 95519093739183670185139751)
  ·
    refine ⟨143278640608775505277709627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95519093739183670185139751 143278640608775505277709627)
    ·
      refine ⟨214917960913163257916564441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143278640608775505277709627 214917960913163257916564441)
      ·
        refine ⟨161188470684872443437423331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214917960913163257916564441 161188470684872443437423331)
        ·
          refine ⟨241782706027308665156134997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161188470684872443437423331 241782706027308665156134997)
          ·
            refine ⟨2833391086257523419798457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 241782706027308665156134997 2833391086257523419798457)
            ·
              refine ⟨2125043314693142564848843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2833391086257523419798457 2125043314693142564848843)
              ·
                refine ⟨3187564972039713847273265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125043314693142564848843 3187564972039713847273265)
                ·
                  refine ⟨2390673729029785385454949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3187564972039713847273265 2390673729029785385454949)
                  ·
                    refine ⟨448251324193084759772803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2390673729029785385454949 448251324193084759772803)
                    ·
                      rfl

theorem cell23_2618899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 2, 4].length) (baseStart_2618899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618899 prefixEnd_2618899 := by exact prefixLift 2618899
  have htrace : WordTrace (prefixWord ++ tailWord_2618899) baseStart_2618899 baseEnd_2618899 := by
    simpa [prefixWord, tailWord_2618899, baseEnd_2618899] using wordTrace_append hprefix tailTrace_2618899
  have hstable : (prefixWord ++ tailWord_2618899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618899).length < 2 ^ (prefixWord ++ tailWord_2618899).sum := by decide
  have hdescent : baseEnd_2618899 < baseStart_2618899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618910 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_2618910 : Nat := 118140960795 + 2618910 * 2 ^ 59
def prefixEnd_2618910 : Nat := 4983230072969 + 3 ^ 40 * 2618910 * 2
def baseEnd_2618910 : Nat := 1344759620866453736280859

theorem tailTrace_2618910 : CollatzResearch.WordTrace tailWord_2618910 prefixEnd_2618910 1344759620866453736280859 := by
  unfold tailWord_2618910
  simp only [CollatzResearch.WordTrace]
  refine ⟨11939936867767977382973773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63679663294762546042526789 11939936867767977382973773)
  ·
    refine ⟨4477476325412991518615165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11939936867767977382973773 4477476325412991518615165)
    ·
      refine ⟨1679053622029871819480687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4477476325412991518615165 1679053622029871819480687)
      ·
        refine ⟨2518580433044807729221031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1679053622029871819480687 2518580433044807729221031)
        ·
          refine ⟨3777870649567211593831547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2518580433044807729221031 3777870649567211593831547)
          ·
            refine ⟨5666805974350817390747321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3777870649567211593831547 5666805974350817390747321)
            ·
              refine ⟨4250104480763113043060491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5666805974350817390747321 4250104480763113043060491)
              ·
                refine ⟨6375156721144669564590737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4250104480763113043060491 6375156721144669564590737)
                ·
                  refine ⟨4781367540858502173443053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6375156721144669564590737 4781367540858502173443053)
                  ·
                    refine ⟨1793012827821938315041145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4781367540858502173443053 1793012827821938315041145)
                    ·
                      refine ⟨1344759620866453736280859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1793012827821938315041145 1344759620866453736280859)
                      ·
                        rfl

theorem cell23_2618910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_2618910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618910 prefixEnd_2618910 := by exact prefixLift 2618910
  have htrace : WordTrace (prefixWord ++ tailWord_2618910) baseStart_2618910 baseEnd_2618910 := by
    simpa [prefixWord, tailWord_2618910, baseEnd_2618910] using wordTrace_append hprefix tailTrace_2618910
  have hstable : (prefixWord ++ tailWord_2618910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618910).length < 2 ^ (prefixWord ++ tailWord_2618910).sum := by decide
  have hdescent : baseEnd_2618910 < baseStart_2618910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618922 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_2618922 : Nat := 118140960795 + 2618922 * 2 ^ 59
def prefixEnd_2618922 : Nat := 4983230072969 + 3 ^ 40 * 2618922 * 2
def baseEnd_2618922 : Nat := 1344765782634307689330803

theorem tailTrace_2618922 : CollatzResearch.WordTrace tailWord_2618922 prefixEnd_2618922 1344765782634307689330803 := by
  unfold tailWord_2618922
  simp only [CollatzResearch.WordTrace]
  refine ⟨23879983154525086278306755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63679955078733563408818013 23879983154525086278306755)
  ·
    refine ⟨35819974731787629417460133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23879983154525086278306755 35819974731787629417460133)
    ·
      refine ⟨6716245262210180515773775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35819974731787629417460133 6716245262210180515773775)
      ·
        refine ⟨10074367893315270773660663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6716245262210180515773775 10074367893315270773660663)
        ·
          refine ⟨15111551839972906160490995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10074367893315270773660663 15111551839972906160490995)
          ·
            refine ⟨22667327759959359240736493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15111551839972906160490995 22667327759959359240736493)
            ·
              refine ⟨8500247909984759715276185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22667327759959359240736493 8500247909984759715276185)
              ·
                refine ⟨6375185932488569786457139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8500247909984759715276185 6375185932488569786457139)
                ·
                  refine ⟨9562778898732854679685709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6375185932488569786457139 9562778898732854679685709)
                  ·
                    refine ⟨3586042087024820504882141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9562778898732854679685709 3586042087024820504882141)
                    ·
                      refine ⟨1344765782634307689330803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3586042087024820504882141 1344765782634307689330803)
                      ·
                        rfl

theorem cell23_2618922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_2618922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618922 prefixEnd_2618922 := by exact prefixLift 2618922
  have htrace : WordTrace (prefixWord ++ tailWord_2618922) baseStart_2618922 baseEnd_2618922 := by
    simpa [prefixWord, tailWord_2618922, baseEnd_2618922] using wordTrace_append hprefix tailTrace_2618922
  have hstable : (prefixWord ++ tailWord_2618922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618922).length < 2 ^ (prefixWord ++ tailWord_2618922).sum := by decide
  have hdescent : baseEnd_2618922 < baseStart_2618922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618926 : List Nat := [4, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_2618926 : Nat := 118140960795 + 2618926 * 2 ^ 59
def prefixEnd_2618926 : Nat := 4983230072969 + 3 ^ 40 * 2618926 * 2
def baseEnd_2618926 : Nat := 1344767836556925673680785

theorem tailTrace_2618926 : CollatzResearch.WordTrace tailWord_2618926 prefixEnd_2618926 1344767836556925673680785 := by
  unfold tailWord_2618926
  simp only [CollatzResearch.WordTrace]
  refine ⟨11940009813760731724546579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63680052340057235864248421 11940009813760731724546579)
  ·
    refine ⟨17910014720641097586819869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11940009813760731724546579 17910014720641097586819869)
    ·
      refine ⟨6716255520240411595057451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17910014720641097586819869 6716255520240411595057451)
      ·
        refine ⟨10074383280360617392586177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6716255520240411595057451 10074383280360617392586177)
        ·
          refine ⟨7555787460270463044439633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10074383280360617392586177 7555787460270463044439633)
          ·
            refine ⟨5666840595202847283329725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7555787460270463044439633 5666840595202847283329725)
            ·
              refine ⟨2125065223201067731248647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5666840595202847283329725 2125065223201067731248647)
              ·
                refine ⟨3187597834801601596872971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125065223201067731248647 3187597834801601596872971)
                ·
                  refine ⟨4781396752202402395309457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3187597834801601596872971 4781396752202402395309457)
                  ·
                    refine ⟨3586047564151801796482093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4781396752202402395309457 3586047564151801796482093)
                    ·
                      refine ⟨1344767836556925673680785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3586047564151801796482093 1344767836556925673680785)
                      ·
                        rfl

theorem cell23_2618926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_2618926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618926 prefixEnd_2618926 := by exact prefixLift 2618926
  have htrace : WordTrace (prefixWord ++ tailWord_2618926) baseStart_2618926 baseEnd_2618926 := by
    simpa [prefixWord, tailWord_2618926, baseEnd_2618926] using wordTrace_append hprefix tailTrace_2618926
  have hstable : (prefixWord ++ tailWord_2618926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618926).length < 2 ^ (prefixWord ++ tailWord_2618926).sum := by decide
  have hdescent : baseEnd_2618926 < baseStart_2618926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618940 : List Nat := [2, 2, 2, 2, 4, 2, 2, 2, 1, 2, 2]
def baseStart_2618940 : Nat := 118140960795 + 2618940 * 2 ^ 59
def prefixEnd_2618940 : Nat := 4983230072969 + 3 ^ 40 * 2618940 * 2
def baseEnd_2618940 : Nat := 1344775025286088618905721

theorem tailTrace_2618940 : CollatzResearch.WordTrace tailWord_2618940 prefixEnd_2618940 1344775025286088618905721 := by
  unfold tailWord_2618940
  simp only [CollatzResearch.WordTrace]
  refine ⟨47760294566017567093691137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63680392754690089458254849 47760294566017567093691137)
  ·
    refine ⟨35820220924513175320268353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47760294566017567093691137 35820220924513175320268353)
    ·
      refine ⟨26865165693384881490201265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35820220924513175320268353 26865165693384881490201265)
      ·
        refine ⟨20148874270038661117650949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26865165693384881490201265 20148874270038661117650949)
        ·
          refine ⟨3777913925632248959559553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20148874270038661117650949 3777913925632248959559553)
          ·
            refine ⟨2833435444224186719669665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3777913925632248959559553 2833435444224186719669665)
            ·
              refine ⟨2125076583168140039752249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2833435444224186719669665 2125076583168140039752249)
              ·
                refine ⟨1593807437376105029814187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2125076583168140039752249 1593807437376105029814187)
                ·
                  refine ⟨2390711156064157544721281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593807437376105029814187 2390711156064157544721281)
                  ·
                    refine ⟨1793033367048118158540961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2390711156064157544721281 1793033367048118158540961)
                    ·
                      refine ⟨1344775025286088618905721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1793033367048118158540961 1344775025286088618905721)
                      ·
                        rfl

theorem cell23_2618940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_2618940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618940 prefixEnd_2618940 := by exact prefixLift 2618940
  have htrace : WordTrace (prefixWord ++ tailWord_2618940) baseStart_2618940 baseEnd_2618940 := by
    simpa [prefixWord, tailWord_2618940, baseEnd_2618940] using wordTrace_append hprefix tailTrace_2618940
  have hstable : (prefixWord ++ tailWord_2618940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618940).length < 2 ^ (prefixWord ++ tailWord_2618940).sum := by decide
  have hdescent : baseEnd_2618940 < baseStart_2618940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618945 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2618945 : Nat := 118140960795 + 2618945 * 2 ^ 59
def prefixEnd_2618945 : Nat := 4983230072969 + 3 ^ 40 * 2618945 * 2
def baseEnd_2618945 : Nat := 1344777592689361099343197

theorem tailTrace_2618945 : CollatzResearch.WordTrace tailWord_2618945 prefixEnd_2618945 1344777592689361099343197 := by
  unfold tailWord_2618945
  simp only [CollatzResearch.WordTrace]
  refine ⟨95520771497017020041314289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63680514331344680027542859 95520771497017020041314289)
  ·
    refine ⟨71640578622762765030985717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95520771497017020041314289 71640578622762765030985717)
    ·
      refine ⟨6716304245884009221654911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71640578622762765030985717 6716304245884009221654911)
      ·
        refine ⟨10074456368826013832482367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6716304245884009221654911 10074456368826013832482367)
        ·
          refine ⟨15111684553239020748723551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10074456368826013832482367 15111684553239020748723551)
          ·
            refine ⟨22667526829858531123085327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15111684553239020748723551 22667526829858531123085327)
            ·
              refine ⟨34001290244787796684627991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22667526829858531123085327 34001290244787796684627991)
              ·
                refine ⟨51001935367181695026941987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34001290244787796684627991 51001935367181695026941987)
                ·
                  refine ⟨76502903050772542540412981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51001935367181695026941987 76502903050772542540412981)
                  ·
                    refine ⟨7172147161009925863163717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76502903050772542540412981 7172147161009925863163717)
                    ·
                      refine ⟨1344777592689361099343197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7172147161009925863163717 1344777592689361099343197)
                      ·
                        rfl

theorem cell23_2618945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2618945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618945 prefixEnd_2618945 := by exact prefixLift 2618945
  have htrace : WordTrace (prefixWord ++ tailWord_2618945) baseStart_2618945 baseEnd_2618945 := by
    simpa [prefixWord, tailWord_2618945, baseEnd_2618945] using wordTrace_append hprefix tailTrace_2618945
  have hstable : (prefixWord ++ tailWord_2618945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618945).length < 2 ^ (prefixWord ++ tailWord_2618945).sum := by decide
  have hdescent : baseEnd_2618945 < baseStart_2618945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618965 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_2618965 : Nat := 118140960795 + 2618965 * 2 ^ 59
def prefixEnd_2618965 : Nat := 4983230072969 + 3 ^ 40 * 2618965 * 2
def baseEnd_2618965 : Nat := 1344787862302451021093105

theorem tailTrace_2618965 : CollatzResearch.WordTrace tailWord_2618965 prefixEnd_2618965 1344787862302451021093105 := by
  unfold tailWord_2618965
  simp only [CollatzResearch.WordTrace]
  refine ⟨95521500956944563457042349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63681000637963042304694899 95521500956944563457042349)
  ·
    refine ⟨35820562858854211296390881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95521500956944563457042349 35820562858854211296390881)
    ·
      refine ⟨26865422144140658472293161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35820562858854211296390881 26865422144140658472293161)
      ·
        refine ⟨20149066608105493854219871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26865422144140658472293161 20149066608105493854219871)
        ·
          refine ⟨30223599912158240781329807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20149066608105493854219871 30223599912158240781329807)
          ·
            refine ⟨45335399868237361171994711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30223599912158240781329807 45335399868237361171994711)
            ·
              refine ⟨68003099802356041757992067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45335399868237361171994711 68003099802356041757992067)
              ·
                refine ⟨102004649703534062636988101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68003099802356041757992067 102004649703534062636988101)
                ·
                  refine ⟨19125871819412636744435269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102004649703534062636988101 19125871819412636744435269)
                  ·
                    refine ⟨3586100966139869389581613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19125871819412636744435269 3586100966139869389581613)
                    ·
                      refine ⟨1344787862302451021093105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3586100966139869389581613 1344787862302451021093105)
                      ·
                        rfl

theorem cell23_2618965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_2618965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618965 prefixEnd_2618965 := by exact prefixLift 2618965
  have htrace : WordTrace (prefixWord ++ tailWord_2618965) baseStart_2618965 baseEnd_2618965 := by
    simpa [prefixWord, tailWord_2618965, baseEnd_2618965] using wordTrace_append hprefix tailTrace_2618965
  have hstable : (prefixWord ++ tailWord_2618965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618965).length < 2 ^ (prefixWord ++ tailWord_2618965).sum := by decide
  have hdescent : baseEnd_2618965 < baseStart_2618965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619015 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 1, 7]
def baseStart_2619015 : Nat := 118140960795 + 2619015 * 2 ^ 59
def prefixEnd_2619015 : Nat := 4983230072969 + 3 ^ 40 * 2619015 * 2
def baseEnd_2619015 : Nat := 448271178778391941822625

theorem tailTrace_2619015 : CollatzResearch.WordTrace tailWord_2619015 prefixEnd_2619015 448271178778391941822625 := by
  unfold tailWord_2619015
  simp only [CollatzResearch.WordTrace]
  refine ⟨95523324606763421996362499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63682216404508947997574999 95523324606763421996362499)
  ·
    refine ⟨143284986910145132994543749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95523324606763421996362499 143284986910145132994543749)
    ·
      refine ⟨26865935045652212436476953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143284986910145132994543749 26865935045652212436476953)
      ·
        refine ⟨20149451284239159327357715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26865935045652212436476953 20149451284239159327357715)
        ·
          refine ⟨30224176926358738991036573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20149451284239159327357715 30224176926358738991036573)
          ·
            refine ⟨11334066347384527121638715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30224176926358738991036573 11334066347384527121638715)
            ·
              refine ⟨17001099521076790682458073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11334066347384527121638715 17001099521076790682458073)
              ·
                refine ⟨12750824640807593011843555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17001099521076790682458073 12750824640807593011843555)
                ·
                  refine ⟨19126236961211389517765333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12750824640807593011843555 19126236961211389517765333)
                  ·
                    refine ⟨448271178778391941822625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19126236961211389517765333 448271178778391941822625)
                    ·
                      rfl

theorem cell23_2619015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_2619015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619015 prefixEnd_2619015 := by exact prefixLift 2619015
  have htrace : WordTrace (prefixWord ++ tailWord_2619015) baseStart_2619015 baseEnd_2619015 := by
    simpa [prefixWord, tailWord_2619015, baseEnd_2619015] using wordTrace_append hprefix tailTrace_2619015
  have hstable : (prefixWord ++ tailWord_2619015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619015).length < 2 ^ (prefixWord ++ tailWord_2619015).sum := by decide
  have hdescent : baseEnd_2619015 < baseStart_2619015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619036 : List Nat := [2, 2, 3, 2, 3, 2, 1, 3, 5]
def baseStart_2619036 : Nat := 118140960795 + 2619036 * 2 ^ 59
def prefixEnd_2619036 : Nat := 4983230072969 + 3 ^ 40 * 2619036 * 2
def baseEnd_2619036 : Nat := 149424924380991138145031

theorem tailTrace_2619036 : CollatzResearch.WordTrace tailWord_2619036 prefixEnd_2619036 149424924380991138145031 := by
  unfold tailWord_2619036
  simp only [CollatzResearch.WordTrace]
  refine ⟨47762045269843671291438481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63682727026458228388584641 47762045269843671291438481)
  ·
    refine ⟨35821533952382753468578861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47762045269843671291438481 35821533952382753468578861)
    ·
      refine ⟨13433075232143532550717073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35821533952382753468578861 13433075232143532550717073)
      ·
        refine ⟨10074806424107649413037805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13433075232143532550717073 10074806424107649413037805)
        ·
          refine ⟨3778052409040368529889177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10074806424107649413037805 3778052409040368529889177)
          ·
            refine ⟨2833539306780276397416883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3778052409040368529889177 2833539306780276397416883)
            ·
              refine ⟨4250308960170414596125325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833539306780276397416883 4250308960170414596125325)
              ·
                refine ⟨1593865860063905473546997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4250308960170414596125325 1593865860063905473546997)
                ·
                  refine ⟨149424924380991138145031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1593865860063905473546997 149424924380991138145031)
                  ·
                    rfl

theorem cell23_2619036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 5].length) (baseStart_2619036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619036 prefixEnd_2619036 := by exact prefixLift 2619036
  have htrace : WordTrace (prefixWord ++ tailWord_2619036) baseStart_2619036 baseEnd_2619036 := by
    simpa [prefixWord, tailWord_2619036, baseEnd_2619036] using wordTrace_append hprefix tailTrace_2619036
  have hstable : (prefixWord ++ tailWord_2619036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619036).length < 2 ^ (prefixWord ++ tailWord_2619036).sum := by decide
  have hdescent : baseEnd_2619036 < baseStart_2619036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619065 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2619065 : Nat := 118140960795 + 2619065 * 2 ^ 59
def prefixEnd_2619065 : Nat := 4983230072969 + 3 ^ 40 * 2619065 * 2
def baseEnd_2619065 : Nat := 1344839210367900629842645

theorem tailTrace_2619065 : CollatzResearch.WordTrace tailWord_2619065 prefixEnd_2619065 1344839210367900629842645 := by
  unfold tailWord_2619065
  simp only [CollatzResearch.WordTrace]
  refine ⟨95525148256582280535682649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63683432171054853690455099 95525148256582280535682649)
  ·
    refine ⟨71643861192436710401761987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95525148256582280535682649 71643861192436710401761987)
    ·
      refine ⟨107465791788655065602642981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71643861192436710401761987 107465791788655065602642981)
      ·
        refine ⟨20149835960372824800495559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107465791788655065602642981 20149835960372824800495559)
        ·
          refine ⟨30224753940559237200743339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20149835960372824800495559 30224753940559237200743339)
          ·
            refine ⟨45337130910838855801115009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30224753940559237200743339 45337130910838855801115009)
            ·
              refine ⟨34002848183129141850836257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45337130910838855801115009 34002848183129141850836257)
              ·
                refine ⟨25502136137346856388127193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34002848183129141850836257 25502136137346856388127193)
                ·
                  refine ⟨19126602103010142291095395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25502136137346856388127193 19126602103010142291095395)
                  ·
                    refine ⟨28689903154515213436643093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19126602103010142291095395 28689903154515213436643093)
                    ·
                      refine ⟨1344839210367900629842645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28689903154515213436643093 1344839210367900629842645)
                      ·
                        rfl

theorem cell23_2619065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2619065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619065 prefixEnd_2619065 := by exact prefixLift 2619065
  have htrace : WordTrace (prefixWord ++ tailWord_2619065) baseStart_2619065 baseEnd_2619065 := by
    simpa [prefixWord, tailWord_2619065, baseEnd_2619065] using wordTrace_append hprefix tailTrace_2619065
  have hstable : (prefixWord ++ tailWord_2619065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619065).length < 2 ^ (prefixWord ++ tailWord_2619065).sum := by decide
  have hdescent : baseEnd_2619065 < baseStart_2619065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619072 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 3]
def baseStart_2619072 : Nat := 118140960795 + 2619072 * 2 ^ 59
def prefixEnd_2619072 : Nat := 4983230072969 + 3 ^ 40 * 2619072 * 2
def baseEnd_2619072 : Nat := 1344842804732482102455113

theorem tailTrace_2619072 : CollatzResearch.WordTrace tailWord_2619072 prefixEnd_2619072 1344842804732482102455113 := by
  unfold tailWord_2619072
  simp only [CollatzResearch.WordTrace]
  refine ⟨47762701783778460365593735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63683602378371280487458313 47762701783778460365593735)
  ·
    refine ⟨71644052675667690548390603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47762701783778460365593735 71644052675667690548390603)
    ·
      refine ⟨107466079013501535822585905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71644052675667690548390603 107466079013501535822585905)
      ·
        refine ⟨80599559260126151866939429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107466079013501535822585905 80599559260126151866939429)
        ·
          refine ⟨15112417361273653475051143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80599559260126151866939429 15112417361273653475051143)
          ·
            refine ⟨22668626041910480212576715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15112417361273653475051143 22668626041910480212576715)
            ·
              refine ⟨34002939062865720318865073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22668626041910480212576715 34002939062865720318865073)
              ·
                refine ⟨25502204297149290239148805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34002939062865720318865073 25502204297149290239148805)
                ·
                  refine ⟨4781663305715491919840401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25502204297149290239148805 4781663305715491919840401)
                  ·
                    refine ⟨3586247479286618939880301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4781663305715491919840401 3586247479286618939880301)
                    ·
                      refine ⟨1344842804732482102455113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3586247479286618939880301 1344842804732482102455113)
                      ·
                        rfl

theorem cell23_2619072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_2619072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619072 prefixEnd_2619072 := by exact prefixLift 2619072
  have htrace : WordTrace (prefixWord ++ tailWord_2619072) baseStart_2619072 baseEnd_2619072 := by
    simpa [prefixWord, tailWord_2619072, baseEnd_2619072] using wordTrace_append hprefix tailTrace_2619072
  have hstable : (prefixWord ++ tailWord_2619072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619072).length < 2 ^ (prefixWord ++ tailWord_2619072).sum := by decide
  have hdescent : baseEnd_2619072 < baseStart_2619072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619089 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 2, 2, 3]
def baseStart_2619089 : Nat := 118140960795 + 2619089 * 2 ^ 59
def prefixEnd_2619089 : Nat := 4983230072969 + 3 ^ 40 * 2619089 * 2
def baseEnd_2619089 : Nat := 1344851533903608535942535

theorem tailTrace_2619089 : CollatzResearch.WordTrace tailWord_2619089 prefixEnd_2619089 1344851533903608535942535 := by
  unfold tailWord_2619089
  simp only [CollatzResearch.WordTrace]
  refine ⟨95526023608495332634556321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63684015738996888423037547 95526023608495332634556321)
  ·
    refine ⟨71644517706371499475917241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95526023608495332634556321 71644517706371499475917241)
    ·
      refine ⟨53733388279778624606937931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71644517706371499475917241 53733388279778624606937931)
      ·
        refine ⟨80600082419667936910406897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53733388279778624606937931 80600082419667936910406897)
        ·
          refine ⟨60450061814750952682805173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80600082419667936910406897 60450061814750952682805173)
          ·
            refine ⟨5667193295132901814012985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60450061814750952682805173 5667193295132901814012985)
            ·
              refine ⟨4250394971349676360509739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5667193295132901814012985 4250394971349676360509739)
              ·
                refine ⟨6375592457024514540764609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4250394971349676360509739 6375592457024514540764609)
                ·
                  refine ⟨4781694342768385905573457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6375592457024514540764609 4781694342768385905573457)
                  ·
                    refine ⟨3586270757076289429180093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4781694342768385905573457 3586270757076289429180093)
                    ·
                      refine ⟨1344851533903608535942535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3586270757076289429180093 1344851533903608535942535)
                      ·
                        rfl

theorem cell23_2619089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_2619089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619089 prefixEnd_2619089 := by exact prefixLift 2619089
  have htrace : WordTrace (prefixWord ++ tailWord_2619089) baseStart_2619089 baseEnd_2619089 := by
    simpa [prefixWord, tailWord_2619089, baseEnd_2619089] using wordTrace_append hprefix tailTrace_2619089
  have hstable : (prefixWord ++ tailWord_2619089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619089).length < 2 ^ (prefixWord ++ tailWord_2619089).sum := by decide
  have hdescent : baseEnd_2619089 < baseStart_2619089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619119 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 3, 1, 3]
def baseStart_2619119 : Nat := 118140960795 + 2619119 * 2 ^ 59
def prefixEnd_2619119 : Nat := 4983230072969 + 3 ^ 40 * 2619119 * 2
def baseEnd_2619119 : Nat := 1344866938323243418567397

theorem tailTrace_2619119 : CollatzResearch.WordTrace tailWord_2619119 prefixEnd_2619119 1344866938323243418567397 := by
  unfold tailWord_2619119
  simp only [CollatzResearch.WordTrace]
  refine ⟨95527117798386647758148411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63684745198924431838765607 95527117798386647758148411)
  ·
    refine ⟨143290676697579971637222617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95527117798386647758148411 143290676697579971637222617)
    ·
      refine ⟨107468007523184978727916963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143290676697579971637222617 107468007523184978727916963)
      ·
        refine ⟨161202011284777468091875445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107468007523184978727916963 161202011284777468091875445)
        ·
          refine ⟨15112688557947887633613323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161202011284777468091875445 15112688557947887633613323)
          ·
            refine ⟨22669032836921831450419985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15112688557947887633613323 22669032836921831450419985)
            ·
              refine ⟨17001774627691373587814989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22669032836921831450419985 17001774627691373587814989)
              ·
                refine ⟨6375665485384265095430621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17001774627691373587814989 6375665485384265095430621)
                ·
                  refine ⟨2390874557019099410786483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6375665485384265095430621 2390874557019099410786483)
                  ·
                    refine ⟨3586311835528649116179725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2390874557019099410786483 3586311835528649116179725)
                    ·
                      refine ⟨1344866938323243418567397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3586311835528649116179725 1344866938323243418567397)
                      ·
                        rfl

theorem cell23_2619119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 1, 3].length) (baseStart_2619119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619119 prefixEnd_2619119 := by exact prefixLift 2619119
  have htrace : WordTrace (prefixWord ++ tailWord_2619119) baseStart_2619119 baseEnd_2619119 := by
    simpa [prefixWord, tailWord_2619119, baseEnd_2619119] using wordTrace_append hprefix tailTrace_2619119
  have hstable : (prefixWord ++ tailWord_2619119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619119).length < 2 ^ (prefixWord ++ tailWord_2619119).sum := by decide
  have hdescent : baseEnd_2619119 < baseStart_2619119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619122 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_2619122 : Nat := 118140960795 + 2619122 * 2 ^ 59
def prefixEnd_2619122 : Nat := 4983230072969 + 3 ^ 40 * 2619122 * 2
def baseEnd_2619122 : Nat := 448289492921735635609961

theorem tailTrace_2619122 : CollatzResearch.WordTrace tailWord_2619122 prefixEnd_2619122 448289492921735635609961 := by
  unfold tailWord_2619122
  simp only [CollatzResearch.WordTrace]
  refine ⟨23881806804343944817626905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63684818144917186180338413 23881806804343944817626905)
  ·
    refine ⟨17911355103257958613220179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23881806804343944817626905 17911355103257958613220179)
    ·
      refine ⟨26867032654886937919830269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17911355103257958613220179 26867032654886937919830269)
      ·
        refine ⟨10075137245582601719936351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26867032654886937919830269 10075137245582601719936351)
        ·
          refine ⟨15112705868373902579904527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10075137245582601719936351 15112705868373902579904527)
          ·
            refine ⟨22669058802560853869856791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15112705868373902579904527 22669058802560853869856791)
            ·
              refine ⟨34003588203841280804785187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22669058802560853869856791 34003588203841280804785187)
              ·
                refine ⟨51005382305761921207177781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34003588203841280804785187 51005382305761921207177781)
                ·
                  refine ⟨4781754591165180113172917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51005382305761921207177781 4781754591165180113172917)
                  ·
                    refine ⟨448289492921735635609961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4781754591165180113172917 448289492921735635609961)
                    ·
                      rfl

theorem cell23_2619122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_2619122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619122 prefixEnd_2619122 := by exact prefixLift 2619122
  have htrace : WordTrace (prefixWord ++ tailWord_2619122) baseStart_2619122 baseEnd_2619122 := by
    simpa [prefixWord, tailWord_2619122, baseEnd_2619122] using wordTrace_append hprefix tailTrace_2619122
  have hstable : (prefixWord ++ tailWord_2619122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619122).length < 2 ^ (prefixWord ++ tailWord_2619122).sum := by decide
  have hdescent : baseEnd_2619122 < baseStart_2619122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619146 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 2, 3, 2]
def baseStart_2619146 : Nat := 118140960795 + 2619146 * 2 ^ 59
def prefixEnd_2619146 : Nat := 4983230072969 + 3 ^ 40 * 2619146 * 2
def baseEnd_2619146 : Nat := 1344880802300914812929773

theorem tailTrace_2619146 : CollatzResearch.WordTrace tailWord_2619146 prefixEnd_2619146 1344880802300914812929773 := by
  unfold tailWord_2619146
  simp only [CollatzResearch.WordTrace]
  refine ⟨23882025642322207842345323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63685401712859220912920861 23882025642322207842345323)
  ·
    refine ⟨35823038463483311763517985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23882025642322207842345323 35823038463483311763517985)
    ·
      refine ⟨26867278847612483822638489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35823038463483311763517985 26867278847612483822638489)
      ·
        refine ⟨20150459135709362866978867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26867278847612483822638489 20150459135709362866978867)
        ·
          refine ⟨30225688703564044300468301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20150459135709362866978867 30225688703564044300468301)
          ·
            refine ⟨11334633263836516612675613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30225688703564044300468301 11334633263836516612675613)
            ·
              refine ⟨4250487473938693729753355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11334633263836516612675613 4250487473938693729753355)
              ·
                refine ⟨6375731210908040594630033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4250487473938693729753355 6375731210908040594630033)
                ·
                  refine ⟨4781798408181030445972525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6375731210908040594630033 4781798408181030445972525)
                  ·
                    refine ⟨1793174403067886417239697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4781798408181030445972525 1793174403067886417239697)
                    ·
                      refine ⟨1344880802300914812929773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1793174403067886417239697 1344880802300914812929773)
                      ·
                        rfl

theorem cell23_2619146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_2619146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619146 prefixEnd_2619146 := by exact prefixLift 2619146
  have htrace : WordTrace (prefixWord ++ tailWord_2619146) baseStart_2619146 baseEnd_2619146 := by
    simpa [prefixWord, tailWord_2619146, baseEnd_2619146] using wordTrace_append hprefix tailTrace_2619146
  have hstable : (prefixWord ++ tailWord_2619146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619146).length < 2 ^ (prefixWord ++ tailWord_2619146).sum := by decide
  have hdescent : baseEnd_2619146 < baseStart_2619146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619169 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 4, 4]
def baseStart_2619169 : Nat := 118140960795 + 2619169 * 2 ^ 59
def prefixEnd_2619169 : Nat := 4983230072969 + 3 ^ 40 * 2619169 * 2
def baseEnd_2619169 : Nat := 448297537451989407647389

theorem tailTrace_2619169 : CollatzResearch.WordTrace tailWord_2619169 prefixEnd_2619169 448297537451989407647389 := by
  unfold tailWord_2619169
  simp only [CollatzResearch.WordTrace]
  refine ⟨95528941448205506297468561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63685960965470337531645707 95528941448205506297468561)
  ·
    refine ⟨71646706086154129723101421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95528941448205506297468561 71646706086154129723101421)
    ·
      refine ⟨26867514782307798646163033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71646706086154129723101421 26867514782307798646163033)
      ·
        refine ⟨20150636086730848984622275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26867514782307798646163033 20150636086730848984622275)
        ·
          refine ⟨30225954130096273476933413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20150636086730848984622275 30225954130096273476933413)
          ·
            refine ⟨5667366399393051276925015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30225954130096273476933413 5667366399393051276925015)
            ·
              refine ⟨8501049599089576915387523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5667366399393051276925015 8501049599089576915387523)
              ·
                refine ⟨12751574398634365373081285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8501049599089576915387523 12751574398634365373081285)
                ·
                  refine ⟨2390920199743943507452741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12751574398634365373081285 2390920199743943507452741)
                  ·
                    refine ⟨448297537451989407647389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2390920199743943507452741 448297537451989407647389)
                    ·
                      rfl

theorem cell23_2619169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_2619169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619169 prefixEnd_2619169 := by exact prefixLift 2619169
  have htrace : WordTrace (prefixWord ++ tailWord_2619169) baseStart_2619169 baseEnd_2619169 := by
    simpa [prefixWord, tailWord_2619169, baseEnd_2619169] using wordTrace_append hprefix tailTrace_2619169
  have hstable : (prefixWord ++ tailWord_2619169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619169).length < 2 ^ (prefixWord ++ tailWord_2619169).sum := by decide
  have hdescent : baseEnd_2619169 < baseStart_2619169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619189 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_2619189 : Nat := 118140960795 + 2619189 * 2 ^ 59
def prefixEnd_2619189 : Nat := 4983230072969 + 3 ^ 40 * 2619189 * 2
def baseEnd_2619189 : Nat := 1344902881969058144692075

theorem tailTrace_2619189 : CollatzResearch.WordTrace tailWord_2619189 prefixEnd_2619189 1344902881969058144692075 := by
  unfold tailWord_2619189
  simp only [CollatzResearch.WordTrace]
  refine ⟨95529670908133049713196621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63686447272088699808797747 95529670908133049713196621)
  ·
    refine ⟨35823626590549893642448733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95529670908133049713196621 35823626590549893642448733)
    ·
      refine ⟨13433859971456210115918275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35823626590549893642448733 13433859971456210115918275)
      ·
        refine ⟨20150789957184315173877413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13433859971456210115918275 20150789957184315173877413)
        ·
          refine ⟨3778273116972059095102015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20150789957184315173877413 3778273116972059095102015)
          ·
            refine ⟨5667409675458088642653023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3778273116972059095102015 5667409675458088642653023)
            ·
              refine ⟨8501114513187132963979535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5667409675458088642653023 8501114513187132963979535)
              ·
                refine ⟨12751671769780699445969303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8501114513187132963979535 12751671769780699445969303)
                ·
                  refine ⟨19127507654671049168953955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12751671769780699445969303 19127507654671049168953955)
                  ·
                    refine ⟨28691261482006573753430933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19127507654671049168953955 28691261482006573753430933)
                    ·
                      refine ⟨1344902881969058144692075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28691261482006573753430933 1344902881969058144692075)
                      ·
                        rfl

theorem cell23_2619189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_2619189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619189 prefixEnd_2619189 := by exact prefixLift 2619189
  have htrace : WordTrace (prefixWord ++ tailWord_2619189) baseStart_2619189 baseEnd_2619189 := by
    simpa [prefixWord, tailWord_2619189, baseEnd_2619189] using wordTrace_append hprefix tailTrace_2619189
  have hstable : (prefixWord ++ tailWord_2619189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619189).length < 2 ^ (prefixWord ++ tailWord_2619189).sum := by decide
  have hdescent : baseEnd_2619189 < baseStart_2619189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619193 : List Nat := [1, 2, 1, 7, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2619193 : Nat := 118140960795 + 2619193 * 2 ^ 59
def prefixEnd_2619193 : Nat := 4983230072969 + 3 ^ 40 * 2619193 * 2
def baseEnd_2619193 : Nat := 1344904935891676129042057

theorem tailTrace_2619193 : CollatzResearch.WordTrace tailWord_2619193 prefixEnd_2619193 1344904935891676129042057 := by
  unfold tailWord_2619193
  simp only [CollatzResearch.WordTrace]
  refine ⟨95529816800118558396342233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63686544533412372264228155 95529816800118558396342233)
  ·
    refine ⟨71647362600088918797256675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95529816800118558396342233 71647362600088918797256675)
    ·
      refine ⟨107471043900133378195885013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71647362600088918797256675 107471043900133378195885013)
      ·
        refine ⟨2518852591409376051466055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 107471043900133378195885013 2518852591409376051466055)
        ·
          refine ⟨3778278887114064077199083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2518852591409376051466055 3778278887114064077199083)
          ·
            refine ⟨5667418330671096115798625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3778278887114064077199083 5667418330671096115798625)
            ·
              refine ⟨4250563748003322086848969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5667418330671096115798625 4250563748003322086848969)
              ·
                refine ⟨3187922811002491565136727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4250563748003322086848969 3187922811002491565136727)
                ·
                  refine ⟨4781884216503737347705091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3187922811002491565136727 4781884216503737347705091)
                  ·
                    refine ⟨7172826324755606021557637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4781884216503737347705091 7172826324755606021557637)
                    ·
                      refine ⟨1344904935891676129042057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7172826324755606021557637 1344904935891676129042057)
                      ·
                        rfl

theorem cell23_2619193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2619193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619193 prefixEnd_2619193 := by exact prefixLift 2619193
  have htrace : WordTrace (prefixWord ++ tailWord_2619193) baseStart_2619193 baseEnd_2619193 := by
    simpa [prefixWord, tailWord_2619193, baseEnd_2619193] using wordTrace_append hprefix tailTrace_2619193
  have hstable : (prefixWord ++ tailWord_2619193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619193).length < 2 ^ (prefixWord ++ tailWord_2619193).sum := by decide
  have hdescent : baseEnd_2619193 < baseStart_2619193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619209 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 6, 1, 3]
def baseStart_2619209 : Nat := 118140960795 + 2619209 * 2 ^ 59
def prefixEnd_2619209 : Nat := 4983230072969 + 3 ^ 40 * 2619209 * 2
def baseEnd_2619209 : Nat := 1344913151582148066441983

theorem tailTrace_2619209 : CollatzResearch.WordTrace tailWord_2619209 prefixEnd_2619209 1344913151582148066441983 := by
  unfold tailWord_2619209
  simp only [CollatzResearch.WordTrace]
  refine ⟨95530400368060593128924681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63686933578707062085949787 95530400368060593128924681)
  ·
    refine ⟨71647800276045444846693511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95530400368060593128924681 71647800276045444846693511)
    ·
      refine ⟨107471700414068167270040267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71647800276045444846693511 107471700414068167270040267)
      ·
        refine ⟨161207550621102250905060401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107471700414068167270040267 161207550621102250905060401)
        ·
          refine ⟨120905662965826688178795301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161207550621102250905060401 120905662965826688178795301)
          ·
            refine ⟨22669811806092504033524119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120905662965826688178795301 22669811806092504033524119)
            ·
              refine ⟨34004717709138756050286179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22669811806092504033524119 34004717709138756050286179)
              ·
                refine ⟨51007076563708134075429269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34004717709138756050286179 51007076563708134075429269)
                ·
                  refine ⟨2390956713923818784785747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51007076563708134075429269 2390956713923818784785747)
                  ·
                    refine ⟨3586435070885728177178621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2390956713923818784785747 3586435070885728177178621)
                    ·
                      refine ⟨1344913151582148066441983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3586435070885728177178621 1344913151582148066441983)
                      ·
                        rfl

theorem cell23_2619209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 1, 3].length) (baseStart_2619209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619209 prefixEnd_2619209 := by exact prefixLift 2619209
  have htrace : WordTrace (prefixWord ++ tailWord_2619209) baseStart_2619209 baseEnd_2619209 := by
    simpa [prefixWord, tailWord_2619209, baseEnd_2619209] using wordTrace_append hprefix tailTrace_2619209
  have hstable : (prefixWord ++ tailWord_2619209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619209).length < 2 ^ (prefixWord ++ tailWord_2619209).sum := by decide
  have hdescent : baseEnd_2619209 < baseStart_2619209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619213 : List Nat := [1, 6, 1, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2619213 : Nat := 118140960795 + 2619213 * 2 ^ 59
def prefixEnd_2619213 : Nat := 4983230072969 + 3 ^ 40 * 2619213 * 2
def baseEnd_2619213 : Nat := 1344915205504766050791965

theorem tailTrace_2619213 : CollatzResearch.WordTrace tailWord_2619213 prefixEnd_2619213 1344915205504766050791965 := by
  unfold tailWord_2619213
  simp only [CollatzResearch.WordTrace]
  refine ⟨95530546260046101812070293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63687030840030734541380195 95530546260046101812070293)
  ·
    refine ⟨4477994355939661022440795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95530546260046101812070293 4477994355939661022440795)
    ·
      refine ⟨6716991533909491533661193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4477994355939661022440795 6716991533909491533661193)
      ·
        refine ⟨5037743650432118650245895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6716991533909491533661193 5037743650432118650245895)
        ·
          refine ⟨7556615475648177975368843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5037743650432118650245895 7556615475648177975368843)
          ·
            refine ⟨11334923213472266963053265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7556615475648177975368843 11334923213472266963053265)
            ·
              refine ⟨8501192410104200222289949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11334923213472266963053265 8501192410104200222289949)
              ·
                refine ⟨3187947153789075083358731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8501192410104200222289949 3187947153789075083358731)
                ·
                  refine ⟨4781920730683612625038097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3187947153789075083358731 4781920730683612625038097)
                  ·
                    refine ⟨3586440548012709468778573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4781920730683612625038097 3586440548012709468778573)
                    ·
                      refine ⟨1344915205504766050791965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3586440548012709468778573 1344915205504766050791965)
                      ·
                        rfl

theorem cell23_2619213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2619213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619213 prefixEnd_2619213 := by exact prefixLift 2619213
  have htrace : WordTrace (prefixWord ++ tailWord_2619213) baseStart_2619213 baseEnd_2619213 := by
    simpa [prefixWord, tailWord_2619213, baseEnd_2619213] using wordTrace_append hprefix tailTrace_2619213
  have hstable : (prefixWord ++ tailWord_2619213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619213).length < 2 ^ (prefixWord ++ tailWord_2619213).sum := by decide
  have hdescent : baseEnd_2619213 < baseStart_2619213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619219 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 7, 3, 2]
def baseStart_2619219 : Nat := 118140960795 + 2619219 * 2 ^ 59
def prefixEnd_2619219 : Nat := 4983230072969 + 3 ^ 40 * 2619219 * 2
def baseEnd_2619219 : Nat := 1344918286388693027316937

theorem tailTrace_2619219 : CollatzResearch.WordTrace tailWord_2619219 prefixEnd_2619219 1344918286388693027316937 := by
  unfold tailWord_2619219
  simp only [CollatzResearch.WordTrace]
  refine ⟨95530765098024364836788711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63687176732016243224525807 95530765098024364836788711)
  ·
    refine ⟨143296147647036547255183067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95530765098024364836788711 143296147647036547255183067)
    ·
      refine ⟨214944221470554820882774601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143296147647036547255183067 214944221470554820882774601)
      ·
        refine ⟨161208166102916115662080951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214944221470554820882774601 161208166102916115662080951)
        ·
          refine ⟨241812249154374173493121427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161208166102916115662080951 241812249154374173493121427)
          ·
            refine ⟨362718373731561260239682141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241812249154374173493121427 362718373731561260239682141)
            ·
              refine ⟨136019390149335472589880803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 362718373731561260239682141 136019390149335472589880803)
              ·
                refine ⟨204029085224003208884821205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136019390149335472589880803 204029085224003208884821205)
                ·
                  refine ⟨4781931684937575208237997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 204029085224003208884821205 4781931684937575208237997)
                  ·
                    refine ⟨1793224381851590703089249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4781931684937575208237997 1793224381851590703089249)
                    ·
                      refine ⟨1344918286388693027316937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1793224381851590703089249 1344918286388693027316937)
                      ·
                        rfl

theorem cell23_2619219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 3, 2].length) (baseStart_2619219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619219 prefixEnd_2619219 := by exact prefixLift 2619219
  have htrace : WordTrace (prefixWord ++ tailWord_2619219) baseStart_2619219 baseEnd_2619219 := by
    simpa [prefixWord, tailWord_2619219, baseEnd_2619219] using wordTrace_append hprefix tailTrace_2619219
  have hstable : (prefixWord ++ tailWord_2619219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619219).length < 2 ^ (prefixWord ++ tailWord_2619219).sum := by decide
  have hdescent : baseEnd_2619219 < baseStart_2619219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619226 : List Nat := [3, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3]
def baseStart_2619226 : Nat := 118140960795 + 2619226 * 2 ^ 59
def prefixEnd_2619226 : Nat := 4983230072969 + 3 ^ 40 * 2619226 * 2
def baseEnd_2619226 : Nat := 1344921880753274499929405

theorem tailTrace_2619226 : CollatzResearch.WordTrace tailWord_2619226 prefixEnd_2619226 1344921880753274499929405 := by
  unfold tailWord_2619226
  simp only [CollatzResearch.WordTrace]
  refine ⟨23882755102249751258073383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63687346939332670021529021 23882755102249751258073383)
  ·
    refine ⟨35824132653374626887110075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23882755102249751258073383 35824132653374626887110075)
    ·
      refine ⟨53736198980061940330665113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35824132653374626887110075 53736198980061940330665113)
      ·
        refine ⟨40302149235046455247998835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53736198980061940330665113 40302149235046455247998835)
        ·
          refine ⟨60453223852569682871998253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40302149235046455247998835 60453223852569682871998253)
          ·
            refine ⟨22669958944713631076999345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60453223852569682871998253 22669958944713631076999345)
            ·
              refine ⟨17002469208535223307749509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22669958944713631076999345 17002469208535223307749509)
              ·
                refine ⟨3187962976600354370203033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17002469208535223307749509 3187962976600354370203033)
                ·
                  refine ⟨2390972232450265777652275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3187962976600354370203033 2390972232450265777652275)
                  ·
                    refine ⟨3586458348675398666478413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2390972232450265777652275 3586458348675398666478413)
                    ·
                      refine ⟨1344921880753274499929405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3586458348675398666478413 1344921880753274499929405)
                      ·
                        rfl

theorem cell23_2619226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_2619226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619226 prefixEnd_2619226 := by exact prefixLift 2619226
  have htrace : WordTrace (prefixWord ++ tailWord_2619226) baseStart_2619226 baseEnd_2619226 := by
    simpa [prefixWord, tailWord_2619226, baseEnd_2619226] using wordTrace_append hprefix tailTrace_2619226
  have hstable : (prefixWord ++ tailWord_2619226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619226).length < 2 ^ (prefixWord ++ tailWord_2619226).sum := by decide
  have hdescent : baseEnd_2619226 < baseStart_2619226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619312 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 5]
def baseStart_2619312 : Nat := 118140960795 + 2619312 * 2 ^ 59
def prefixEnd_2619312 : Nat := 4983230072969 + 3 ^ 40 * 2619312 * 2
def baseEnd_2619312 : Nat := 1344966040089561163454009

theorem tailTrace_2619312 : CollatzResearch.WordTrace tailWord_2619312 prefixEnd_2619312 1344966040089561163454009 := by
  unfold tailWord_2619312
  simp only [CollatzResearch.WordTrace]
  refine ⟨47767078543343720859962095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63689438057791627813282793 47767078543343720859962095)
  ·
    refine ⟨71650617815015581289943143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47767078543343720859962095 71650617815015581289943143)
    ·
      refine ⟨107475926722523371934914715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71650617815015581289943143 107475926722523371934914715)
      ·
        refine ⟨161213890083785057902372073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107475926722523371934914715 161213890083785057902372073)
        ·
          refine ⟨120910417562838793426779055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161213890083785057902372073 120910417562838793426779055)
          ·
            refine ⟨181365626344258190140168583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120910417562838793426779055 181365626344258190140168583)
            ·
              refine ⟨272048439516387285210252875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181365626344258190140168583 272048439516387285210252875)
              ·
                refine ⟨408072659274580927815379313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272048439516387285210252875 408072659274580927815379313)
                ·
                  refine ⟨306054494455935695861534485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408072659274580927815379313 306054494455935695861534485)
                  ·
                    refine ⟨14346304427621985743509429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 306054494455935695861534485 14346304427621985743509429)
                    ·
                      refine ⟨1344966040089561163454009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14346304427621985743509429 1344966040089561163454009)
                      ·
                        rfl

theorem cell23_2619312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_2619312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619312 prefixEnd_2619312 := by exact prefixLift 2619312
  have htrace : WordTrace (prefixWord ++ tailWord_2619312) baseStart_2619312 baseEnd_2619312 := by
    simpa [prefixWord, tailWord_2619312, baseEnd_2619312] using wordTrace_append hprefix tailTrace_2619312
  have hstable : (prefixWord ++ tailWord_2619312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619312).length < 2 ^ (prefixWord ++ tailWord_2619312).sum := by decide
  have hdescent : baseEnd_2619312 < baseStart_2619312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619339 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 4]
def baseStart_2619339 : Nat := 118140960795 + 2619339 * 2 ^ 59
def prefixEnd_2619339 : Nat := 4983230072969 + 3 ^ 40 * 2619339 * 2
def baseEnd_2619339 : Nat := 1344979904067232557816385

theorem tailTrace_2619339 : CollatzResearch.WordTrace tailWord_2619339 prefixEnd_2619339 1344979904067232557816385 := by
  unfold tailWord_2619339
  simp only [CollatzResearch.WordTrace]
  refine ⟨95535141857589625331157071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63690094571726416887438047 95535141857589625331157071)
  ·
    refine ⟨143302712786384437996735607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95535141857589625331157071 143302712786384437996735607)
    ·
      refine ⟨214954069179576656995103411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143302712786384437996735607 214954069179576656995103411)
      ·
        refine ⟨322431103769364985492655117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214954069179576656995103411 322431103769364985492655117)
        ·
          refine ⟨120911663913511869559745669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322431103769364985492655117 120911663913511869559745669)
          ·
            refine ⟨22670936983783475542452313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120911663913511869559745669 22670936983783475542452313)
            ·
              refine ⟨17003202737837606656839235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22670936983783475542452313 17003202737837606656839235)
              ·
                refine ⟨25504804106756409985258853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17003202737837606656839235 25504804106756409985258853)
                ·
                  refine ⟨4782150770016826872236035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25504804106756409985258853 4782150770016826872236035)
                  ·
                    refine ⟨7173226155025240308354053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4782150770016826872236035 7173226155025240308354053)
                    ·
                      refine ⟨1344979904067232557816385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7173226155025240308354053 1344979904067232557816385)
                      ·
                        rfl

theorem cell23_2619339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 4].length) (baseStart_2619339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619339 prefixEnd_2619339 := by exact prefixLift 2619339
  have htrace : WordTrace (prefixWord ++ tailWord_2619339) baseStart_2619339 baseEnd_2619339 := by
    simpa [prefixWord, tailWord_2619339, baseEnd_2619339] using wordTrace_append hprefix tailTrace_2619339
  have hstable : (prefixWord ++ tailWord_2619339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619339).length < 2 ^ (prefixWord ++ tailWord_2619339).sum := by decide
  have hdescent : baseEnd_2619339 < baseStart_2619339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619400 : List Nat := [2, 1, 3, 2, 1, 2, 5, 2, 1, 4]
def baseStart_2619400 : Nat := 118140960795 + 2619400 * 2 ^ 59
def prefixEnd_2619400 : Nat := 4983230072969 + 3 ^ 40 * 2619400 * 2
def baseEnd_2619400 : Nat := 448337075462385606384535

theorem tailTrace_2619400 : CollatzResearch.WordTrace tailWord_2619400 prefixEnd_2619400 448337075462385606384535 := by
  unfold tailWord_2619400
  simp only [CollatzResearch.WordTrace]
  refine ⟨47768683355184316374563827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63691577806912421832751769 47768683355184316374563827)
  ·
    refine ⟨71653025032776474561845741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47768683355184316374563827 71653025032776474561845741)
    ·
      refine ⟨26869884387291177960692153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71653025032776474561845741 26869884387291177960692153)
      ·
        refine ⟨20152413290468383470519115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26869884387291177960692153 20152413290468383470519115)
        ·
          refine ⟨30228619935702575205778673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20152413290468383470519115 30228619935702575205778673)
          ·
            refine ⟨22671464951776931404334005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30228619935702575205778673 22671464951776931404334005)
            ·
              refine ⟨2125449839229087319156313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22671464951776931404334005 2125449839229087319156313)
              ·
                refine ⟨1594087379421815489367235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2125449839229087319156313 1594087379421815489367235)
                ·
                  refine ⟨2391131069132723234050853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594087379421815489367235 2391131069132723234050853)
                  ·
                    refine ⟨448337075462385606384535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2391131069132723234050853 448337075462385606384535)
                    ·
                      rfl

theorem cell23_2619400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_2619400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619400 prefixEnd_2619400 := by exact prefixLift 2619400
  have htrace : WordTrace (prefixWord ++ tailWord_2619400) baseStart_2619400 baseEnd_2619400 := by
    simpa [prefixWord, tailWord_2619400, baseEnd_2619400] using wordTrace_append hprefix tailTrace_2619400
  have hstable : (prefixWord ++ tailWord_2619400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619400).length < 2 ^ (prefixWord ++ tailWord_2619400).sum := by decide
  have hdescent : baseEnd_2619400 < baseStart_2619400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619426 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_2619426 : Nat := 118140960795 + 2619426 * 2 ^ 59
def prefixEnd_2619426 : Nat := 4983230072969 + 3 ^ 40 * 2619426 * 2
def baseEnd_2619426 : Nat := 448341525628057905809495

theorem tailTrace_2619426 : CollatzResearch.WordTrace tailWord_2619426 prefixEnd_2619426 448341525628057905809495 := by
  unfold tailWord_2619426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23884578752068609797393533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63692210005516292793049421 23884578752068609797393533)
  ·
    refine ⟨8956717032025728674022575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23884578752068609797393533 8956717032025728674022575)
    ·
      refine ⟨13435075548038593011033863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8956717032025728674022575 13435075548038593011033863)
      ·
        refine ⟨20152613322057889516550795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13435075548038593011033863 20152613322057889516550795)
        ·
          refine ⟨30228919983086834274826193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20152613322057889516550795 30228919983086834274826193)
          ·
            refine ⟨22671689987315125706119645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30228919983086834274826193 22671689987315125706119645)
            ·
              refine ⟨8501883745243172139794867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22671689987315125706119645 8501883745243172139794867)
              ·
                refine ⟨12752825617864758209692301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8501883745243172139794867 12752825617864758209692301)
                ·
                  refine ⟨4782309606699284328634613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12752825617864758209692301 4782309606699284328634613)
                  ·
                    refine ⟨448341525628057905809495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4782309606699284328634613 448341525628057905809495)
                    ·
                      rfl

theorem cell23_2619426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_2619426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619426 prefixEnd_2619426 := by exact prefixLift 2619426
  have htrace : WordTrace (prefixWord ++ tailWord_2619426) baseStart_2619426 baseEnd_2619426 := by
    simpa [prefixWord, tailWord_2619426, baseEnd_2619426] using wordTrace_append hprefix tailTrace_2619426
  have hstable : (prefixWord ++ tailWord_2619426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619426).length < 2 ^ (prefixWord ++ tailWord_2619426).sum := by decide
  have hdescent : baseEnd_2619426 < baseStart_2619426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619457 : List Nat := [1, 2, 5, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_2619457 : Nat := 118140960795 + 2619457 * 2 ^ 59
def prefixEnd_2619457 : Nat := 4983230072969 + 3 ^ 40 * 2619457 * 2
def baseEnd_2619457 : Nat := 1345040494784463096140843

theorem tailTrace_2619457 : CollatzResearch.WordTrace tailWord_2619457 prefixEnd_2619457 1345040494784463096140843 := by
  unfold tailWord_2619457
  simp only [CollatzResearch.WordTrace]
  refine ⟨95539445671162131483952625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63692963780774754322635083 95539445671162131483952625)
  ·
    refine ⟨71654584253371598612964469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95539445671162131483952625 71654584253371598612964469)
    ·
      refine ⟨6717617273753587369965419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71654584253371598612964469 6717617273753587369965419)
      ·
        refine ⟨10076425910630381054948129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6717617273753587369965419 10076425910630381054948129)
        ·
          refine ⟨7557319432972785791211097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10076425910630381054948129 7557319432972785791211097)
          ·
            refine ⟨5667989574729589343408323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7557319432972785791211097 5667989574729589343408323)
            ·
              refine ⟨8501984362094384015112485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5667989574729589343408323 8501984362094384015112485)
              ·
                refine ⟨1594122067892697002833591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8501984362094384015112485 1594122067892697002833591)
                ·
                  refine ⟨2391183101839045504250387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594122067892697002833591 2391183101839045504250387)
                  ·
                    refine ⟨3586774652758568256375581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2391183101839045504250387 3586774652758568256375581)
                    ·
                      refine ⟨1345040494784463096140843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3586774652758568256375581 1345040494784463096140843)
                      ·
                        rfl

theorem cell23_2619457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_2619457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619457 prefixEnd_2619457 := by exact prefixLift 2619457
  have htrace : WordTrace (prefixWord ++ tailWord_2619457) baseStart_2619457 baseEnd_2619457 := by
    simpa [prefixWord, tailWord_2619457, baseEnd_2619457] using wordTrace_append hprefix tailTrace_2619457
  have hstable : (prefixWord ++ tailWord_2619457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619457).length < 2 ^ (prefixWord ++ tailWord_2619457).sum := by decide
  have hdescent : baseEnd_2619457 < baseStart_2619457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619459 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 6]
def baseStart_2619459 : Nat := 118140960795 + 2619459 * 2 ^ 59
def prefixEnd_2619459 : Nat := 4983230072969 + 3 ^ 40 * 2619459 * 2
def baseEnd_2619459 : Nat := 1345041521745772088315833

theorem tailTrace_2619459 : CollatzResearch.WordTrace tailWord_2619459 prefixEnd_2619459 1345041521745772088315833 := by
  unfold tailWord_2619459
  simp only [CollatzResearch.WordTrace]
  refine ⟨95539518617154885825525431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63693012411436590550350287 95539518617154885825525431)
  ·
    refine ⟨143309277925732328738288147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95539518617154885825525431 143309277925732328738288147)
    ·
      refine ⟨214963916888598493107432221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143309277925732328738288147 214963916888598493107432221)
      ·
        refine ⟨80611468833224434915287083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214963916888598493107432221 80611468833224434915287083)
        ·
          refine ⟨120917203249836652372930625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80611468833224434915287083 120917203249836652372930625)
          ·
            refine ⟨90687902437377489279697969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120917203249836652372930625 90687902437377489279697969)
            ·
              refine ⟨68015926828033116959773477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90687902437377489279697969 68015926828033116959773477)
              ·
                refine ⟨12752986280256209429957527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68015926828033116959773477 12752986280256209429957527)
                ·
                  refine ⟨19129479420384314144936291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12752986280256209429957527 19129479420384314144936291)
                  ·
                    refine ⟨28694219130576471217404437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19129479420384314144936291 28694219130576471217404437)
                    ·
                      refine ⟨1345041521745772088315833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28694219130576471217404437 1345041521745772088315833)
                      ·
                        rfl

theorem cell23_2619459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_2619459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619459 prefixEnd_2619459 := by exact prefixLift 2619459
  have htrace : WordTrace (prefixWord ++ tailWord_2619459) baseStart_2619459 baseEnd_2619459 := by
    simpa [prefixWord, tailWord_2619459, baseEnd_2619459] using wordTrace_append hprefix tailTrace_2619459
  have hstable : (prefixWord ++ tailWord_2619459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619459).length < 2 ^ (prefixWord ++ tailWord_2619459).sum := by decide
  have hdescent : baseEnd_2619459 < baseStart_2619459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619480 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 3, 2, 2]
def baseStart_2619480 : Nat := 118140960795 + 2619480 * 2 ^ 59
def prefixEnd_2619480 : Nat := 4983230072969 + 3 ^ 40 * 2619480 * 2
def baseEnd_2619480 : Nat := 1345052304839516506153237

theorem tailTrace_2619480 : CollatzResearch.WordTrace tailWord_2619480 prefixEnd_2619480 1345052304839516506153237 := by
  unfold tailWord_2619480
  simp only [CollatzResearch.WordTrace]
  refine ⟨47770142275039403206019947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63693523033385870941359929 47770142275039403206019947)
  ·
    refine ⟨71655213412559104809029921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47770142275039403206019947 71655213412559104809029921)
    ·
      refine ⟨53741410059419328606772441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71655213412559104809029921 53741410059419328606772441)
      ·
        refine ⟨40306057544564496455079331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53741410059419328606772441 40306057544564496455079331)
        ·
          refine ⟨60459086316846744682618997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40306057544564496455079331 60459086316846744682618997)
          ·
            refine ⟨5668039342204382313995531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60459086316846744682618997 5668039342204382313995531)
            ·
              refine ⟨8502059013306573470993297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5668039342204382313995531 8502059013306573470993297)
              ·
                refine ⟨6376544259979930103244973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8502059013306573470993297 6376544259979930103244973)
                ·
                  refine ⟨2391204097492473788716865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6376544259979930103244973 2391204097492473788716865)
                  ·
                    refine ⟨1793403073119355341537649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2391204097492473788716865 1793403073119355341537649)
                    ·
                      refine ⟨1345052304839516506153237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1793403073119355341537649 1345052304839516506153237)
                      ·
                        rfl

theorem cell23_2619480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_2619480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619480 prefixEnd_2619480 := by exact prefixLift 2619480
  have htrace : WordTrace (prefixWord ++ tailWord_2619480) baseStart_2619480 baseEnd_2619480 := by
    simpa [prefixWord, tailWord_2619480, baseEnd_2619480] using wordTrace_append hprefix tailTrace_2619480
  have hstable : (prefixWord ++ tailWord_2619480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619480).length < 2 ^ (prefixWord ++ tailWord_2619480).sum := by decide
  have hdescent : baseEnd_2619480 < baseStart_2619480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619497 : List Nat := [1, 2, 1, 1, 1, 5, 4, 3, 1, 2, 2]
def baseStart_2619497 : Nat := 118140960795 + 2619497 * 2 ^ 59
def prefixEnd_2619497 : Nat := 4983230072969 + 3 ^ 40 * 2619497 * 2
def baseEnd_2619497 : Nat := 1345061034010642939640659

theorem tailTrace_2619497 : CollatzResearch.WordTrace tailWord_2619497 prefixEnd_2619497 1345061034010642939640659 := by
  unfold tailWord_2619497
  simp only [CollatzResearch.WordTrace]
  refine ⟨95540904591017218315408745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63693936394011478876939163 95540904591017218315408745)
  ·
    refine ⟨71655678443262913736556559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95540904591017218315408745 71655678443262913736556559)
    ·
      refine ⟨107483517664894370604834839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71655678443262913736556559 107483517664894370604834839)
      ·
        refine ⟨161225276497341555907252259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107483517664894370604834839 161225276497341555907252259)
        ·
          refine ⟨241837914746012333860878389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161225276497341555907252259 241837914746012333860878389)
          ·
            refine ⟨22672304507438656299457349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 241837914746012333860878389 22672304507438656299457349)
            ·
              refine ⟨4251057095144748056148253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22672304507438656299457349 4251057095144748056148253)
              ·
                refine ⟨1594146410679280521055595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4251057095144748056148253 1594146410679280521055595)
                ·
                  refine ⟨2391219616018920781583393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594146410679280521055595 2391219616018920781583393)
                  ·
                    refine ⟨1793414712014190586187545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2391219616018920781583393 1793414712014190586187545)
                    ·
                      refine ⟨1345061034010642939640659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1793414712014190586187545 1345061034010642939640659)
                      ·
                        rfl

theorem cell23_2619497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 1, 2, 2].length) (baseStart_2619497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619497 prefixEnd_2619497 := by exact prefixLift 2619497
  have htrace : WordTrace (prefixWord ++ tailWord_2619497) baseStart_2619497 baseEnd_2619497 := by
    simpa [prefixWord, tailWord_2619497, baseEnd_2619497] using wordTrace_append hprefix tailTrace_2619497
  have hstable : (prefixWord ++ tailWord_2619497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619497).length < 2 ^ (prefixWord ++ tailWord_2619497).sum := by decide
  have hdescent : baseEnd_2619497 < baseStart_2619497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619500 : List Nat := [2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 3]
def baseStart_2619500 : Nat := 118140960795 + 2619500 * 2 ^ 59
def prefixEnd_2619500 : Nat := 4983230072969 + 3 ^ 40 * 2619500 * 2
def baseEnd_2619500 : Nat := 1345062574452606427903145

theorem tailTrace_2619500 : CollatzResearch.WordTrace tailWord_2619500 prefixEnd_2619500 1345062574452606427903145 := by
  unfold tailWord_2619500
  simp only [CollatzResearch.WordTrace]
  refine ⟨47770507005003174913883977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63694009340004233218511969 47770507005003174913883977)
  ·
    refine ⟨35827880253752381185412983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47770507005003174913883977 35827880253752381185412983)
    ·
      refine ⟨53741820380628571778119475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35827880253752381185412983 53741820380628571778119475)
      ·
        refine ⟨80612730570942857667179213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53741820380628571778119475 80612730570942857667179213)
        ·
          refine ⟨30229773964103571625192205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80612730570942857667179213 30229773964103571625192205)
          ·
            refine ⟨11336165236538839359447077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30229773964103571625192205 11336165236538839359447077)
            ·
              refine ⟨2125530981851032379896327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11336165236538839359447077 2125530981851032379896327)
              ·
                refine ⟨3188296472776548569844491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125530981851032379896327 3188296472776548569844491)
                ·
                  refine ⟨4782444709164822854766737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3188296472776548569844491 4782444709164822854766737)
                  ·
                    refine ⟨3586833531873617141075053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4782444709164822854766737 3586833531873617141075053)
                    ·
                      refine ⟨1345062574452606427903145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3586833531873617141075053 1345062574452606427903145)
                      ·
                        rfl

theorem cell23_2619500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 3].length) (baseStart_2619500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619500 prefixEnd_2619500 := by exact prefixLift 2619500
  have htrace : WordTrace (prefixWord ++ tailWord_2619500) baseStart_2619500 baseEnd_2619500 := by
    simpa [prefixWord, tailWord_2619500, baseEnd_2619500] using wordTrace_append hprefix tailTrace_2619500
  have hstable : (prefixWord ++ tailWord_2619500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619500).length < 2 ^ (prefixWord ++ tailWord_2619500).sum := by decide
  have hdescent : baseEnd_2619500 < baseStart_2619500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619530 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_2619530 : Nat := 118140960795 + 2619530 * 2 ^ 59
def prefixEnd_2619530 : Nat := 4983230072969 + 3 ^ 40 * 2619530 * 2
def baseEnd_2619530 : Nat := 1345077978872241310528007

theorem tailTrace_2619530 : CollatzResearch.WordTrace tailWord_2619530 prefixEnd_2619530 1345077978872241310528007 := by
  unfold tailWord_2619530
  simp only [CollatzResearch.WordTrace]
  refine ⟨23885527049974416237840011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63694738799931776634240029 23885527049974416237840011)
  ·
    refine ⟨35828290574961624356760017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23885527049974416237840011 35828290574961624356760017)
    ·
      refine ⟨26871217931221218267570013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35828290574961624356760017 26871217931221218267570013)
      ·
        refine ⟨10076706724207956850338755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26871217931221218267570013 10076706724207956850338755)
        ·
          refine ⟨15115060086311935275508133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10076706724207956850338755 15115060086311935275508133)
          ·
            refine ⟨2834073766183487864157775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15115060086311935275508133 2834073766183487864157775)
            ·
              refine ⟨4251110649275231796236663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834073766183487864157775 4251110649275231796236663)
              ·
                refine ⟨6376665973912847694354995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4251110649275231796236663 6376665973912847694354995)
                ·
                  refine ⟨9564998960869271541532493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6376665973912847694354995 9564998960869271541532493)
                  ·
                    refine ⟨3586874610325976828074685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9564998960869271541532493 3586874610325976828074685)
                    ·
                      refine ⟨1345077978872241310528007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3586874610325976828074685 1345077978872241310528007)
                      ·
                        rfl

theorem cell23_2619530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_2619530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619530 prefixEnd_2619530 := by exact prefixLift 2619530
  have htrace : WordTrace (prefixWord ++ tailWord_2619530) baseStart_2619530 baseEnd_2619530 := by
    simpa [prefixWord, tailWord_2619530, baseEnd_2619530] using wordTrace_append hprefix tailTrace_2619530
  have hstable : (prefixWord ++ tailWord_2619530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619530).length < 2 ^ (prefixWord ++ tailWord_2619530).sum := by decide
  have hdescent : baseEnd_2619530 < baseStart_2619530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619542 : List Nat := [5, 3, 2, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_2619542 : Nat := 118140960795 + 2619542 * 2 ^ 59
def prefixEnd_2619542 : Nat := 4983230072969 + 3 ^ 40 * 2619542 * 2
def baseEnd_2619542 : Nat := 1345084140640095263577953

theorem tailTrace_2619542 : CollatzResearch.WordTrace tailWord_2619542 prefixEnd_2619542 1345084140640095263577953 := by
  unfold tailWord_2619542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5971409117240886937549805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63695030583902794000531253 5971409117240886937549805)
  ·
    refine ⟨2239278418965332601581177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5971409117240886937549805 2239278418965332601581177)
    ·
      refine ⟨1679458814223999451185883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2239278418965332601581177 1679458814223999451185883)
      ·
        refine ⟨2519188221335999176778825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1679458814223999451185883 2519188221335999176778825)
        ·
          refine ⟨1889391166001999382584119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2519188221335999176778825 1889391166001999382584119)
          ·
            refine ⟨2834086749002999073876179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889391166001999382584119 2834086749002999073876179)
            ·
              refine ⟨4251130123504498610814269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834086749002999073876179 4251130123504498610814269)
              ·
                refine ⟨1594173796314186979055351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4251130123504498610814269 1594173796314186979055351)
                ·
                  refine ⟨2391260694471280468583027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594173796314186979055351 2391260694471280468583027)
                  ·
                    refine ⟨3586891041706920702874541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2391260694471280468583027 3586891041706920702874541)
                    ·
                      refine ⟨1345084140640095263577953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3586891041706920702874541 1345084140640095263577953)
                      ·
                        rfl

theorem cell23_2619542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_2619542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619542 prefixEnd_2619542 := by exact prefixLift 2619542
  have htrace : WordTrace (prefixWord ++ tailWord_2619542) baseStart_2619542 baseEnd_2619542 := by
    simpa [prefixWord, tailWord_2619542, baseEnd_2619542] using wordTrace_append hprefix tailTrace_2619542
  have hstable : (prefixWord ++ tailWord_2619542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619542).length < 2 ^ (prefixWord ++ tailWord_2619542).sum := by decide
  have hdescent : baseEnd_2619542 < baseStart_2619542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619570 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2]
def baseStart_2619570 : Nat := 118140960795 + 2619570 * 2 ^ 59
def prefixEnd_2619570 : Nat := 4983230072969 + 3 ^ 40 * 2619570 * 2
def baseEnd_2619570 : Nat := 1345098518098421154027823

theorem tailTrace_2619570 : CollatzResearch.WordTrace tailWord_2619570 prefixEnd_2619570 1345098518098421154027823 := by
  unfold tailWord_2619570
  simp only [CollatzResearch.WordTrace]
  refine ⟨23885891779938187945704041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63695711413168501188544109 23885891779938187945704041)
  ·
    refine ⟨17914418834953640959278031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23885891779938187945704041 17914418834953640959278031)
    ·
      refine ⟨26871628252430461438917047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17914418834953640959278031 26871628252430461438917047)
      ·
        refine ⟨40307442378645692158375571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26871628252430461438917047 40307442378645692158375571)
        ·
          refine ⟨60461163567968538237563357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40307442378645692158375571 60461163567968538237563357)
          ·
            refine ⟨22672936337988201839086259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60461163567968538237563357 22672936337988201839086259)
            ·
              refine ⟨34009404506982302758629389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22672936337988201839086259 34009404506982302758629389)
              ·
                refine ⟨12753526690118363534486021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34009404506982302758629389 12753526690118363534486021)
                ·
                  refine ⟨2391286254397193162716129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12753526690118363534486021 2391286254397193162716129)
                  ·
                    refine ⟨1793464690797894872037097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2391286254397193162716129 1793464690797894872037097)
                    ·
                      refine ⟨1345098518098421154027823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1793464690797894872037097 1345098518098421154027823)
                      ·
                        rfl

theorem cell23_2619570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_2619570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619570 prefixEnd_2619570 := by exact prefixLift 2619570
  have htrace : WordTrace (prefixWord ++ tailWord_2619570) baseStart_2619570 baseEnd_2619570 := by
    simpa [prefixWord, tailWord_2619570, baseEnd_2619570] using wordTrace_append hprefix tailTrace_2619570
  have hstable : (prefixWord ++ tailWord_2619570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619570).length < 2 ^ (prefixWord ++ tailWord_2619570).sum := by decide
  have hdescent : baseEnd_2619570 < baseStart_2619570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619616 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 5]
def baseStart_2619616 : Nat := 118140960795 + 2619616 * 2 ^ 59
def prefixEnd_2619616 : Nat := 4983230072969 + 3 ^ 40 * 2619616 * 2
def baseEnd_2619616 : Nat := 1345122138208527974052611

theorem tailTrace_2619616 : CollatzResearch.WordTrace tailWord_2619616 prefixEnd_2619616 1345122138208527974052611 := by
  unfold tailWord_2619616
  simp only [CollatzResearch.WordTrace]
  refine ⟨47772622438793050819495351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63696829918390734425993801 47772622438793050819495351)
  ·
    refine ⟨71658933658189576229243027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47772622438793050819495351 71658933658189576229243027)
    ·
      refine ⟨107488400487284364343864541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71658933658189576229243027 107488400487284364343864541)
      ·
        refine ⟨40308150182731636628949203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107488400487284364343864541 40308150182731636628949203)
        ·
          refine ⟨60462225274097454943423805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40308150182731636628949203 60462225274097454943423805)
          ·
            refine ⟨22673334477786545603783927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60462225274097454943423805 22673334477786545603783927)
            ·
              refine ⟨34010001716679818405675891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22673334477786545603783927 34010001716679818405675891)
              ·
                refine ⟨51015002575019727608513837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34010001716679818405675891 51015002575019727608513837)
                ·
                  refine ⟨19130625965632397853192689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51015002575019727608513837 19130625965632397853192689)
                  ·
                    refine ⟨14347969474224298389894517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19130625965632397853192689 14347969474224298389894517)
                    ·
                      refine ⟨1345122138208527974052611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14347969474224298389894517 1345122138208527974052611)
                      ·
                        rfl

theorem cell23_2619616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_2619616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619616 prefixEnd_2619616 := by exact prefixLift 2619616
  have htrace : WordTrace (prefixWord ++ tailWord_2619616) baseStart_2619616 baseEnd_2619616 := by
    simpa [prefixWord, tailWord_2619616, baseEnd_2619616] using wordTrace_append hprefix tailTrace_2619616
  have hstable : (prefixWord ++ tailWord_2619616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619616).length < 2 ^ (prefixWord ++ tailWord_2619616).sum := by decide
  have hdescent : baseEnd_2619616 < baseStart_2619616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619696 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 2, 9]
def baseStart_2619696 : Nat := 118140960795 + 2619696 * 2 ^ 59
def prefixEnd_2619696 : Nat := 4983230072969 + 3 ^ 40 * 2619696 * 2
def baseEnd_2619696 : Nat := 448387738886962553684081

theorem tailTrace_2619696 : CollatzResearch.WordTrace tailWord_2619696 prefixEnd_2619696 448387738886962553684081 := by
  unfold tailWord_2619696
  simp only [CollatzResearch.WordTrace]
  refine ⟨47774081358648137650951471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63698775144864183534601961 47774081358648137650951471)
  ·
    refine ⟨71661122037972206476427207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47774081358648137650951471 71661122037972206476427207)
    ·
      refine ⟨107491683056958309714640811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71661122037972206476427207 107491683056958309714640811)
      ·
        refine ⟨161237524585437464571961217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107491683056958309714640811 161237524585437464571961217)
        ·
          refine ⟨120928143439078098428970913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161237524585437464571961217 120928143439078098428970913)
          ·
            refine ⟨90696107579308573821728185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120928143439078098428970913 90696107579308573821728185)
            ·
              refine ⟨68022080684481430366296139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90696107579308573821728185 68022080684481430366296139)
              ·
                refine ⟨102033121026722145549444209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68022080684481430366296139 102033121026722145549444209)
                ·
                  refine ⟨76524840770041609162083157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102033121026722145549444209 76524840770041609162083157)
                  ·
                    refine ⟨448387738886962553684081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 76524840770041609162083157 448387738886962553684081)
                    ·
                      rfl

theorem cell23_2619696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_2619696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619696 prefixEnd_2619696 := by exact prefixLift 2619696
  have htrace : WordTrace (prefixWord ++ tailWord_2619696) baseStart_2619696 baseEnd_2619696 := by
    simpa [prefixWord, tailWord_2619696, baseEnd_2619696] using wordTrace_append hprefix tailTrace_2619696
  have hstable : (prefixWord ++ tailWord_2619696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619696).length < 2 ^ (prefixWord ++ tailWord_2619696).sum := by decide
  have hdescent : baseEnd_2619696 < baseStart_2619696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619720 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 1, 5, 2]
def baseStart_2619720 : Nat := 118140960795 + 2619720 * 2 ^ 59
def prefixEnd_2619720 : Nat := 4983230072969 + 3 ^ 40 * 2619720 * 2
def baseEnd_2619720 : Nat := 1345175540196595567152133

theorem tailTrace_2619720 : CollatzResearch.WordTrace tailWord_2619720 prefixEnd_2619720 1345175540196595567152133 := by
  unfold tailWord_2619720
  simp only [CollatzResearch.WordTrace]
  refine ⟨47774519034604663700388307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63699358712806218267184409 47774519034604663700388307)
  ·
    refine ⟨71661778551906995550582461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47774519034604663700388307 71661778551906995550582461)
    ·
      refine ⟨26873166956965123331468423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71661778551906995550582461 26873166956965123331468423)
      ·
        refine ⟨40309750435447684997202635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26873166956965123331468423 40309750435447684997202635)
        ·
          refine ⟨60464625653171527495803953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40309750435447684997202635 60464625653171527495803953)
          ·
            refine ⟨45348469239878645621852965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60464625653171527495803953 45348469239878645621852965)
            ·
              refine ⟨8502837982477246054097431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45348469239878645621852965 8502837982477246054097431)
              ·
                refine ⟨12754256973715869081146147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8502837982477246054097431 12754256973715869081146147)
                ·
                  refine ⟨19131385460573803621719221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12754256973715869081146147 19131385460573803621719221)
                  ·
                    refine ⟨1793567386928794089536177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19131385460573803621719221 1793567386928794089536177)
                    ·
                      refine ⟨1345175540196595567152133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1793567386928794089536177 1345175540196595567152133)
                      ·
                        rfl

theorem cell23_2619720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_2619720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619720 prefixEnd_2619720 := by exact prefixLift 2619720
  have htrace : WordTrace (prefixWord ++ tailWord_2619720) baseStart_2619720 baseEnd_2619720 := by
    simpa [prefixWord, tailWord_2619720, baseEnd_2619720] using wordTrace_append hprefix tailTrace_2619720
  have hstable : (prefixWord ++ tailWord_2619720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619720).length < 2 ^ (prefixWord ++ tailWord_2619720).sum := by decide
  have hdescent : baseEnd_2619720 < baseStart_2619720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619727 : List Nat := [1, 1, 2, 1, 1, 2, 1, 9, 1, 1, 3]
def baseStart_2619727 : Nat := 118140960795 + 2619727 * 2 ^ 59
def prefixEnd_2619727 : Nat := 4983230072969 + 3 ^ 40 * 2619727 * 2
def baseEnd_2619727 : Nat := 1345179134561177039764601

theorem tailTrace_2619727 : CollatzResearch.WordTrace tailWord_2619727 prefixEnd_2619727 1345179134561177039764601 := by
  unfold tailWord_2619727
  simp only [CollatzResearch.WordTrace]
  refine ⟨95549293380183967596281435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63699528920122645064187623 95549293380183967596281435)
  ·
    refine ⟨143323940070275951394422153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95549293380183967596281435 143323940070275951394422153)
    ·
      refine ⟨107492955052706963545816615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143323940070275951394422153 107492955052706963545816615)
      ·
        refine ⟨161239432579060445318724923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107492955052706963545816615 161239432579060445318724923)
        ·
          refine ⟨241859148868590667978087385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161239432579060445318724923 241859148868590667978087385)
          ·
            refine ⟨181394361651443000983565539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241859148868590667978087385 181394361651443000983565539)
            ·
              refine ⟨272091542477164501475348309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181394361651443000983565539 272091542477164501475348309)
              ·
                refine ⟨1594286381702135750832119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 272091542477164501475348309 1594286381702135750832119)
                ·
                  refine ⟨2391429572553203626248179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594286381702135750832119 2391429572553203626248179)
                  ·
                    refine ⟨3587144358829805439372269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2391429572553203626248179 3587144358829805439372269)
                    ·
                      refine ⟨1345179134561177039764601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3587144358829805439372269 1345179134561177039764601)
                      ·
                        rfl

theorem cell23_2619727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 1, 1, 3].length) (baseStart_2619727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619727 prefixEnd_2619727 := by exact prefixLift 2619727
  have htrace : WordTrace (prefixWord ++ tailWord_2619727) baseStart_2619727 baseEnd_2619727 := by
    simpa [prefixWord, tailWord_2619727, baseEnd_2619727] using wordTrace_append hprefix tailTrace_2619727
  have hstable : (prefixWord ++ tailWord_2619727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619727).length < 2 ^ (prefixWord ++ tailWord_2619727).sum := by decide
  have hdescent : baseEnd_2619727 < baseStart_2619727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619730 : List Nat := [3, 2, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_2619730 : Nat := 118140960795 + 2619730 * 2 ^ 59
def prefixEnd_2619730 : Nat := 4983230072969 + 3 ^ 40 * 2619730 * 2
def baseEnd_2619730 : Nat := 448393558334380176009029

theorem tailTrace_2619730 : CollatzResearch.WordTrace tailWord_2619730 prefixEnd_2619730 448393558334380176009029 := by
  unfold tailWord_2619730
  simp only [CollatzResearch.WordTrace]
  refine ⟨23887350699793274777160161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63699601866115399405760429 23887350699793274777160161)
  ·
    refine ⟨17915513024844956082870121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23887350699793274777160161 17915513024844956082870121)
    ·
      refine ⟨13436634768633717062152591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17915513024844956082870121 13436634768633717062152591)
      ·
        refine ⟨20154952152950575593228887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13436634768633717062152591 20154952152950575593228887)
        ·
          refine ⟨30232428229425863389843331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20154952152950575593228887 30232428229425863389843331)
          ·
            refine ⟨45348642344138795084764997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30232428229425863389843331 45348642344138795084764997)
            ·
              refine ⟨8502870439526024078393437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45348642344138795084764997 8502870439526024078393437)
              ·
                refine ⟨3188576414822259029397539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8502870439526024078393437 3188576414822259029397539)
                ·
                  refine ⟨4782864622233388544096309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3188576414822259029397539 4782864622233388544096309)
                  ·
                    refine ⟨448393558334380176009029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4782864622233388544096309 448393558334380176009029)
                    ·
                      rfl

theorem cell23_2619730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_2619730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619730 prefixEnd_2619730 := by exact prefixLift 2619730
  have htrace : WordTrace (prefixWord ++ tailWord_2619730) baseStart_2619730 baseEnd_2619730 := by
    simpa [prefixWord, tailWord_2619730, baseEnd_2619730] using wordTrace_append hprefix tailTrace_2619730
  have hstable : (prefixWord ++ tailWord_2619730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619730).length < 2 ^ (prefixWord ++ tailWord_2619730).sum := by decide
  have hdescent : baseEnd_2619730 < baseStart_2619730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619744 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 3, 1, 3]
def baseStart_2619744 : Nat := 118140960795 + 2619744 * 2 ^ 59
def prefixEnd_2619744 : Nat := 4983230072969 + 3 ^ 40 * 2619744 * 2
def baseEnd_2619744 : Nat := 1345187863732303473252023

theorem tailTrace_2619744 : CollatzResearch.WordTrace tailWord_2619744 prefixEnd_2619744 1345187863732303473252023 := by
  unfold tailWord_2619744
  simp only [CollatzResearch.WordTrace]
  refine ⟨47774956710561189749825143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63699942280748252999766857 47774956710561189749825143)
  ·
    refine ⟨71662435065841784624737715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47774956710561189749825143 71662435065841784624737715)
    ·
      refine ⟨107493652598762676937106573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71662435065841784624737715 107493652598762676937106573)
      ·
        refine ⟨40310119724536003851414965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107493652598762676937106573 40310119724536003851414965)
        ·
          refine ⟨3779073724175250361070153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40310119724536003851414965 3779073724175250361070153)
          ·
            refine ⟨2834305293131437770802615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3779073724175250361070153 2834305293131437770802615)
            ·
              refine ⟨4251457939697156656203923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834305293131437770802615 4251457939697156656203923)
              ·
                refine ⟨6377186909545734984305885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4251457939697156656203923 6377186909545734984305885)
                ·
                  refine ⟨2391445091079650619114707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6377186909545734984305885 2391445091079650619114707)
                  ·
                    refine ⟨3587167636619475928672061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2391445091079650619114707 3587167636619475928672061)
                    ·
                      refine ⟨1345187863732303473252023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3587167636619475928672061 1345187863732303473252023)
                      ·
                        rfl

theorem cell23_2619744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_2619744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619744 prefixEnd_2619744 := by exact prefixLift 2619744
  have htrace : WordTrace (prefixWord ++ tailWord_2619744) baseStart_2619744 baseEnd_2619744 := by
    simpa [prefixWord, tailWord_2619744, baseEnd_2619744] using wordTrace_append hprefix tailTrace_2619744
  have hstable : (prefixWord ++ tailWord_2619744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619744).length < 2 ^ (prefixWord ++ tailWord_2619744).sum := by decide
  have hdescent : baseEnd_2619744 < baseStart_2619744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619753 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 5]
def baseStart_2619753 : Nat := 118140960795 + 2619753 * 2 ^ 59
def prefixEnd_2619753 : Nat := 4983230072969 + 3 ^ 40 * 2619753 * 2
def baseEnd_2619753 : Nat := 1345192485058193938039481

theorem tailTrace_2619753 : CollatzResearch.WordTrace tailWord_2619753 prefixEnd_2619753 1345192485058193938039481 := by
  unfold tailWord_2619753
  simp only [CollatzResearch.WordTrace]
  refine ⟨95550241678089774036727913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63700161118726516024485275 95550241678089774036727913)
  ·
    refine ⟨71662681258567330527545935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95550241678089774036727913 71662681258567330527545935)
    ·
      refine ⟨107494021887850995791318903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71662681258567330527545935 107494021887850995791318903)
      ·
        refine ⟨161241032831776493686978355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107494021887850995791318903 161241032831776493686978355)
        ·
          refine ⟨241861549247664740530467533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161241032831776493686978355 241861549247664740530467533)
          ·
            refine ⟨90698080967874277698925325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241861549247664740530467533 90698080967874277698925325)
            ·
              refine ⟨34011780362952854137096997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90698080967874277698925325 34011780362952854137096997)
              ·
                refine ⟨6377208818053660150705687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34011780362952854137096997 6377208818053660150705687)
                ·
                  refine ⟨9565813227080490226058531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6377208818053660150705687 9565813227080490226058531)
                  ·
                    refine ⟨14348719840620735339087797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9565813227080490226058531 14348719840620735339087797)
                    ·
                      refine ⟨1345192485058193938039481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14348719840620735339087797 1345192485058193938039481)
                      ·
                        rfl

theorem cell23_2619753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_2619753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619753 prefixEnd_2619753 := by exact prefixLift 2619753
  have htrace : WordTrace (prefixWord ++ tailWord_2619753) baseStart_2619753 baseEnd_2619753 := by
    simpa [prefixWord, tailWord_2619753, baseEnd_2619753] using wordTrace_append hprefix tailTrace_2619753
  have hstable : (prefixWord ++ tailWord_2619753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619753).length < 2 ^ (prefixWord ++ tailWord_2619753).sum := by decide
  have hdescent : baseEnd_2619753 < baseStart_2619753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619773 : List Nat := [1, 4, 1, 1, 2, 3, 2, 9]
def baseStart_2619773 : Nat := 118140960795 + 2619773 * 2 ^ 59
def prefixEnd_2619773 : Nat := 4983230072969 + 3 ^ 40 * 2619773 * 2
def baseEnd_2619773 : Nat := 49822324247084587399607

theorem tailTrace_2619773 : CollatzResearch.WordTrace tailWord_2619773 prefixEnd_2619773 49822324247084587399607 := by
  unfold tailWord_2619773
  simp only [CollatzResearch.WordTrace]
  refine ⟨95550971138017317452455973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63700647425344878301637315 95550971138017317452455973)
  ·
    refine ⟨17915807088378247022335495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95550971138017317452455973 17915807088378247022335495)
    ·
      refine ⟨26873710632567370533503243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17915807088378247022335495 26873710632567370533503243)
      ·
        refine ⟨40310565948851055800254865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26873710632567370533503243 40310565948851055800254865)
        ·
          refine ⟨30232924461638291850191149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40310565948851055800254865 30232924461638291850191149)
          ·
            refine ⟨11337346673114359443821681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30232924461638291850191149 11337346673114359443821681)
            ·
              refine ⟨8503010004835769582866261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11337346673114359443821681 8503010004835769582866261)
              ·
                refine ⟨49822324247084587399607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8503010004835769582866261 49822324247084587399607)
                ·
                  rfl

theorem cell23_2619773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 9].length) (baseStart_2619773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619773 prefixEnd_2619773 := by exact prefixLift 2619773
  have htrace : WordTrace (prefixWord ++ tailWord_2619773) baseStart_2619773 baseEnd_2619773 := by
    simpa [prefixWord, tailWord_2619773, baseEnd_2619773] using wordTrace_append hprefix tailTrace_2619773
  have hstable : (prefixWord ++ tailWord_2619773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619773).length < 2 ^ (prefixWord ++ tailWord_2619773).sum := by decide
  have hdescent : baseEnd_2619773 < baseStart_2619773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619780 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_2619780 : Nat := 118140960795 + 2619780 * 2 ^ 59
def prefixEnd_2619780 : Nat := 4983230072969 + 3 ^ 40 * 2619780 * 2
def baseEnd_2619780 : Nat := 1345206349035865332401857

theorem tailTrace_2619780 : CollatzResearch.WordTrace tailWord_2619780 prefixEnd_2619780 1345206349035865332401857 := by
  unfold tailWord_2619780
  simp only [CollatzResearch.WordTrace]
  refine ⟨47775613224495978823980397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63700817632661305098640529 47775613224495978823980397)
  ·
    refine ⟨17915854959185992058992649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47775613224495978823980397 17915854959185992058992649)
    ·
      refine ⟨13436891219389494044244487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17915854959185992058992649 13436891219389494044244487)
      ·
        refine ⟨20155336829084241066366731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13436891219389494044244487 20155336829084241066366731)
        ·
          refine ⟨30233005243626361599550097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20155336829084241066366731 30233005243626361599550097)
          ·
            refine ⟨22674753932719771199662573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30233005243626361599550097 22674753932719771199662573)
            ·
              refine ⟨8503032724769914199873465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22674753932719771199662573 8503032724769914199873465)
              ·
                refine ⟨6377274543577435649905099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8503032724769914199873465 6377274543577435649905099)
                ·
                  refine ⟨9565911815366153474857649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6377274543577435649905099 9565911815366153474857649)
                  ·
                    refine ⟨7174433861524615106143237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9565911815366153474857649 7174433861524615106143237)
                    ·
                      refine ⟨1345206349035865332401857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7174433861524615106143237 1345206349035865332401857)
                      ·
                        rfl

theorem cell23_2619780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_2619780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619780 prefixEnd_2619780 := by exact prefixLift 2619780
  have htrace : WordTrace (prefixWord ++ tailWord_2619780) baseStart_2619780 baseEnd_2619780 := by
    simpa [prefixWord, tailWord_2619780, baseEnd_2619780] using wordTrace_append hprefix tailTrace_2619780
  have hstable : (prefixWord ++ tailWord_2619780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619780).length < 2 ^ (prefixWord ++ tailWord_2619780).sum := by decide
  have hdescent : baseEnd_2619780 < baseStart_2619780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619843 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 5]
def baseStart_2619843 : Nat := 118140960795 + 2619843 * 2 ^ 59
def prefixEnd_2619843 : Nat := 4983230072969 + 3 ^ 40 * 2619843 * 2
def baseEnd_2619843 : Nat := 1345238698317098585914067

theorem tailTrace_2619843 : CollatzResearch.WordTrace tailWord_2619843 prefixEnd_2619843 1345238698317098585914067 := by
  unfold tailWord_2619843
  simp only [CollatzResearch.WordTrace]
  refine ⟨95553524247763719407504183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63702349498509146271669455 95553524247763719407504183)
  ·
    refine ⟨143330286371645579111256275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95553524247763719407504183 143330286371645579111256275)
    ·
      refine ⟨214995429557468368666884413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143330286371645579111256275 214995429557468368666884413)
      ·
        refine ⟨80623286084050638250081655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214995429557468368666884413 80623286084050638250081655)
        ·
          refine ⟨120934929126075957375122483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80623286084050638250081655 120934929126075957375122483)
          ·
            refine ⟨181402393689113936062683725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120934929126075957375122483 181402393689113936062683725)
            ·
              refine ⟨68025897633417726023506397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181402393689113936062683725 68025897633417726023506397)
              ·
                refine ⟨25509711612531647258814899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68025897633417726023506397 25509711612531647258814899)
                ·
                  refine ⟨38264567418797470888222349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25509711612531647258814899 38264567418797470888222349)
                  ·
                    refine ⟨14349212782049051583083381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38264567418797470888222349 14349212782049051583083381)
                    ·
                      refine ⟨1345238698317098585914067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14349212782049051583083381 1345238698317098585914067)
                      ·
                        rfl

theorem cell23_2619843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_2619843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619843 prefixEnd_2619843 := by exact prefixLift 2619843
  have htrace : WordTrace (prefixWord ++ tailWord_2619843) baseStart_2619843 baseEnd_2619843 := by
    simpa [prefixWord, tailWord_2619843, baseEnd_2619843] using wordTrace_append hprefix tailTrace_2619843
  have hstable : (prefixWord ++ tailWord_2619843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619843).length < 2 ^ (prefixWord ++ tailWord_2619843).sum := by decide
  have hdescent : baseEnd_2619843 < baseStart_2619843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619880 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 7]
def baseStart_2619880 : Nat := 118140960795 + 2619880 * 2 ^ 59
def prefixEnd_2619880 : Nat := 4983230072969 + 3 ^ 40 * 2619880 * 2
def baseEnd_2619880 : Nat := 149473077455701660127933

theorem tailTrace_2619880 : CollatzResearch.WordTrace tailWord_2619880 prefixEnd_2619880 149473077455701660127933 := by
  unfold tailWord_2619880
  simp only [CollatzResearch.WordTrace]
  refine ⟨47777436874314837363300547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63703249165753116484400729 47777436874314837363300547)
  ·
    refine ⟨71666155311472256044950821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47777436874314837363300547 71666155311472256044950821)
    ·
      refine ⟨13437404120901048008428279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71666155311472256044950821 13437404120901048008428279)
      ·
        refine ⟨20156106181351572012642419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13437404120901048008428279 20156106181351572012642419)
        ·
          refine ⟨30234159272027358018963629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20156106181351572012642419 30234159272027358018963629)
          ·
            refine ⟨11337809727010259257111361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30234159272027358018963629 11337809727010259257111361)
            ·
              refine ⟨8503357295257694442833521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11337809727010259257111361 8503357295257694442833521)
              ·
                refine ⟨6377517971443270832125141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8503357295257694442833521 6377517971443270832125141)
                ·
                  refine ⟨149473077455701660127933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6377517971443270832125141 149473077455701660127933)
                  ·
                    rfl

theorem cell23_2619880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 7].length) (baseStart_2619880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619880 prefixEnd_2619880 := by exact prefixLift 2619880
  have htrace : WordTrace (prefixWord ++ tailWord_2619880) baseStart_2619880 baseEnd_2619880 := by
    simpa [prefixWord, tailWord_2619880, baseEnd_2619880] using wordTrace_append hprefix tailTrace_2619880
  have hstable : (prefixWord ++ tailWord_2619880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619880).length < 2 ^ (prefixWord ++ tailWord_2619880).sum := by decide
  have hdescent : baseEnd_2619880 < baseStart_2619880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619897 : List Nat := [1, 2, 1, 3, 1, 2, 5, 3, 5]
def baseStart_2619897 : Nat := 118140960795 + 2619897 * 2 ^ 59
def prefixEnd_2619897 : Nat := 4983230072969 + 3 ^ 40 * 2619897 * 2
def baseEnd_2619897 : Nat := 149474047363604597182091

theorem tailTrace_2619897 : CollatzResearch.WordTrace tailWord_2619897 prefixEnd_2619897 149474047363604597182091 := by
  unfold tailWord_2619897
  simp only [CollatzResearch.WordTrace]
  refine ⟨95555493789568086629969945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63703662526378724419979963 95555493789568086629969945)
  ·
    refine ⟨71666620342176064972477459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95555493789568086629969945 71666620342176064972477459)
    ·
      refine ⟨107499930513264097458716189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71666620342176064972477459 107499930513264097458716189)
      ·
        refine ⟨40312473942474036547018571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107499930513264097458716189 40312473942474036547018571)
        ·
          refine ⟨60468710913711054820527857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40312473942474036547018571 60468710913711054820527857)
          ·
            refine ⟨45351533185283291115395893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60468710913711054820527857 45351533185283291115395893)
            ·
              refine ⟨4251706236120308542068365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45351533185283291115395893 4251706236120308542068365)
              ·
                refine ⟨1594389838545115703275637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4251706236120308542068365 1594389838545115703275637)
                ·
                  refine ⟨149474047363604597182091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1594389838545115703275637 149474047363604597182091)
                  ·
                    rfl

theorem cell23_2619897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 5].length) (baseStart_2619897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619897 prefixEnd_2619897 := by exact prefixLift 2619897
  have htrace : WordTrace (prefixWord ++ tailWord_2619897) baseStart_2619897 baseEnd_2619897 := by
    simpa [prefixWord, tailWord_2619897, baseEnd_2619897] using wordTrace_append hprefix tailTrace_2619897
  have hstable : (prefixWord ++ tailWord_2619897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619897).length < 2 ^ (prefixWord ++ tailWord_2619897).sum := by decide
  have hdescent : baseEnd_2619897 < baseStart_2619897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619914 : List Nat := [3, 1, 2, 2, 2, 1, 5, 2, 5]
def baseStart_2619914 : Nat := 118140960795 + 2619914 * 2 ^ 59
def prefixEnd_2619914 : Nat := 4983230072969 + 3 ^ 40 * 2619914 * 2
def baseEnd_2619914 : Nat := 149475017271507534236249

theorem tailTrace_2619914 : CollatzResearch.WordTrace tailWord_2619914 prefixEnd_2619914 149475017271507534236249 := by
  unfold tailWord_2619914
  simp only [CollatzResearch.WordTrace]
  refine ⟨23889028457626624633334699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63704075887004332355559197 23889028457626624633334699)
  ·
    refine ⟨35833542686439936950002049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23889028457626624633334699 35833542686439936950002049)
    ·
      refine ⟨26875157014829952712501537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35833542686439936950002049 26875157014829952712501537)
      ·
        refine ⟨20156367761122464534376153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26875157014829952712501537 20156367761122464534376153)
        ·
          refine ⟨15117275820841848400782115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20156367761122464534376153 15117275820841848400782115)
          ·
            refine ⟨22675913731262772601173173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15117275820841848400782115 22675913731262772601173173)
            ·
              refine ⟨2125866912305884931359985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22675913731262772601173173 2125866912305884931359985)
              ·
                refine ⟨1594400184229413698519989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2125866912305884931359985 1594400184229413698519989)
                ·
                  refine ⟨149475017271507534236249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1594400184229413698519989 149475017271507534236249)
                  ·
                    rfl

theorem cell23_2619914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 5].length) (baseStart_2619914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619914 prefixEnd_2619914 := by exact prefixLift 2619914
  have htrace : WordTrace (prefixWord ++ tailWord_2619914) baseStart_2619914 baseEnd_2619914 := by
    simpa [prefixWord, tailWord_2619914, baseEnd_2619914] using wordTrace_append hprefix tailTrace_2619914
  have hstable : (prefixWord ++ tailWord_2619914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619914).length < 2 ^ (prefixWord ++ tailWord_2619914).sum := by decide
  have hdescent : baseEnd_2619914 < baseStart_2619914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619930 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_2619930 : Nat := 118140960795 + 2619930 * 2 ^ 59
def prefixEnd_2619930 : Nat := 4983230072969 + 3 ^ 40 * 2619930 * 2
def baseEnd_2619930 : Nat := 1345283371134039745526167

theorem tailTrace_2619930 : CollatzResearch.WordTrace tailWord_2619930 prefixEnd_2619930 1345283371134039745526167 := by
  unfold tailWord_2619930
  simp only [CollatzResearch.WordTrace]
  refine ⟨23889174349612133316480311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63704464932299022177280829 23889174349612133316480311)
  ·
    refine ⟨35833761524418199974720467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23889174349612133316480311 35833761524418199974720467)
    ·
      refine ⟨53750642286627299962080701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35833761524418199974720467 53750642286627299962080701)
      ·
        refine ⟨20156490857485237485780263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53750642286627299962080701 20156490857485237485780263)
        ·
          refine ⟨30234736286227856228670395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20156490857485237485780263 30234736286227856228670395)
          ·
            refine ⟨45352104429341784343005593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30234736286227856228670395 45352104429341784343005593)
            ·
              refine ⟨34014078322006338257254195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45352104429341784343005593 34014078322006338257254195)
              ·
                refine ⟨51021117483009507385881293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34014078322006338257254195 51021117483009507385881293)
                ·
                  refine ⟨19132919056128565269705485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51021117483009507385881293 19132919056128565269705485)
                  ·
                    refine ⟨7174844646048211976139557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19132919056128565269705485 7174844646048211976139557)
                    ·
                      refine ⟨1345283371134039745526167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7174844646048211976139557 1345283371134039745526167)
                      ·
                        rfl

theorem cell23_2619930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_2619930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619930 prefixEnd_2619930 := by exact prefixLift 2619930
  have htrace : WordTrace (prefixWord ++ tailWord_2619930) baseStart_2619930 baseEnd_2619930 := by
    simpa [prefixWord, tailWord_2619930, baseEnd_2619930] using wordTrace_append hprefix tailTrace_2619930
  have hstable : (prefixWord ++ tailWord_2619930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619930).length < 2 ^ (prefixWord ++ tailWord_2619930).sum := by decide
  have hdescent : baseEnd_2619930 < baseStart_2619930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619944 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 2, 5]
def baseStart_2619944 : Nat := 118140960795 + 2619944 * 2 ^ 59
def prefixEnd_2619944 : Nat := 4983230072969 + 3 ^ 40 * 2619944 * 2
def baseEnd_2619944 : Nat := 448430186621067563583701

theorem tailTrace_2619944 : CollatzResearch.WordTrace tailWord_2619944 prefixEnd_2619944 448430186621067563583701 := by
  unfold tailWord_2619944
  simp only [CollatzResearch.WordTrace]
  refine ⟨47778604010198906828465443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63704805346931875771287257 47778604010198906828465443)
  ·
    refine ⟨71667906015298360242698165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47778604010198906828465443 71667906015298360242698165)
    ·
      refine ⟨6718866188934221272752953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71667906015298360242698165 6718866188934221272752953)
      ·
        refine ⟨5039149641700665954564715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6718866188934221272752953 5039149641700665954564715)
        ·
          refine ⟨7558724462550998931847073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5039149641700665954564715 7558724462550998931847073)
          ·
            refine ⟨5669043346913249198885305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7558724462550998931847073 5669043346913249198885305)
            ·
              refine ⟨4251782510184936899163979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5669043346913249198885305 4251782510184936899163979)
              ·
                refine ⟨6377673765277405348745969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4251782510184936899163979 6377673765277405348745969)
                ·
                  refine ⟨4783255323958054011559477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6377673765277405348745969 4783255323958054011559477)
                  ·
                    refine ⟨448430186621067563583701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4783255323958054011559477 448430186621067563583701)
                    ·
                      rfl

theorem cell23_2619944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_2619944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619944 prefixEnd_2619944 := by exact prefixLift 2619944
  have htrace : WordTrace (prefixWord ++ tailWord_2619944) baseStart_2619944 baseEnd_2619944 := by
    simpa [prefixWord, tailWord_2619944, baseEnd_2619944] using wordTrace_append hprefix tailTrace_2619944
  have hstable : (prefixWord ++ tailWord_2619944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619944).length < 2 ^ (prefixWord ++ tailWord_2619944).sum := by decide
  have hdescent : baseEnd_2619944 < baseStart_2619944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619960 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_2619960 : Nat := 118140960795 + 2619960 * 2 ^ 59
def prefixEnd_2619960 : Nat := 4983230072969 + 3 ^ 40 * 2619960 * 2
def baseEnd_2619960 : Nat := 1345298775553674628151029

theorem tailTrace_2619960 : CollatzResearch.WordTrace tailWord_2619960 prefixEnd_2619960 1345298775553674628151029 := by
  unfold tailWord_2619960
  simp only [CollatzResearch.WordTrace]
  refine ⟨47778895794169924194756667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63705194392226565593008889 47778895794169924194756667)
  ·
    refine ⟨71668343691254886292135001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47778895794169924194756667 71668343691254886292135001)
    ·
      refine ⟨53751257768441164719101251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71668343691254886292135001 53751257768441164719101251)
      ·
        refine ⟨80626886652661747078651877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53751257768441164719101251 80626886652661747078651877)
        ·
          refine ⟨15117541247374077577247227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80626886652661747078651877 15117541247374077577247227)
          ·
            refine ⟨22676311871061116365870841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15117541247374077577247227 22676311871061116365870841)
            ·
              refine ⟨17007233903295837274403131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22676311871061116365870841 17007233903295837274403131)
              ·
                refine ⟨25510850854943755911604697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17007233903295837274403131 25510850854943755911604697)
                ·
                  refine ⟨19133138141207816933703523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25510850854943755911604697 19133138141207816933703523)
                  ·
                    refine ⟨28699707211811725400555285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19133138141207816933703523 28699707211811725400555285)
                    ·
                      refine ⟨1345298775553674628151029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28699707211811725400555285 1345298775553674628151029)
                      ·
                        rfl

theorem cell23_2619960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_2619960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619960 prefixEnd_2619960 := by exact prefixLift 2619960
  have htrace : WordTrace (prefixWord ++ tailWord_2619960) baseStart_2619960 baseEnd_2619960 := by
    simpa [prefixWord, tailWord_2619960, baseEnd_2619960] using wordTrace_append hprefix tailTrace_2619960
  have hstable : (prefixWord ++ tailWord_2619960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619960).length < 2 ^ (prefixWord ++ tailWord_2619960).sum := by decide
  have hdescent : baseEnd_2619960 < baseStart_2619960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619967 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 3]
def baseStart_2619967 : Nat := 118140960795 + 2619967 * 2 ^ 59
def prefixEnd_2619967 : Nat := 4983230072969 + 3 ^ 40 * 2619967 * 2
def baseEnd_2619967 : Nat := 1345302369918256100763497

theorem tailTrace_2619967 : CollatzResearch.WordTrace tailWord_2619967 prefixEnd_2619967 1345302369918256100763497 := by
  unfold tailWord_2619967
  simp only [CollatzResearch.WordTrace]
  refine ⟨95558046899314488585018155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63705364599542992390012103 95558046899314488585018155)
  ·
    refine ⟨143337070348971732877527233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95558046899314488585018155 143337070348971732877527233)
    ·
      refine ⟨107502802761728799658145425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143337070348971732877527233 107502802761728799658145425)
      ·
        refine ⟨80627102071296599743609069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107502802761728799658145425 80627102071296599743609069)
        ·
          refine ⟨30235163276736224903853401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80627102071296599743609069 30235163276736224903853401)
          ·
            refine ⟨22676372457552168677890051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30235163276736224903853401 22676372457552168677890051)
            ·
              refine ⟨34014558686328253016835077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22676372457552168677890051 34014558686328253016835077)
              ·
                refine ⟨6377729753686547440656577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34014558686328253016835077 6377729753686547440656577)
                ·
                  refine ⟨4783297315264910580492433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6377729753686547440656577 4783297315264910580492433)
                  ·
                    refine ⟨3587472986448682935369325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4783297315264910580492433 3587472986448682935369325)
                    ·
                      refine ⟨1345302369918256100763497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3587472986448682935369325 1345302369918256100763497)
                      ·
                        rfl

theorem cell23_2619967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_2619967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619967 prefixEnd_2619967 := by exact prefixLift 2619967
  have htrace : WordTrace (prefixWord ++ tailWord_2619967) baseStart_2619967 baseEnd_2619967 := by
    simpa [prefixWord, tailWord_2619967, baseEnd_2619967] using wordTrace_append hprefix tailTrace_2619967
  have hstable : (prefixWord ++ tailWord_2619967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619967).length < 2 ^ (prefixWord ++ tailWord_2619967).sum := by decide
  have hdescent : baseEnd_2619967 < baseStart_2619967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619981 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_2619981 : Nat := 118140960795 + 2619981 * 2 ^ 59
def prefixEnd_2619981 : Nat := 4983230072969 + 3 ^ 40 * 2619981 * 2
def baseEnd_2619981 : Nat := 1345309558647419045988433

theorem tailTrace_2619981 : CollatzResearch.WordTrace tailWord_2619981 prefixEnd_2619981 1345309558647419045988433 := by
  unfold tailWord_2619981
  simp only [CollatzResearch.WordTrace]
  refine ⟨95558557521263768976027797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63705705014175845984018531 95558557521263768976027797)
  ·
    refine ⟨4479307383809239170751303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95558557521263768976027797 4479307383809239170751303)
    ·
      refine ⟨6718961075713858756126955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4479307383809239170751303 6718961075713858756126955)
      ·
        refine ⟨10078441613570788134190433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6718961075713858756126955 10078441613570788134190433)
        ·
          refine ⟨7558831210178091100642825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10078441613570788134190433 7558831210178091100642825)
          ·
            refine ⟨5669123407633568325482119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7558831210178091100642825 5669123407633568325482119)
            ·
              refine ⟨8503685111450352488223179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5669123407633568325482119 8503685111450352488223179)
              ·
                refine ⟨12755527667175528732334769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8503685111450352488223179 12755527667175528732334769)
                ·
                  refine ⟨9566645750381646549251077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12755527667175528732334769 9566645750381646549251077)
                  ·
                    refine ⟨1793746078196558727984577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9566645750381646549251077 1793746078196558727984577)
                    ·
                      refine ⟨1345309558647419045988433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1793746078196558727984577 1345309558647419045988433)
                      ·
                        rfl

theorem cell23_2619981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_2619981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619981 prefixEnd_2619981 := by exact prefixLift 2619981
  have htrace : WordTrace (prefixWord ++ tailWord_2619981) baseStart_2619981 baseEnd_2619981 := by
    simpa [prefixWord, tailWord_2619981, baseEnd_2619981] using wordTrace_append hprefix tailTrace_2619981
  have hstable : (prefixWord ++ tailWord_2619981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619981).length < 2 ^ (prefixWord ++ tailWord_2619981).sum := by decide
  have hdescent : baseEnd_2619981 < baseStart_2619981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619998 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2619998 : Nat := 118140960795 + 2619998 * 2 ^ 59
def prefixEnd_2619998 : Nat := 4983230072969 + 3 ^ 40 * 2619998 * 2
def baseEnd_2619998 : Nat := 1345318287818545479475855

theorem tailTrace_2619998 : CollatzResearch.WordTrace tailWord_2619998 prefixEnd_2619998 1345318287818545479475855 := by
  unfold tailWord_2619998
  simp only [CollatzResearch.WordTrace]
  refine ⟨11944897195275272609924581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63706118374801453919597765 11944897195275272609924581)
  ·
    refine ⟨2239668224114113614360859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11944897195275272609924581 2239668224114113614360859)
    ·
      refine ⟨3359502336171170421541289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2239668224114113614360859 3359502336171170421541289)
      ·
        refine ⟨2519626752128377816155967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3359502336171170421541289 2519626752128377816155967)
        ·
          refine ⟨3779440128192566724233951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2519626752128377816155967 3779440128192566724233951)
          ·
            refine ⟨5669160192288850086350927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3779440128192566724233951 5669160192288850086350927)
            ·
              refine ⟨8503740288433275129526391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5669160192288850086350927 8503740288433275129526391)
              ·
                refine ⟨12755610432649912694289587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8503740288433275129526391 12755610432649912694289587)
                ·
                  refine ⟨19133415648974869041434381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12755610432649912694289587 19133415648974869041434381)
                  ·
                    refine ⟨7175030868365575890537893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19133415648974869041434381 7175030868365575890537893)
                    ·
                      refine ⟨1345318287818545479475855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7175030868365575890537893 1345318287818545479475855)
                      ·
                        rfl

theorem cell23_2619998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2619998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2619998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2619998 prefixEnd_2619998 := by exact prefixLift 2619998
  have htrace : WordTrace (prefixWord ++ tailWord_2619998) baseStart_2619998 baseEnd_2619998 := by
    simpa [prefixWord, tailWord_2619998, baseEnd_2619998] using wordTrace_append hprefix tailTrace_2619998
  have hstable : (prefixWord ++ tailWord_2619998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619998).length < 2 ^ (prefixWord ++ tailWord_2619998).sum := by decide
  have hdescent : baseEnd_2619998 < baseStart_2619998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620008 : List Nat := [2, 1, 4, 3, 2, 1, 2, 3, 1, 4]
def baseStart_2620008 : Nat := 118140960795 + 2620008 * 2 ^ 59
def prefixEnd_2620008 : Nat := 4983230072969 + 3 ^ 40 * 2620008 * 2
def baseEnd_2620008 : Nat := 448441140875030146783603

theorem tailTrace_2620008 : CollatzResearch.WordTrace tailWord_2620008 prefixEnd_2620008 448441140875030146783603 := by
  unfold tailWord_2620008
  simp only [CollatzResearch.WordTrace]
  refine ⟨47779771146082976293630339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63706361528110635058173785 47779771146082976293630339)
  ·
    refine ⟨71669656719124464440445509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47779771146082976293630339 71669656719124464440445509)
    ·
      refine ⟨13438060634835837082583533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71669656719124464440445509 13438060634835837082583533)
      ·
        refine ⟨5039272738063438905968825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13438060634835837082583533 5039272738063438905968825)
        ·
          refine ⟨3779454553547579179476619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5039272738063438905968825 3779454553547579179476619)
          ·
            refine ⟨5669181830321368769214929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3779454553547579179476619 5669181830321368769214929)
            ·
              refine ⟨4251886372741026576911197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5669181830321368769214929 4251886372741026576911197)
              ·
                refine ⟨1594457389777884966341699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4251886372741026576911197 1594457389777884966341699)
                ·
                  refine ⟨2391686084666827449512549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594457389777884966341699 2391686084666827449512549)
                  ·
                    refine ⟨448441140875030146783603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2391686084666827449512549 448441140875030146783603)
                    ·
                      rfl

theorem cell23_2620008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_2620008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620008 prefixEnd_2620008 := by exact prefixLift 2620008
  have htrace : WordTrace (prefixWord ++ tailWord_2620008) baseStart_2620008 baseEnd_2620008 := by
    simpa [prefixWord, tailWord_2620008, baseEnd_2620008] using wordTrace_append hprefix tailTrace_2620008
  have hstable : (prefixWord ++ tailWord_2620008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620008).length < 2 ^ (prefixWord ++ tailWord_2620008).sum := by decide
  have hdescent : baseEnd_2620008 < baseStart_2620008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620021 : List Nat := [1, 3, 4, 2, 2, 2, 1, 2, 6]
def baseStart_2620021 : Nat := 118140960795 + 2620021 * 2 ^ 59
def prefixEnd_2620021 : Nat := 4983230072969 + 3 ^ 40 * 2620021 * 2
def baseEnd_2620021 : Nat := 149481121985955432165361

theorem tailTrace_2620021 : CollatzResearch.WordTrace tailWord_2620021 prefixEnd_2620021 149481121985955432165361 := by
  unfold tailWord_2620021
  simp only [CollatzResearch.WordTrace]
  refine ⟨95560016441118855807483917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63706677627412570538322611 95560016441118855807483917)
  ·
    refine ⟨35835006165419570927806469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95560016441118855807483917 35835006165419570927806469)
    ·
      refine ⟨6719063656016169548963713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35835006165419570927806469 6719063656016169548963713)
      ·
        refine ⟨5039297742012127161722785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6719063656016169548963713 5039297742012127161722785)
        ·
          refine ⟨3779473306509095371292089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5039297742012127161722785 3779473306509095371292089)
          ·
            refine ⟨2834604979881821528469067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3779473306509095371292089 2834604979881821528469067)
            ·
              refine ⟨4251907469822732292703601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834604979881821528469067 4251907469822732292703601)
              ·
                refine ⟨3188930602367049219527701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4251907469822732292703601 3188930602367049219527701)
                ·
                  refine ⟨149481121985955432165361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3188930602367049219527701 149481121985955432165361)
                  ·
                    rfl

theorem cell23_2620021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_2620021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620021 prefixEnd_2620021 := by exact prefixLift 2620021
  have htrace : WordTrace (prefixWord ++ tailWord_2620021) baseStart_2620021 baseEnd_2620021 := by
    simpa [prefixWord, tailWord_2620021, baseEnd_2620021] using wordTrace_append hprefix tailTrace_2620021
  have hstable : (prefixWord ++ tailWord_2620021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620021).length < 2 ^ (prefixWord ++ tailWord_2620021).sum := by decide
  have hdescent : baseEnd_2620021 < baseStart_2620021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620065 : List Nat := [1, 2, 3, 3, 3, 2, 1, 3, 1, 1, 3]
def baseStart_2620065 : Nat := 118140960795 + 2620065 * 2 ^ 59
def prefixEnd_2620065 : Nat := 4983230072969 + 3 ^ 40 * 2620065 * 2
def baseEnd_2620065 : Nat := 1345352691022396717338047

theorem tailTrace_2620065 : CollatzResearch.WordTrace tailWord_2620065 prefixEnd_2620065 1345352691022396717338047 := by
  unfold tailWord_2620065
  simp only [CollatzResearch.WordTrace]
  refine ⟨95561621252959451322085649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63707747501972967548057099 95561621252959451322085649)
  ·
    refine ⟨71671215939719588491564237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95561621252959451322085649 71671215939719588491564237)
    ·
      refine ⟨26876705977394845684336589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71671215939719588491564237 26876705977394845684336589)
      ·
        refine ⟨10078764741523067131626221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26876705977394845684336589 10078764741523067131626221)
        ·
          refine ⟨3779536778071150174359833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10078764741523067131626221 3779536778071150174359833)
          ·
            refine ⟨2834652583553362630769875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3779536778071150174359833 2834652583553362630769875)
            ·
              refine ⟨4251978875330043946154813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834652583553362630769875 4251978875330043946154813)
              ·
                refine ⟨1594492078248766479808055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4251978875330043946154813 1594492078248766479808055)
                ·
                  refine ⟨2391738117373149719712083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594492078248766479808055 2391738117373149719712083)
                  ·
                    refine ⟨3587607176059724579568125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2391738117373149719712083 3587607176059724579568125)
                    ·
                      refine ⟨1345352691022396717338047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3587607176059724579568125 1345352691022396717338047)
                      ·
                        rfl

theorem cell23_2620065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_2620065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620065 prefixEnd_2620065 := by exact prefixLift 2620065
  have htrace : WordTrace (prefixWord ++ tailWord_2620065) baseStart_2620065 baseEnd_2620065 := by
    simpa [prefixWord, tailWord_2620065, baseEnd_2620065] using wordTrace_append hprefix tailTrace_2620065
  have hstable : (prefixWord ++ tailWord_2620065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620065).length < 2 ^ (prefixWord ++ tailWord_2620065).sum := by decide
  have hdescent : baseEnd_2620065 < baseStart_2620065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620077 : List Nat := [1, 5, 2, 1, 1, 2, 11]
def baseStart_2620077 : Nat := 118140960795 + 2620077 * 2 ^ 59
def prefixEnd_2620077 : Nat := 4983230072969 + 3 ^ 40 * 2620077 * 2
def baseEnd_2620077 : Nat := 16609368552966057659111

theorem tailTrace_2620077 : CollatzResearch.WordTrace tailWord_2620077 prefixEnd_2620077 16609368552966057659111 := by
  unfold tailWord_2620077
  simp only [CollatzResearch.WordTrace]
  refine ⟨95562058928915977371522485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63708039285943984914348323 95562058928915977371522485)
  ·
    refine ⟨8958943024585872878580233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95562058928915977371522485 8958943024585872878580233)
    ·
      refine ⟨6719207268439404658935175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8958943024585872878580233 6719207268439404658935175)
      ·
        refine ⟨10078810902659106988402763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6719207268439404658935175 10078810902659106988402763)
        ·
          refine ⟨15118216353988660482604145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10078810902659106988402763 15118216353988660482604145)
          ·
            refine ⟨11338662265491495361953109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15118216353988660482604145 11338662265491495361953109)
            ·
              refine ⟨16609368552966057659111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11338662265491495361953109 16609368552966057659111)
              ·
                rfl

theorem cell23_2620077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 11].length) (baseStart_2620077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620077 prefixEnd_2620077 := by exact prefixLift 2620077
  have htrace : WordTrace (prefixWord ++ tailWord_2620077) baseStart_2620077 baseEnd_2620077 := by
    simpa [prefixWord, tailWord_2620077, baseEnd_2620077] using wordTrace_append hprefix tailTrace_2620077
  have hstable : (prefixWord ++ tailWord_2620077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620077).length < 2 ^ (prefixWord ++ tailWord_2620077).sum := by decide
  have hdescent : baseEnd_2620077 < baseStart_2620077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620102 : List Nat := [6, 1, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_2620102 : Nat := 118140960795 + 2620102 * 2 ^ 59
def prefixEnd_2620102 : Nat := 4983230072969 + 3 ^ 40 * 2620102 * 2
def baseEnd_2620102 : Nat := 448457229935537690858459

theorem tailTrace_2620102 : CollatzResearch.WordTrace tailWord_2620102 prefixEnd_2620102 448457229935537690858459 := by
  unfold tailWord_2620102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2986342836057043957536955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63708647169216937760788373 2986342836057043957536955)
  ·
    refine ⟨4479514254085565936305433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2986342836057043957536955 4479514254085565936305433)
    ·
      refine ⟨3359635690564174452229075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4479514254085565936305433 3359635690564174452229075)
      ·
        refine ⟨5039453535846261678343613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3359635690564174452229075 5039453535846261678343613)
        ·
          refine ⟨1889795075942348129378855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5039453535846261678343613 1889795075942348129378855)
          ·
            refine ⟨2834692613913522194068283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889795075942348129378855 2834692613913522194068283)
            ·
              refine ⟨4252038920870283291102425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834692613913522194068283 4252038920870283291102425)
              ·
                refine ⟨3189029190652712468326819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4252038920870283291102425 3189029190652712468326819)
                ·
                  refine ⟨4783543785979068702490229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189029190652712468326819 4783543785979068702490229)
                  ·
                    refine ⟨448457229935537690858459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4783543785979068702490229 448457229935537690858459)
                    ·
                      rfl

theorem cell23_2620102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_2620102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620102 prefixEnd_2620102 := by exact prefixLift 2620102
  have htrace : WordTrace (prefixWord ++ tailWord_2620102) baseStart_2620102 baseEnd_2620102 := by
    simpa [prefixWord, tailWord_2620102, baseEnd_2620102] using wordTrace_append hprefix tailTrace_2620102
  have hstable : (prefixWord ++ tailWord_2620102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620102).length < 2 ^ (prefixWord ++ tailWord_2620102).sum := by decide
  have hdescent : baseEnd_2620102 < baseStart_2620102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620108 : List Nat := [2, 2, 1, 5, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2620108 : Nat := 118140960795 + 2620108 * 2 ^ 59
def prefixEnd_2620108 : Nat := 4983230072969 + 3 ^ 40 * 2620108 * 2
def baseEnd_2620108 : Nat := 1345374770690540049100349

theorem tailTrace_2620108 : CollatzResearch.WordTrace tailWord_2620108 prefixEnd_2620108 1345374770690540049100349 := by
  unfold tailWord_2620108
  simp only [CollatzResearch.WordTrace]
  refine ⟨47781594795901834832950489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63708793061202446443933985 47781594795901834832950489)
  ·
    refine ⟨35836196096926376124712867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47781594795901834832950489 35836196096926376124712867)
    ·
      refine ⟨53754294145389564187069301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35836196096926376124712867 53754294145389564187069301)
      ·
        refine ⟨5039465076130271642537747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53754294145389564187069301 5039465076130271642537747)
        ·
          refine ⟨7559197614195407463806621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5039465076130271642537747 7559197614195407463806621)
          ·
            refine ⟨2834699105323277798927483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7559197614195407463806621 2834699105323277798927483)
            ·
              refine ⟨4252048657984916698391225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834699105323277798927483 4252048657984916698391225)
              ·
                refine ⟨3189036493488687523793419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4252048657984916698391225 3189036493488687523793419)
                ·
                  refine ⟨4783554740233031285690129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189036493488687523793419 4783554740233031285690129)
                  ·
                    refine ⟨3587666055174773464267597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4783554740233031285690129 3587666055174773464267597)
                    ·
                      refine ⟨1345374770690540049100349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3587666055174773464267597 1345374770690540049100349)
                      ·
                        rfl

theorem cell23_2620108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2620108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620108 prefixEnd_2620108 := by exact prefixLift 2620108
  have htrace : WordTrace (prefixWord ++ tailWord_2620108) baseStart_2620108 baseEnd_2620108 := by
    simpa [prefixWord, tailWord_2620108, baseEnd_2620108] using wordTrace_append hprefix tailTrace_2620108
  have hstable : (prefixWord ++ tailWord_2620108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620108).length < 2 ^ (prefixWord ++ tailWord_2620108).sum := by decide
  have hdescent : baseEnd_2620108 < baseStart_2620108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620144 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 3, 4, 2]
def baseStart_2620144 : Nat := 118140960795 + 2620144 * 2 ^ 59
def prefixEnd_2620144 : Nat := 4983230072969 + 3 ^ 40 * 2620144 * 2
def baseEnd_2620144 : Nat := 1345393255994101908250183

theorem tailTrace_2620144 : CollatzResearch.WordTrace tailWord_2620144 prefixEnd_2620144 1345393255994101908250183 := by
  unfold tailWord_2620144
  simp only [CollatzResearch.WordTrace]
  refine ⟨47782251309836623907105743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63709668413115498542807657 47782251309836623907105743)
  ·
    refine ⟨71673376964754935860658615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47782251309836623907105743 71673376964754935860658615)
    ·
      refine ⟨107510065447132403790987923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71673376964754935860658615 107510065447132403790987923)
      ·
        refine ⟨161265098170698605686481885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107510065447132403790987923 161265098170698605686481885)
        ·
          refine ⟨60474411814011977132430707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161265098170698605686481885 60474411814011977132430707)
          ·
            refine ⟨90711617721017965698646061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60474411814011977132430707 90711617721017965698646061)
            ·
              refine ⟨34016856645381737136992273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90711617721017965698646061 34016856645381737136992273)
              ·
                refine ⟨25512642484036302852744205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34016856645381737136992273 25512642484036302852744205)
                ·
                  refine ⟨9567240931513613569779077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25512642484036302852744205 9567240931513613569779077)
                  ·
                    refine ⟨1793857674658802544333577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9567240931513613569779077 1793857674658802544333577)
                    ·
                      refine ⟨1345393255994101908250183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1793857674658802544333577 1345393255994101908250183)
                      ·
                        rfl

theorem cell23_2620144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 4, 2].length) (baseStart_2620144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620144 prefixEnd_2620144 := by exact prefixLift 2620144
  have htrace : WordTrace (prefixWord ++ tailWord_2620144) baseStart_2620144 baseEnd_2620144 := by
    simpa [prefixWord, tailWord_2620144, baseEnd_2620144] using wordTrace_append hprefix tailTrace_2620144
  have hstable : (prefixWord ++ tailWord_2620144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620144).length < 2 ^ (prefixWord ++ tailWord_2620144).sum := by decide
  have hdescent : baseEnd_2620144 < baseStart_2620144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620161 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_2620161 : Nat := 118140960795 + 2620161 * 2 ^ 59
def prefixEnd_2620161 : Nat := 4983230072969 + 3 ^ 40 * 2620161 * 2
def baseEnd_2620161 : Nat := 1345401985165228341737605

theorem tailTrace_2620161 : CollatzResearch.WordTrace tailWord_2620161 prefixEnd_2620161 1345401985165228341737605 := by
  unfold tailWord_2620161
  simp only [CollatzResearch.WordTrace]
  refine ⟨95565122660611659717580337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63710081773741106478386891 95565122660611659717580337)
  ·
    refine ⟨71673841995458744788185253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95565122660611659717580337 71673841995458744788185253)
    ·
      refine ⟨13438845374148514647784735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71673841995458744788185253 13438845374148514647784735)
      ·
        refine ⟨20158268061222771971677103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13438845374148514647784735 20158268061222771971677103)
        ·
          refine ⟨30237402091834157957515655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20158268061222771971677103 30237402091834157957515655)
          ·
            refine ⟨45356103137751236936273483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30237402091834157957515655 45356103137751236936273483)
            ·
              refine ⟨68034154706626855404410225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45356103137751236936273483 68034154706626855404410225)
              ·
                refine ⟨51025616029970141553307669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68034154706626855404410225 51025616029970141553307669)
                ·
                  refine ⟨2391825751404850385311297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51025616029970141553307669 2391825751404850385311297)
                  ·
                    refine ⟨1793869313553637788983473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2391825751404850385311297 1793869313553637788983473)
                    ·
                      refine ⟨1345401985165228341737605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1793869313553637788983473 1345401985165228341737605)
                      ·
                        rfl

theorem cell23_2620161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_2620161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620161 prefixEnd_2620161 := by exact prefixLift 2620161
  have htrace : WordTrace (prefixWord ++ tailWord_2620161) baseStart_2620161 baseEnd_2620161 := by
    simpa [prefixWord, tailWord_2620161, baseEnd_2620161] using wordTrace_append hprefix tailTrace_2620161
  have hstable : (prefixWord ++ tailWord_2620161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620161).length < 2 ^ (prefixWord ++ tailWord_2620161).sum := by decide
  have hdescent : baseEnd_2620161 < baseStart_2620161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620164 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_2620164 : Nat := 118140960795 + 2620164 * 2 ^ 59
def prefixEnd_2620164 : Nat := 4983230072969 + 3 ^ 40 * 2620164 * 2
def baseEnd_2620164 : Nat := 1345403525607191830000091

theorem tailTrace_2620164 : CollatzResearch.WordTrace tailWord_2620164 prefixEnd_2620164 1345403525607191830000091 := by
  unfold tailWord_2620164
  simp only [CollatzResearch.WordTrace]
  refine ⟨47782616039800395614969773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63710154719733860819959697 47782616039800395614969773)
  ·
    refine ⟨17918481014925148355613665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47782616039800395614969773 17918481014925148355613665)
    ·
      refine ⟨13438860761193861266710249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17918481014925148355613665 13438860761193861266710249)
      ·
        refine ⟨10079145570895395950032687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13438860761193861266710249 10079145570895395950032687)
        ·
          refine ⟨15118718356343093925049031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10079145570895395950032687 15118718356343093925049031)
          ·
            refine ⟨22678077534514640887573547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15118718356343093925049031 22678077534514640887573547)
            ·
              refine ⟨34017116301771961331360321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22678077534514640887573547 34017116301771961331360321)
              ·
                refine ⟨25512837226328970998520241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34017116301771961331360321 25512837226328970998520241)
                ·
                  refine ⟨19134627919746728248890181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25512837226328970998520241 19134627919746728248890181)
                  ·
                    refine ⟨3587742734952511546666909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19134627919746728248890181 3587742734952511546666909)
                    ·
                      refine ⟨1345403525607191830000091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3587742734952511546666909 1345403525607191830000091)
                      ·
                        rfl

theorem cell23_2620164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_2620164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620164 prefixEnd_2620164 := by exact prefixLift 2620164
  have htrace : WordTrace (prefixWord ++ tailWord_2620164) baseStart_2620164 baseEnd_2620164 := by
    simpa [prefixWord, tailWord_2620164, baseEnd_2620164] using wordTrace_append hprefix tailTrace_2620164
  have hstable : (prefixWord ++ tailWord_2620164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620164).length < 2 ^ (prefixWord ++ tailWord_2620164).sum := by decide
  have hdescent : baseEnd_2620164 < baseStart_2620164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620212 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_2620212 : Nat := 118140960795 + 2620212 * 2 ^ 59
def prefixEnd_2620212 : Nat := 4983230072969 + 3 ^ 40 * 2620212 * 2
def baseEnd_2620212 : Nat := 1345428172678607642199871

theorem tailTrace_2620212 : CollatzResearch.WordTrace tailWord_2620212 prefixEnd_2620212 1345428172678607642199871 := by
  unfold tailWord_2620212
  simp only [CollatzResearch.WordTrace]
  refine ⟨47783491391713447713843445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63711321855617930285124593 47783491391713447713843445)
  ·
    refine ⟨4479702317973135723172823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47783491391713447713843445 4479702317973135723172823)
    ·
      refine ⟨6719553476959703584759235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4479702317973135723172823 6719553476959703584759235)
      ·
        refine ⟨10079330215439555377138853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6719553476959703584759235 10079330215439555377138853)
        ·
          refine ⟨1889874415394916633213535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10079330215439555377138853 1889874415394916633213535)
          ·
            refine ⟨2834811623092374949820303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889874415394916633213535 2834811623092374949820303)
            ·
              refine ⟨4252217434638562424730455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834811623092374949820303 4252217434638562424730455)
              ·
                refine ⟨6378326151957843637095683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4252217434638562424730455 6378326151957843637095683)
                ·
                  refine ⟨9567489227936765455643525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6378326151957843637095683 9567489227936765455643525)
                  ·
                    refine ⟨1793904230238143522933161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9567489227936765455643525 1793904230238143522933161)
                    ·
                      refine ⟨1345428172678607642199871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1793904230238143522933161 1345428172678607642199871)
                      ·
                        rfl

theorem cell23_2620212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_2620212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620212 prefixEnd_2620212 := by exact prefixLift 2620212
  have htrace : WordTrace (prefixWord ++ tailWord_2620212) baseStart_2620212 baseEnd_2620212 := by
    simpa [prefixWord, tailWord_2620212, baseEnd_2620212] using wordTrace_append hprefix tailTrace_2620212
  have hstable : (prefixWord ++ tailWord_2620212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620212).length < 2 ^ (prefixWord ++ tailWord_2620212).sum := by decide
  have hdescent : baseEnd_2620212 < baseStart_2620212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620227 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 2, 8]
def baseStart_2620227 : Nat := 118140960795 + 2620227 * 2 ^ 59
def prefixEnd_2620227 : Nat := 4983230072969 + 3 ^ 40 * 2620227 * 2
def baseEnd_2620227 : Nat := 448478624962808361170767

theorem tailTrace_2620227 : CollatzResearch.WordTrace tailWord_2620227 prefixEnd_2620227 448478624962808361170767 := by
  unfold tailWord_2620227
  simp only [CollatzResearch.WordTrace]
  refine ⟨95567529878372552989482935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63711686585581701992988623 95567529878372552989482935)
  ·
    refine ⟨143351294817558829484224403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95567529878372552989482935 143351294817558829484224403)
    ·
      refine ⟨215026942226338244226336605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143351294817558829484224403 215026942226338244226336605)
      ·
        refine ⟨80635103334876841584876227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215026942226338244226336605 80635103334876841584876227)
        ·
          refine ⟨120952655002315262377314341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80635103334876841584876227 120952655002315262377314341)
          ·
            refine ⟨22678622812934111695746439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120952655002315262377314341 22678622812934111695746439)
            ·
              refine ⟨34017934219401167543619659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22678622812934111695746439 34017934219401167543619659)
              ·
                refine ⟨51026901329101751315429489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34017934219401167543619659 51026901329101751315429489)
                ·
                  refine ⟨38270175996826313486572117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51026901329101751315429489 38270175996826313486572117)
                  ·
                    refine ⟨448478624962808361170767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38270175996826313486572117 448478624962808361170767)
                    ·
                      rfl

theorem cell23_2620227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 8].length) (baseStart_2620227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620227 prefixEnd_2620227 := by exact prefixLift 2620227
  have htrace : WordTrace (prefixWord ++ tailWord_2620227) baseStart_2620227 baseEnd_2620227 := by
    simpa [prefixWord, tailWord_2620227, baseEnd_2620227] using wordTrace_append hprefix tailTrace_2620227
  have hstable : (prefixWord ++ tailWord_2620227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620227).length < 2 ^ (prefixWord ++ tailWord_2620227).sum := by decide
  have hdescent : baseEnd_2620227 < baseStart_2620227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620261 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 3, 4]
def baseStart_2620261 : Nat := 118140960795 + 2620261 * 2 ^ 59
def prefixEnd_2620261 : Nat := 4983230072969 + 3 ^ 40 * 2620261 * 2
def baseEnd_2620261 : Nat := 448484444410225983495715

theorem tailTrace_2620261 : CollatzResearch.WordTrace tailWord_2620261 prefixEnd_2620261 448484444410225983495715 := by
  unfold tailWord_2620261
  simp only [CollatzResearch.WordTrace]
  refine ⟨95568769960249376796220637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63712513306832917864147091 95568769960249376796220637)
  ·
    refine ⟨35838288735093516298582739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95568769960249376796220637 35838288735093516298582739)
    ·
      refine ⟨53757433102640274447874109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35838288735093516298582739 53757433102640274447874109)
      ·
        refine ⟨20159037413490102917952791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53757433102640274447874109 20159037413490102917952791)
        ·
          refine ⟨30238556120235154376929187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20159037413490102917952791 30238556120235154376929187)
          ·
            refine ⟨45357834180352731565393781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30238556120235154376929187 45357834180352731565393781)
            ·
              refine ⟨4252296954408068584255667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45357834180352731565393781 4252296954408068584255667)
              ·
                refine ⟨6378445431612102876383501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4252296954408068584255667 6378445431612102876383501)
                ·
                  refine ⟨2391917036854538578643813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6378445431612102876383501 2391917036854538578643813)
                  ·
                    refine ⟨448484444410225983495715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2391917036854538578643813 448484444410225983495715)
                    ·
                      rfl

theorem cell23_2620261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_2620261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620261 prefixEnd_2620261 := by exact prefixLift 2620261
  have htrace : WordTrace (prefixWord ++ tailWord_2620261) baseStart_2620261 baseEnd_2620261 := by
    simpa [prefixWord, tailWord_2620261, baseEnd_2620261] using wordTrace_append hprefix tailTrace_2620261
  have hstable : (prefixWord ++ tailWord_2620261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620261).length < 2 ^ (prefixWord ++ tailWord_2620261).sum := by decide
  have hdescent : baseEnd_2620261 < baseStart_2620261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620284 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_2620284 : Nat := 118140960795 + 2620284 * 2 ^ 59
def prefixEnd_2620284 : Nat := 4983230072969 + 3 ^ 40 * 2620284 * 2
def baseEnd_2620284 : Nat := 1345465143285731360499539

theorem tailTrace_2620284 : CollatzResearch.WordTrace tailWord_2620284 prefixEnd_2620284 1345465143285731360499539 := by
  unfold tailWord_2620284
  simp only [CollatzResearch.WordTrace]
  refine ⟨47784804419583025862153953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63713072559444034482871937 47784804419583025862153953)
  ·
    refine ⟨35838603314687269396615465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47784804419583025862153953 35838603314687269396615465)
    ·
      refine ⟨26878952486015452047461599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35838603314687269396615465 26878952486015452047461599)
      ·
        refine ⟨40318428729023178071192399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26878952486015452047461599 40318428729023178071192399)
        ·
          refine ⟨60477643093534767106788599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40318428729023178071192399 60477643093534767106788599)
          ·
            refine ⟨90716464640302150660182899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60477643093534767106788599 90716464640302150660182899)
            ·
              refine ⟨136074696960453225990274349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90716464640302150660182899 136074696960453225990274349)
              ·
                refine ⟨51028011360169959746352881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136074696960453225990274349 51028011360169959746352881)
                ·
                  refine ⟨38271008520127469809764661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51028011360169959746352881 38271008520127469809764661)
                  ·
                    refine ⟨3587907048761950294665437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38271008520127469809764661 3587907048761950294665437)
                    ·
                      refine ⟨1345465143285731360499539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3587907048761950294665437 1345465143285731360499539)
                      ·
                        rfl

theorem cell23_2620284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_2620284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620284 prefixEnd_2620284 := by exact prefixLift 2620284
  have htrace : WordTrace (prefixWord ++ tailWord_2620284) baseStart_2620284 baseEnd_2620284 := by
    simpa [prefixWord, tailWord_2620284, baseEnd_2620284] using wordTrace_append hprefix tailTrace_2620284
  have hstable : (prefixWord ++ tailWord_2620284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620284).length < 2 ^ (prefixWord ++ tailWord_2620284).sum := by decide
  have hdescent : baseEnd_2620284 < baseStart_2620284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620321 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 3, 5]
def baseStart_2620321 : Nat := 118140960795 + 2620321 * 2 ^ 59
def prefixEnd_2620321 : Nat := 4983230072969 + 3 ^ 40 * 2620321 * 2
def baseEnd_2620321 : Nat := 448494714023315905245623

theorem tailTrace_2620321 : CollatzResearch.WordTrace tailWord_2620321 prefixEnd_2620321 448494714023315905245623 := by
  unfold tailWord_2620321
  simp only [CollatzResearch.WordTrace]
  refine ⟨95570958340032007043404817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63713972226688004695603211 95570958340032007043404817)
  ·
    refine ⟨71678218755024005282553613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95570958340032007043404817 71678218755024005282553613)
    ·
      refine ⟨26879332033134001980957605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71678218755024005282553613 26879332033134001980957605)
      ·
        refine ⟨5039874756212625371429551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26879332033134001980957605 5039874756212625371429551)
        ·
          refine ⟨7559812134318938057144327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5039874756212625371429551 7559812134318938057144327)
          ·
            refine ⟨11339718201478407085716491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7559812134318938057144327 11339718201478407085716491)
            ·
              refine ⟨17009577302217610628574737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11339718201478407085716491 17009577302217610628574737)
              ·
                refine ⟨12757182976663207971431053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17009577302217610628574737 12757182976663207971431053)
                ·
                  refine ⟨4783943616248702989286645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12757182976663207971431053 4783943616248702989286645)
                  ·
                    refine ⟨448494714023315905245623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4783943616248702989286645 448494714023315905245623)
                    ·
                      rfl

theorem cell23_2620321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_2620321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620321 prefixEnd_2620321 := by exact prefixLift 2620321
  have htrace : WordTrace (prefixWord ++ tailWord_2620321) baseStart_2620321 baseEnd_2620321 := by
    simpa [prefixWord, tailWord_2620321, baseEnd_2620321] using wordTrace_append hprefix tailTrace_2620321
  have hstable : (prefixWord ++ tailWord_2620321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620321).length < 2 ^ (prefixWord ++ tailWord_2620321).sum := by decide
  have hdescent : baseEnd_2620321 < baseStart_2620321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620341 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_2620341 : Nat := 118140960795 + 2620341 * 2 ^ 59
def prefixEnd_2620341 : Nat := 4983230072969 + 3 ^ 40 * 2620341 * 2
def baseEnd_2620341 : Nat := 1345494411683037637486777

theorem tailTrace_2620341 : CollatzResearch.WordTrace tailWord_2620341 prefixEnd_2620341 1345494411683037637486777 := by
  unfold tailWord_2620341
  simp only [CollatzResearch.WordTrace]
  refine ⟨95571687799959550459132877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63714458533306366972755251 95571687799959550459132877)
  ·
    refine ⟨35839382924984831422174829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95571687799959550459132877 35839382924984831422174829)
    ·
      refine ⟨13439768596869311783315561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35839382924984831422174829 13439768596869311783315561)
      ·
        refine ⟨10079826447651983837486671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13439768596869311783315561 10079826447651983837486671)
        ·
          refine ⟨15119739671477975756230007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10079826447651983837486671 15119739671477975756230007)
          ·
            refine ⟨22679609507216963634345011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15119739671477975756230007 22679609507216963634345011)
            ·
              refine ⟨34019414260825445451517517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22679609507216963634345011 34019414260825445451517517)
              ·
                refine ⟨12757280347809542044319069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34019414260825445451517517 12757280347809542044319069)
                ·
                  refine ⟨4783980130428578266619651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12757280347809542044319069 4783980130428578266619651)
                  ·
                    refine ⟨7175970195642867399929477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4783980130428578266619651 7175970195642867399929477)
                    ·
                      refine ⟨1345494411683037637486777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7175970195642867399929477 1345494411683037637486777)
                      ·
                        rfl

theorem cell23_2620341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_2620341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620341 prefixEnd_2620341 := by exact prefixLift 2620341
  have htrace : WordTrace (prefixWord ++ tailWord_2620341) baseStart_2620341 baseEnd_2620341 := by
    simpa [prefixWord, tailWord_2620341, baseEnd_2620341] using wordTrace_append hprefix tailTrace_2620341
  have hstable : (prefixWord ++ tailWord_2620341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620341).length < 2 ^ (prefixWord ++ tailWord_2620341).sum := by decide
  have hdescent : baseEnd_2620341 < baseStart_2620341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620345 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 2, 3, 2]
def baseStart_2620345 : Nat := 118140960795 + 2620345 * 2 ^ 59
def prefixEnd_2620345 : Nat := 4983230072969 + 3 ^ 40 * 2620345 * 2
def baseEnd_2620345 : Nat := 1345496465605655621836759

theorem tailTrace_2620345 : CollatzResearch.WordTrace tailWord_2620345 prefixEnd_2620345 1345496465605655621836759 := by
  unfold tailWord_2620345
  simp only [CollatzResearch.WordTrace]
  refine ⟨95571833691945059142278489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63714555794630039428185659 95571833691945059142278489)
  ·
    refine ⟨71678875268958794356708867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95571833691945059142278489 71678875268958794356708867)
    ·
      refine ⟨107518312903438191535063301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71678875268958794356708867 107518312903438191535063301)
      ·
        refine ⟨20159683669394660912824369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107518312903438191535063301 20159683669394660912824369)
        ·
          refine ⟨15119762752045995684618277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20159683669394660912824369 15119762752045995684618277)
          ·
            refine ⟨2834955516008624190865927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15119762752045995684618277 2834955516008624190865927)
            ·
              refine ⟨4252433274012936286298891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834955516008624190865927 4252433274012936286298891)
              ·
                refine ⟨6378649911019404429448337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4252433274012936286298891 6378649911019404429448337)
                ·
                  refine ⟨4783987433264553322086253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6378649911019404429448337 4783987433264553322086253)
                  ·
                    refine ⟨1793995287474207495782345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4783987433264553322086253 1793995287474207495782345)
                    ·
                      refine ⟨1345496465605655621836759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1793995287474207495782345 1345496465605655621836759)
                      ·
                        rfl

theorem cell23_2620345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_2620345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620345 prefixEnd_2620345 := by exact prefixLift 2620345
  have htrace : WordTrace (prefixWord ++ tailWord_2620345) baseStart_2620345 baseEnd_2620345 := by
    simpa [prefixWord, tailWord_2620345, baseEnd_2620345] using wordTrace_append hprefix tailTrace_2620345
  have hstable : (prefixWord ++ tailWord_2620345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620345).length < 2 ^ (prefixWord ++ tailWord_2620345).sum := by decide
  have hdescent : baseEnd_2620345 < baseStart_2620345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620364 : List Nat := [2, 2, 1, 4, 1, 1, 12]
def baseStart_2620364 : Nat := 118140960795 + 2620364 * 2 ^ 59
def prefixEnd_2620364 : Nat := 4983230072969 + 3 ^ 40 * 2620364 * 2
def baseEnd_2620364 : Nat := 16611187922692482067891

theorem tailTrace_2620364 : CollatzResearch.WordTrace tailWord_2620364 prefixEnd_2620364 16611187922692482067891 := by
  unfold tailWord_2620364
  simp only [CollatzResearch.WordTrace]
  refine ⟨47786263339438112693610073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63715017785917483591480097 47786263339438112693610073)
  ·
    refine ⟨35839697504578584520207555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47786263339438112693610073 35839697504578584520207555)
    ·
      refine ⟨53759546256867876780311333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35839697504578584520207555 53759546256867876780311333)
      ·
        refine ⟨10079914923162726896308375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53759546256867876780311333 10079914923162726896308375)
        ·
          refine ⟨15119872384744090344462563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10079914923162726896308375 15119872384744090344462563)
          ·
            refine ⟨22679808577116135516693845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15119872384744090344462563 22679808577116135516693845)
            ·
              refine ⟨16611187922692482067891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 22679808577116135516693845 16611187922692482067891)
              ·
                rfl

theorem cell23_2620364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 12].length) (baseStart_2620364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620364 prefixEnd_2620364 := by exact prefixLift 2620364
  have htrace : WordTrace (prefixWord ++ tailWord_2620364) baseStart_2620364 baseEnd_2620364 := by
    simpa [prefixWord, tailWord_2620364, baseEnd_2620364] using wordTrace_append hprefix tailTrace_2620364
  have hstable : (prefixWord ++ tailWord_2620364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620364).length < 2 ^ (prefixWord ++ tailWord_2620364).sum := by decide
  have hdescent : baseEnd_2620364 < baseStart_2620364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620451 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 5]
def baseStart_2620451 : Nat := 118140960795 + 2620451 * 2 ^ 59
def prefixEnd_2620451 : Nat := 4983230072969 + 3 ^ 40 * 2620451 * 2
def baseEnd_2620451 : Nat := 1345550894555032207111271

theorem tailTrace_2620451 : CollatzResearch.WordTrace tailWord_2620451 prefixEnd_2620451 1345550894555032207111271 := by
  unfold tailWord_2620451
  simp only [CollatzResearch.WordTrace]
  refine ⟨95575699829561039245637207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63717133219707359497091471 95575699829561039245637207)
  ·
    refine ⟨143363549744341558868455811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95575699829561039245637207 143363549744341558868455811)
    ·
      refine ⟨215045324616512338302683717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143363549744341558868455811 215045324616512338302683717)
      ·
        refine ⟨40320998365596063431753197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215045324616512338302683717 40320998365596063431753197)
        ·
          refine ⟨15120374387098523786907449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40320998365596063431753197 15120374387098523786907449)
          ·
            refine ⟨11340280790323892840180587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15120374387098523786907449 11340280790323892840180587)
            ·
              refine ⟨17010421185485839260270881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11340280790323892840180587 17010421185485839260270881)
              ·
                refine ⟨12757815889114379445203161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17010421185485839260270881 12757815889114379445203161)
                ·
                  refine ⟨9568361916835784583902371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12757815889114379445203161 9568361916835784583902371)
                  ·
                    refine ⟨14352542875253676875853557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9568361916835784583902371 14352542875253676875853557)
                    ·
                      refine ⟨1345550894555032207111271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14352542875253676875853557 1345550894555032207111271)
                      ·
                        rfl

theorem cell23_2620451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_2620451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620451 prefixEnd_2620451 := by exact prefixLift 2620451
  have htrace : WordTrace (prefixWord ++ tailWord_2620451) baseStart_2620451 baseEnd_2620451 := by
    simpa [prefixWord, tailWord_2620451, baseEnd_2620451] using wordTrace_append hprefix tailTrace_2620451
  have hstable : (prefixWord ++ tailWord_2620451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620451).length < 2 ^ (prefixWord ++ tailWord_2620451).sum := by decide
  have hdescent : baseEnd_2620451 < baseStart_2620451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620452 : List Nat := [2, 3, 1, 4, 1, 1, 3, 2, 1, 3, 2]
def baseStart_2620452 : Nat := 118140960795 + 2620452 * 2 ^ 59
def prefixEnd_2620452 : Nat := 4983230072969 + 3 ^ 40 * 2620452 * 2
def baseEnd_2620452 : Nat := 1345551408035686703198767

theorem tailTrace_2620452 : CollatzResearch.WordTrace tailWord_2620452 prefixEnd_2620452 1345551408035686703198767 := by
  unfold tailWord_2620452
  simp only [CollatzResearch.WordTrace]
  refine ⟨47787868151278708208211805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63717157535038277610949073 47787868151278708208211805)
  ·
    refine ⟨17920450556729515578079427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47787868151278708208211805 17920450556729515578079427)
    ·
      refine ⟨26880675835094273367119141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17920450556729515578079427 26880675835094273367119141)
      ·
        refine ⟨5040126719080176256334839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26880675835094273367119141 5040126719080176256334839)
        ·
          refine ⟨7560190078620264384502259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5040126719080176256334839 7560190078620264384502259)
          ·
            refine ⟨11340285117930396576753389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7560190078620264384502259 11340285117930396576753389)
            ·
              refine ⟨4252606919223898716282521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11340285117930396576753389 4252606919223898716282521)
              ·
                refine ⟨3189455189417924037211891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4252606919223898716282521 3189455189417924037211891)
                ·
                  refine ⟨4784182784126886055817837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189455189417924037211891 4784182784126886055817837)
                  ·
                    refine ⟨1794068544047582270931689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4784182784126886055817837 1794068544047582270931689)
                    ·
                      refine ⟨1345551408035686703198767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1794068544047582270931689 1345551408035686703198767)
                      ·
                        rfl

theorem cell23_2620452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_2620452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620452 prefixEnd_2620452 := by exact prefixLift 2620452
  have htrace : WordTrace (prefixWord ++ tailWord_2620452) baseStart_2620452 baseEnd_2620452 := by
    simpa [prefixWord, tailWord_2620452, baseEnd_2620452] using wordTrace_append hprefix tailTrace_2620452
  have hstable : (prefixWord ++ tailWord_2620452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620452).length < 2 ^ (prefixWord ++ tailWord_2620452).sum := by decide
  have hdescent : baseEnd_2620452 < baseStart_2620452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620488 : List Nat := [2, 1, 3, 1, 1, 1, 5, 4, 5]
def baseStart_2620488 : Nat := 118140960795 + 2620488 * 2 ^ 59
def prefixEnd_2620488 : Nat := 4983230072969 + 3 ^ 40 * 2620488 * 2
def baseEnd_2620488 : Nat := 149507765926583173594289

theorem tailTrace_2620488 : CollatzResearch.WordTrace tailWord_2620488 prefixEnd_2620488 149507765926583173594289 := by
  unfold tailWord_2620488
  simp only [CollatzResearch.WordTrace]
  refine ⟨47788524665213497282367059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63718032886951329709822745 47788524665213497282367059)
  ·
    refine ⟨71682786997820245923550589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47788524665213497282367059 71682786997820245923550589)
    ·
      refine ⟨26881045124182592221331471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71682786997820245923550589 26881045124182592221331471)
      ·
        refine ⟨40321567686273888331997207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26881045124182592221331471 40321567686273888331997207)
        ·
          refine ⟨60482351529410832497995811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40321567686273888331997207 60482351529410832497995811)
          ·
            refine ⟨90723527294116248746993717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60482351529410832497995811 90723527294116248746993717)
            ·
              refine ⟨8505330683823398320030661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90723527294116248746993717 8505330683823398320030661)
              ·
                refine ⟨1594749503216887185005749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8505330683823398320030661 1594749503216887185005749)
                ·
                  refine ⟨149507765926583173594289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1594749503216887185005749 149507765926583173594289)
                  ·
                    rfl

theorem cell23_2620488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 5].length) (baseStart_2620488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620488 prefixEnd_2620488 := by exact prefixLift 2620488
  have htrace : WordTrace (prefixWord ++ tailWord_2620488) baseStart_2620488 baseEnd_2620488 := by
    simpa [prefixWord, tailWord_2620488, baseEnd_2620488] using wordTrace_append hprefix tailTrace_2620488
  have hstable : (prefixWord ++ tailWord_2620488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620488).length < 2 ^ (prefixWord ++ tailWord_2620488).sum := by decide
  have hdescent : baseEnd_2620488 < baseStart_2620488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620498 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_2620498 : Nat := 118140960795 + 2620498 * 2 ^ 59
def prefixEnd_2620498 : Nat := 4983230072969 + 3 ^ 40 * 2620498 * 2
def baseEnd_2620498 : Nat := 1345575028145793523223555

theorem tailTrace_2620498 : CollatzResearch.WordTrace tailWord_2620498 prefixEnd_2620498 1345575028145793523223555 := by
  unfold tailWord_2620498
  simp only [CollatzResearch.WordTrace]
  refine ⟨23894353515097691568149537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63718276040260510848398765 23894353515097691568149537)
  ·
    refine ⟨17920765136323268676112153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23894353515097691568149537 17920765136323268676112153)
    ·
      refine ⟨13440573852242451507084115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17920765136323268676112153 13440573852242451507084115)
      ·
        refine ⟨20160860778363677260626173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13440573852242451507084115 20160860778363677260626173)
        ·
          refine ⟨7560322791886378972734815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20160860778363677260626173 7560322791886378972734815)
          ·
            refine ⟨11340484187829568459102223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7560322791886378972734815 11340484187829568459102223)
            ·
              refine ⟨17010726281744352688653335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11340484187829568459102223 17010726281744352688653335)
              ·
                refine ⟨25516089422616529032980003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17010726281744352688653335 25516089422616529032980003)
                ·
                  refine ⟨38274134133924793549470005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25516089422616529032980003 38274134133924793549470005)
                  ·
                    refine ⟨3588200075055449395262813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38274134133924793549470005 3588200075055449395262813)
                    ·
                      refine ⟨1345575028145793523223555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3588200075055449395262813 1345575028145793523223555)
                      ·
                        rfl

theorem cell23_2620498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_2620498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620498 prefixEnd_2620498 := by exact prefixLift 2620498
  have htrace : WordTrace (prefixWord ++ tailWord_2620498) baseStart_2620498 baseEnd_2620498 := by
    simpa [prefixWord, tailWord_2620498, baseEnd_2620498] using wordTrace_append hprefix tailTrace_2620498
  have hstable : (prefixWord ++ tailWord_2620498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620498).length < 2 ^ (prefixWord ++ tailWord_2620498).sum := by decide
  have hdescent : baseEnd_2620498 < baseStart_2620498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620501 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 1, 7]
def baseStart_2620501 : Nat := 118140960795 + 2620501 * 2 ^ 59
def prefixEnd_2620501 : Nat := 4983230072969 + 3 ^ 40 * 2620501 * 2
def baseEnd_2620501 : Nat := 448525522862585670495347

theorem tailTrace_2620501 : CollatzResearch.WordTrace tailWord_2620501 prefixEnd_2620501 448525522862585670495347 := by
  unfold tailWord_2620501
  simp only [CollatzResearch.WordTrace]
  refine ⟨95577523479379897784957357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63718348986253265189971571 95577523479379897784957357)
  ·
    refine ⟨35841571304767461669359009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95577523479379897784957357 35841571304767461669359009)
    ·
      refine ⟨26881178478575596252019257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35841571304767461669359009 26881178478575596252019257)
      ·
        refine ⟨20160883858931697189014443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26881178478575596252019257 20160883858931697189014443)
        ·
          refine ⟨30241325788397545783521665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20160883858931697189014443 30241325788397545783521665)
          ·
            refine ⟨22680994341298159337641249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30241325788397545783521665 22680994341298159337641249)
            ·
              refine ⟨17010745755973619503230937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22680994341298159337641249 17010745755973619503230937)
              ·
                refine ⟨12758059316980214627423203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17010745755973619503230937 12758059316980214627423203)
                ·
                  refine ⟨19137088975470321941134805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12758059316980214627423203 19137088975470321941134805)
                  ·
                    refine ⟨448525522862585670495347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19137088975470321941134805 448525522862585670495347)
                    ·
                      rfl

theorem cell23_2620501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_2620501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620501 prefixEnd_2620501 := by exact prefixLift 2620501
  have htrace : WordTrace (prefixWord ++ tailWord_2620501) baseStart_2620501 baseEnd_2620501 := by
    simpa [prefixWord, tailWord_2620501, baseEnd_2620501] using wordTrace_append hprefix tailTrace_2620501
  have hstable : (prefixWord ++ tailWord_2620501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620501).length < 2 ^ (prefixWord ++ tailWord_2620501).sum := by decide
  have hdescent : baseEnd_2620501 < baseStart_2620501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620533 : List Nat := [1, 3, 4, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2620533 : Nat := 118140960795 + 2620533 * 2 ^ 59
def prefixEnd_2620533 : Nat := 4983230072969 + 3 ^ 40 * 2620533 * 2
def baseEnd_2620533 : Nat := 1345592999968700886285895

theorem tailTrace_2620533 : CollatzResearch.WordTrace tailWord_2620533 prefixEnd_2620533 1345592999968700886285895 := by
  unfold tailWord_2620533
  simp only [CollatzResearch.WordTrace]
  refine ⟨95578690615263967250122253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63719127076842644833414835 95578690615263967250122253)
  ·
    refine ⟨35842008980723987718795845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95578690615263967250122253 35842008980723987718795845)
    ·
      refine ⟨6720376683885747697274221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35842008980723987718795845 6720376683885747697274221)
      ·
        refine ⟨2520141256457155386477833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6720376683885747697274221 2520141256457155386477833)
        ·
          refine ⟨1890105942342866539858375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2520141256457155386477833 1890105942342866539858375)
          ·
            refine ⟨2835158913514299809787563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890105942342866539858375 2835158913514299809787563)
            ·
              refine ⟨4252738370271449714681345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835158913514299809787563 4252738370271449714681345)
              ·
                refine ⟨3189553777703587286011009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4252738370271449714681345 3189553777703587286011009)
                ·
                  refine ⟨2392165333277690464508257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3189553777703587286011009 2392165333277690464508257)
                  ·
                    refine ⟨1794123999958267848381193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2392165333277690464508257 1794123999958267848381193)
                    ·
                      refine ⟨1345592999968700886285895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1794123999958267848381193 1345592999968700886285895)
                      ·
                        rfl

theorem cell23_2620533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2620533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620533 prefixEnd_2620533 := by exact prefixLift 2620533
  have htrace : WordTrace (prefixWord ++ tailWord_2620533) baseStart_2620533 baseEnd_2620533 := by
    simpa [prefixWord, tailWord_2620533, baseEnd_2620533] using wordTrace_append hprefix tailTrace_2620533
  have hstable : (prefixWord ++ tailWord_2620533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620533).length < 2 ^ (prefixWord ++ tailWord_2620533).sum := by decide
  have hdescent : baseEnd_2620533 < baseStart_2620533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620551 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_2620551 : Nat := 118140960795 + 2620551 * 2 ^ 59
def prefixEnd_2620551 : Nat := 4983230072969 + 3 ^ 40 * 2620551 * 2
def baseEnd_2620551 : Nat := 1345602242620481815860811

theorem tailTrace_2620551 : CollatzResearch.WordTrace tailWord_2620551 prefixEnd_2620551 1345602242620481815860811 := by
  unfold tailWord_2620551
  simp only [CollatzResearch.WordTrace]
  refine ⟨95579347129198756324277507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63719564752799170882851671 95579347129198756324277507)
  ·
    refine ⟨143369020693798134486416261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95579347129198756324277507 143369020693798134486416261)
    ·
      refine ⟨26881691380087150216203049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143369020693798134486416261 26881691380087150216203049)
      ·
        refine ⟨20161268535065362662152287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26881691380087150216203049 20161268535065362662152287)
        ·
          refine ⟨30241902802598043993228431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20161268535065362662152287 30241902802598043993228431)
          ·
            refine ⟨45362854203897065989842647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30241902802598043993228431 45362854203897065989842647)
            ·
              refine ⟨68044281305845598984763971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45362854203897065989842647 68044281305845598984763971)
              ·
                refine ⟨102066421958768398477145957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68044281305845598984763971 102066421958768398477145957)
                ·
                  refine ⟨19137454117269074714464867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102066421958768398477145957 19137454117269074714464867)
                  ·
                    refine ⟨28706181175903612071697301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19137454117269074714464867 28706181175903612071697301)
                    ·
                      refine ⟨1345602242620481815860811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28706181175903612071697301 1345602242620481815860811)
                      ·
                        rfl

theorem cell23_2620551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_2620551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620551 prefixEnd_2620551 := by exact prefixLift 2620551
  have htrace : WordTrace (prefixWord ++ tailWord_2620551) baseStart_2620551 baseEnd_2620551 := by
    simpa [prefixWord, tailWord_2620551, baseEnd_2620551] using wordTrace_append hprefix tailTrace_2620551
  have hstable : (prefixWord ++ tailWord_2620551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620551).length < 2 ^ (prefixWord ++ tailWord_2620551).sum := by decide
  have hdescent : baseEnd_2620551 < baseStart_2620551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620651 : List Nat := [1, 1, 1, 1, 2, 17]
def baseStart_2620651 : Nat := 118140960795 + 2620651 * 2 ^ 59
def prefixEnd_2620651 : Nat := 4983230072969 + 3 ^ 40 * 2620651 * 2
def baseEnd_2620651 : Nat := 5537669097472968825557

theorem tailTrace_2620651 : CollatzResearch.WordTrace tailWord_2620651 prefixEnd_2620651 5537669097472968825557 := by
  unfold tailWord_2620651
  simp only [CollatzResearch.WordTrace]
  refine ⟨95582994428836473402917807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63721996285890982268611871 95582994428836473402917807)
  ·
    refine ⟨143374491643254710104376711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95582994428836473402917807 143374491643254710104376711)
    ·
      refine ⟨215061737464882065156565067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143374491643254710104376711 215061737464882065156565067)
      ·
        refine ⟨322592606197323097734847601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215061737464882065156565067 322592606197323097734847601)
        ·
          refine ⟨241944454647992323301135701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322592606197323097734847601 241944454647992323301135701)
          ·
            refine ⟨5537669097472968825557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 17 241944454647992323301135701 5537669097472968825557)
            ·
              rfl

theorem cell23_2620651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 17].length) (baseStart_2620651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620651 prefixEnd_2620651 := by exact prefixLift 2620651
  have htrace : WordTrace (prefixWord ++ tailWord_2620651) baseStart_2620651 baseEnd_2620651 := by
    simpa [prefixWord, tailWord_2620651, baseEnd_2620651] using wordTrace_append hprefix tailTrace_2620651
  have hstable : (prefixWord ++ tailWord_2620651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620651).length < 2 ^ (prefixWord ++ tailWord_2620651).sum := by decide
  have hdescent : baseEnd_2620651 < baseStart_2620651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620675 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 4]
def baseStart_2620675 : Nat := 118140960795 + 2620675 * 2 ^ 59
def prefixEnd_2620675 : Nat := 4983230072969 + 3 ^ 40 * 2620675 * 2
def baseEnd_2620675 : Nat := 1345665914221639330710241

theorem tailTrace_2620675 : CollatzResearch.WordTrace tailWord_2620675 prefixEnd_2620675 1345665914221639330710241 := by
  unfold tailWord_2620675
  simp only [CollatzResearch.WordTrace]
  refine ⟨95583869780749525501791479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63722579853833017001194319 95583869780749525501791479)
  ·
    refine ⟨143375804671124288252687219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95583869780749525501791479 143375804671124288252687219)
    ·
      refine ⟨215063707006686432379030829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143375804671124288252687219 215063707006686432379030829)
      ·
        refine ⟨80648890127507412142136561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215063707006686432379030829 80648890127507412142136561)
        ·
          refine ⟨60486667595630559106602421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80648890127507412142136561 60486667595630559106602421)
          ·
            refine ⟨5670625087090364916243977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60486667595630559106602421 5670625087090364916243977)
            ·
              refine ⟨4252968815317773687182983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5670625087090364916243977 4252968815317773687182983)
              ·
                refine ⟨6379453222976660530774475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4252968815317773687182983 6379453222976660530774475)
                ·
                  refine ⟨9569179834464990796161713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6379453222976660530774475 9569179834464990796161713)
                  ·
                    refine ⟨7176884875848743097121285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9569179834464990796161713 7176884875848743097121285)
                    ·
                      refine ⟨1345665914221639330710241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7176884875848743097121285 1345665914221639330710241)
                      ·
                        rfl

theorem cell23_2620675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_2620675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620675 prefixEnd_2620675 := by exact prefixLift 2620675
  have htrace : WordTrace (prefixWord ++ tailWord_2620675) baseStart_2620675 baseEnd_2620675 := by
    simpa [prefixWord, tailWord_2620675, baseEnd_2620675] using wordTrace_append hprefix tailTrace_2620675
  have hstable : (prefixWord ++ tailWord_2620675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620675).length < 2 ^ (prefixWord ++ tailWord_2620675).sum := by decide
  have hdescent : baseEnd_2620675 < baseStart_2620675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620695 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 3]
def baseStart_2620695 : Nat := 118140960795 + 2620695 * 2 ^ 59
def prefixEnd_2620695 : Nat := 4983230072969 + 3 ^ 40 * 2620695 * 2
def baseEnd_2620695 : Nat := 1345676183834729252460149

theorem tailTrace_2620695 : CollatzResearch.WordTrace tailWord_2620695 prefixEnd_2620695 1345676183834729252460149 := by
  unfold tailWord_2620695
  simp only [CollatzResearch.WordTrace]
  refine ⟨95584599240677068917519539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63723066160451379278346359 95584599240677068917519539)
  ·
    refine ⟨143376898861015603376279309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95584599240677068917519539 143376898861015603376279309)
    ·
      refine ⟨53766337072880851266104741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143376898861015603376279309 53766337072880851266104741)
      ·
        refine ⟨10081188201165159612394639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53766337072880851266104741 10081188201165159612394639)
        ·
          refine ⟨15121782301747739418591959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10081188201165159612394639 15121782301747739418591959)
          ·
            refine ⟨22682673452621609127887939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15121782301747739418591959 22682673452621609127887939)
            ·
              refine ⟨34024010178932413691831909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22682673452621609127887939 34024010178932413691831909)
              ·
                refine ⟨6379501908549827567218483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34024010178932413691831909 6379501908549827567218483)
                ·
                  refine ⟨9569252862824741350827725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6379501908549827567218483 9569252862824741350827725)
                  ·
                    refine ⟨3588469823559278006560397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9569252862824741350827725 3588469823559278006560397)
                    ·
                      refine ⟨1345676183834729252460149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3588469823559278006560397 1345676183834729252460149)
                      ·
                        rfl

theorem cell23_2620695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_2620695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620695 prefixEnd_2620695 := by exact prefixLift 2620695
  have htrace : WordTrace (prefixWord ++ tailWord_2620695) baseStart_2620695 baseEnd_2620695 := by
    simpa [prefixWord, tailWord_2620695, baseEnd_2620695] using wordTrace_append hprefix tailTrace_2620695
  have hstable : (prefixWord ++ tailWord_2620695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620695).length < 2 ^ (prefixWord ++ tailWord_2620695).sum := by decide
  have hdescent : baseEnd_2620695 < baseStart_2620695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620696 : List Nat := [2, 1, 2, 3, 1, 4, 2, 3, 1, 2, 2]
def baseStart_2620696 : Nat := 118140960795 + 2620696 * 2 ^ 59
def prefixEnd_2620696 : Nat := 4983230072969 + 3 ^ 40 * 2620696 * 2
def baseEnd_2620696 : Nat := 1345676697315383748547645

theorem tailTrace_2620696 : CollatzResearch.WordTrace tailWord_2620696 prefixEnd_2620696 1345676697315383748547645 := by
  unfold tailWord_2620696
  simp only [CollatzResearch.WordTrace]
  refine ⟨47792317856836723044152971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63723090475782297392203961 47792317856836723044152971)
  ·
    refine ⟨71688476785255084566229457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47792317856836723044152971 71688476785255084566229457)
    ·
      refine ⟨53766357588941313424672093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71688476785255084566229457 53766357588941313424672093)
      ·
        refine ⟨20162384095852992534252035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53766357588941313424672093 20162384095852992534252035)
        ·
          refine ⟨30243576143779488801378053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20162384095852992534252035 30243576143779488801378053)
          ·
            refine ⟨5670670526958654150258385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30243576143779488801378053 5670670526958654150258385)
            ·
              refine ⟨4253002895218990612693789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5670670526958654150258385 4253002895218990612693789)
              ·
                refine ⟨1594876085707121479760171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4253002895218990612693789 1594876085707121479760171)
                ·
                  refine ⟨2392314128560682219640257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594876085707121479760171 2392314128560682219640257)
                  ·
                    refine ⟨1794235596420511664730193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2392314128560682219640257 1794235596420511664730193)
                    ·
                      refine ⟨1345676697315383748547645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1794235596420511664730193 1345676697315383748547645)
                      ·
                        rfl

theorem cell23_2620696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_2620696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620696 prefixEnd_2620696 := by exact prefixLift 2620696
  have htrace : WordTrace (prefixWord ++ tailWord_2620696) baseStart_2620696 baseEnd_2620696 := by
    simpa [prefixWord, tailWord_2620696, baseEnd_2620696] using wordTrace_append hprefix tailTrace_2620696
  have hstable : (prefixWord ++ tailWord_2620696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620696).length < 2 ^ (prefixWord ++ tailWord_2620696).sum := by decide
  have hdescent : baseEnd_2620696 < baseStart_2620696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620702 : List Nat := [4, 3, 2, 1, 2, 1, 10]
def baseStart_2620702 : Nat := 118140960795 + 2620702 * 2 ^ 59
def prefixEnd_2620702 : Nat := 4983230072969 + 3 ^ 40 * 2620702 * 2
def baseEnd_2620702 : Nat := 16613330595053218828057

theorem tailTrace_2620702 : CollatzResearch.WordTrace tailWord_2620702 prefixEnd_2620702 16613330595053218828057 := by
  unfold tailWord_2620702
  simp only [CollatzResearch.WordTrace]
  refine ⟨11948106818956463639128045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63723236367767806075349573 11948106818956463639128045)
  ·
    refine ⟨4480540057108673864673017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11948106818956463639128045 4480540057108673864673017)
    ·
      refine ⟨3360405042831505398504763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4480540057108673864673017 3360405042831505398504763)
      ·
        refine ⟨5040607564247258097757145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3360405042831505398504763 5040607564247258097757145)
        ·
          refine ⟨3780455673185443573317859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5040607564247258097757145 3780455673185443573317859)
          ·
            refine ⟨5670683509778165359976789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3780455673185443573317859 5670683509778165359976789)
            ·
              refine ⟨16613330595053218828057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5670683509778165359976789 16613330595053218828057)
              ·
                rfl

theorem cell23_2620702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 10].length) (baseStart_2620702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620702 prefixEnd_2620702 := by exact prefixLift 2620702
  have htrace : WordTrace (prefixWord ++ tailWord_2620702) baseStart_2620702 baseEnd_2620702 := by
    simpa [prefixWord, tailWord_2620702, baseEnd_2620702] using wordTrace_append hprefix tailTrace_2620702
  have hstable : (prefixWord ++ tailWord_2620702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620702).length < 2 ^ (prefixWord ++ tailWord_2620702).sum := by decide
  have hdescent : baseEnd_2620702 < baseStart_2620702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620706 : List Nat := [3, 3, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_2620706 : Nat := 118140960795 + 2620706 * 2 ^ 59
def prefixEnd_2620706 : Nat := 4983230072969 + 3 ^ 40 * 2620706 * 2
def baseEnd_2620706 : Nat := 448560610707309569807533

theorem tailTrace_2620706 : CollatzResearch.WordTrace tailWord_2620706 prefixEnd_2620706 448560610707309569807533 := by
  unfold tailWord_2620706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23896250110909304449042493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63723333629091478530779981 23896250110909304449042493)
  ·
    refine ⟨8961093791590989168390935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23896250110909304449042493 8961093791590989168390935)
    ·
      refine ⟨13441640687386483752586403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8961093791590989168390935 13441640687386483752586403)
      ·
        refine ⟨20162461031079725628879605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13441640687386483752586403 20162461031079725628879605)
        ·
          refine ⟨1890230721663724277707463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20162461031079725628879605 1890230721663724277707463)
          ·
            refine ⟨2835346082495586416561195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890230721663724277707463 2835346082495586416561195)
            ·
              refine ⟨4253019123743379624841793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835346082495586416561195 4253019123743379624841793)
              ·
                refine ⟨3189764342807534718631345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4253019123743379624841793 3189764342807534718631345)
                ·
                  refine ⟨2392323257105651038973509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3189764342807534718631345 2392323257105651038973509)
                  ·
                    refine ⟨448560610707309569807533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2392323257105651038973509 448560610707309569807533)
                    ·
                      rfl

theorem cell23_2620706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_2620706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620706 prefixEnd_2620706 := by exact prefixLift 2620706
  have htrace : WordTrace (prefixWord ++ tailWord_2620706) baseStart_2620706 baseEnd_2620706 := by
    simpa [prefixWord, tailWord_2620706, baseEnd_2620706] using wordTrace_append hprefix tailTrace_2620706
  have hstable : (prefixWord ++ tailWord_2620706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620706).length < 2 ^ (prefixWord ++ tailWord_2620706).sum := by decide
  have hdescent : baseEnd_2620706 < baseStart_2620706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620726 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2620726 : Nat := 118140960795 + 2620726 * 2 ^ 59
def prefixEnd_2620726 : Nat := 4983230072969 + 3 ^ 40 * 2620726 * 2
def baseEnd_2620726 : Nat := 1345692101735018631172507

theorem tailTrace_2620726 : CollatzResearch.WordTrace tailWord_2620726 prefixEnd_2620726 1345692101735018631172507 := by
  unfold tailWord_2620726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5974108118972797575743627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63723819935709840807932021 5974108118972797575743627)
  ·
    refine ⟨8961162178459196363615441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5974108118972797575743627 8961162178459196363615441)
    ·
      refine ⟨6720871633844397272711581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8961162178459196363615441 6720871633844397272711581)
      ·
        refine ⟨2520326862691648977266843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6720871633844397272711581 2520326862691648977266843)
        ·
          refine ⟨3780490294037473465900265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2520326862691648977266843 3780490294037473465900265)
          ·
            refine ⟨2835367720528105099425199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3780490294037473465900265 2835367720528105099425199)
            ·
              refine ⟨4253051580792157649137799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835367720528105099425199 4253051580792157649137799)
              ·
                refine ⟨6379577371188236473706699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4253051580792157649137799 6379577371188236473706699)
                ·
                  refine ⟨9569366056782354710560049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6379577371188236473706699 9569366056782354710560049)
                  ·
                    refine ⟨7177024542586766032920037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9569366056782354710560049 7177024542586766032920037)
                    ·
                      refine ⟨1345692101735018631172507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7177024542586766032920037 1345692101735018631172507)
                      ·
                        rfl

theorem cell23_2620726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2620726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620726 prefixEnd_2620726 := by exact prefixLift 2620726
  have htrace : WordTrace (prefixWord ++ tailWord_2620726) baseStart_2620726 baseEnd_2620726 := by
    simpa [prefixWord, tailWord_2620726, baseEnd_2620726] using wordTrace_append hprefix tailTrace_2620726
  have hstable : (prefixWord ++ tailWord_2620726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620726).length < 2 ^ (prefixWord ++ tailWord_2620726).sum := by decide
  have hdescent : baseEnd_2620726 < baseStart_2620726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620729 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2620729 : Nat := 118140960795 + 2620729 * 2 ^ 59
def prefixEnd_2620729 : Nat := 4983230072969 + 3 ^ 40 * 2620729 * 2
def baseEnd_2620729 : Nat := 1345693642176982119434993

theorem tailTrace_2620729 : CollatzResearch.WordTrace tailWord_2620729 prefixEnd_2620729 1345693642176982119434993 := by
  unfold tailWord_2620729
  simp only [CollatzResearch.WordTrace]
  refine ⟨95585839322553892724257241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63723892881702595149504827 95585839322553892724257241)
  ·
    refine ⟨71689379491915419543192931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95585839322553892724257241 71689379491915419543192931)
    ·
      refine ⟨107534069237873129314789397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71689379491915419543192931 107534069237873129314789397)
      ·
        refine ⟨5040659495525302936630753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107534069237873129314789397 5040659495525302936630753)
        ·
          refine ⟨3780494621643977202473065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5040659495525302936630753 3780494621643977202473065)
          ·
            refine ⟨2835370966232982901854799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3780494621643977202473065 2835370966232982901854799)
            ·
              refine ⟨4253056449349474352782199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835370966232982901854799 4253056449349474352782199)
              ·
                refine ⟨6379584674024211529173299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4253056449349474352782199 6379584674024211529173299)
                ·
                  refine ⟨9569377011036317293759949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6379584674024211529173299 9569377011036317293759949)
                  ·
                    refine ⟨3588516379138618985159981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9569377011036317293759949 3588516379138618985159981)
                    ·
                      refine ⟨1345693642176982119434993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3588516379138618985159981 1345693642176982119434993)
                      ·
                        rfl

theorem cell23_2620729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2620729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620729 prefixEnd_2620729 := by exact prefixLift 2620729
  have htrace : WordTrace (prefixWord ++ tailWord_2620729) baseStart_2620729 baseEnd_2620729 := by
    simpa [prefixWord, tailWord_2620729, baseEnd_2620729] using wordTrace_append hprefix tailTrace_2620729
  have hstable : (prefixWord ++ tailWord_2620729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620729).length < 2 ^ (prefixWord ++ tailWord_2620729).sum := by decide
  have hdescent : baseEnd_2620729 < baseStart_2620729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620752 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 6, 2, 2]
def baseStart_2620752 : Nat := 118140960795 + 2620752 * 2 ^ 59
def prefixEnd_2620752 : Nat := 4983230072969 + 3 ^ 40 * 2620752 * 2
def baseEnd_2620752 : Nat := 1345705452232035529447387

theorem tailTrace_2620752 : CollatzResearch.WordTrace tailWord_2620752 prefixEnd_2620752 1345705452232035529447387 := by
  unfold tailWord_2620752
  simp only [CollatzResearch.WordTrace]
  refine ⟨47793339100735283826172255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63724452134313711768229673 47793339100735283826172255)
  ·
    refine ⟨71690008651102925739258383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47793339100735283826172255 71690008651102925739258383)
    ·
      refine ⟨107535012976654388608887575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71690008651102925739258383 107535012976654388608887575)
      ·
        refine ⟨161302519464981582913331363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107535012976654388608887575 161302519464981582913331363)
        ·
          refine ⟨241953779197472374369997045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161302519464981582913331363 241953779197472374369997045)
          ·
            refine ⟨22683166799763035097187223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 241953779197472374369997045 22683166799763035097187223)
            ·
              refine ⟨34024750199644552645780835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22683166799763035097187223 34024750199644552645780835)
              ·
                refine ⟨51037125299466828968671253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34024750199644552645780835 51037125299466828968671253)
                ·
                  refine ⟨2392365248412507607906465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51037125299466828968671253 2392365248412507607906465)
                  ·
                    refine ⟨1794273936309380705929849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2392365248412507607906465 1794273936309380705929849)
                    ·
                      refine ⟨1345705452232035529447387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1794273936309380705929849 1345705452232035529447387)
                      ·
                        rfl

theorem cell23_2620752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 6, 2, 2].length) (baseStart_2620752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620752 prefixEnd_2620752 := by exact prefixLift 2620752
  have htrace : WordTrace (prefixWord ++ tailWord_2620752) baseStart_2620752 baseEnd_2620752 := by
    simpa [prefixWord, tailWord_2620752, baseEnd_2620752] using wordTrace_append hprefix tailTrace_2620752
  have hstable : (prefixWord ++ tailWord_2620752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620752).length < 2 ^ (prefixWord ++ tailWord_2620752).sum := by decide
  have hdescent : baseEnd_2620752 < baseStart_2620752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620785 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 2, 3, 3]
def baseStart_2620785 : Nat := 118140960795 + 2620785 * 2 ^ 59
def prefixEnd_2620785 : Nat := 4983230072969 + 3 ^ 40 * 2620785 * 2
def baseEnd_2620785 : Nat := 1345722397093633900334735

theorem tailTrace_2620785 : CollatzResearch.WordTrace tailWord_2620785 prefixEnd_2620785 1345722397093633900334735 := by
  unfold tailWord_2620785
  simp only [CollatzResearch.WordTrace]
  refine ⟨95587881810351014288295809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63725254540234009525530539 95587881810351014288295809)
  ·
    refine ⟨71690911357763260716221857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95587881810351014288295809 71690911357763260716221857)
    ·
      refine ⟨53768183518322445537166393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71690911357763260716221857 53768183518322445537166393)
      ·
        refine ⟨40326137638741834152874795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53768183518322445537166393 40326137638741834152874795)
        ·
          refine ⟨60489206458112751229312193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40326137638741834152874795 60489206458112751229312193)
          ·
            refine ⟨45366904843584563421984145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60489206458112751229312193 45366904843584563421984145)
            ·
              refine ⟨34025178632688422566488109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45366904843584563421984145 34025178632688422566488109)
              ·
                refine ⟨12759441987258158462433041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34025178632688422566488109 12759441987258158462433041)
                ·
                  refine ⟨9569581490443618846824781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12759441987258158462433041 9569581490443618846824781)
                  ·
                    refine ⟨3588593058916357067559293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9569581490443618846824781 3588593058916357067559293)
                    ·
                      refine ⟨1345722397093633900334735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3588593058916357067559293 1345722397093633900334735)
                      ·
                        rfl

theorem cell23_2620785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_2620785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620785 prefixEnd_2620785 := by exact prefixLift 2620785
  have htrace : WordTrace (prefixWord ++ tailWord_2620785) baseStart_2620785 baseEnd_2620785 := by
    simpa [prefixWord, tailWord_2620785, baseEnd_2620785] using wordTrace_append hprefix tailTrace_2620785
  have hstable : (prefixWord ++ tailWord_2620785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620785).length < 2 ^ (prefixWord ++ tailWord_2620785).sum := by decide
  have hdescent : baseEnd_2620785 < baseStart_2620785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620805 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 2, 5]
def baseStart_2620805 : Nat := 118140960795 + 2620805 * 2 ^ 59
def prefixEnd_2620805 : Nat := 4983230072969 + 3 ^ 40 * 2620805 * 2
def baseEnd_2620805 : Nat := 448577555568907940694881

theorem tailTrace_2620805 : CollatzResearch.WordTrace tailWord_2620805 prefixEnd_2620805 448577555568907940694881 := by
  unfold tailWord_2620805
  simp only [CollatzResearch.WordTrace]
  refine ⟨95588611270278557704023869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63725740846852371802682579 95588611270278557704023869)
  ·
    refine ⟨35845729226354459139008951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95588611270278557704023869 35845729226354459139008951)
    ·
      refine ⟨53768593839531688708513427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35845729226354459139008951 53768593839531688708513427)
      ·
        refine ⟨80652890759297533062770141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53768593839531688708513427 80652890759297533062770141)
        ·
          refine ⟨30244834034736574898538803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80652890759297533062770141 30244834034736574898538803)
          ·
            refine ⟨45367251052104862347808205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30244834034736574898538803 45367251052104862347808205)
            ·
              refine ⟨17012719144539323380428077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45367251052104862347808205 17012719144539323380428077)
              ·
                refine ⟨6379769679202246267660529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17012719144539323380428077 6379769679202246267660529)
                ·
                  refine ⟨4784827259401684700745397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6379769679202246267660529 4784827259401684700745397)
                  ·
                    refine ⟨448577555568907940694881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4784827259401684700745397 448577555568907940694881)
                    ·
                      rfl

theorem cell23_2620805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_2620805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620805 prefixEnd_2620805 := by exact prefixLift 2620805
  have htrace : WordTrace (prefixWord ++ tailWord_2620805) baseStart_2620805 baseEnd_2620805 := by
    simpa [prefixWord, tailWord_2620805, baseEnd_2620805] using wordTrace_append hprefix tailTrace_2620805
  have hstable : (prefixWord ++ tailWord_2620805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620805).length < 2 ^ (prefixWord ++ tailWord_2620805).sum := by decide
  have hdescent : baseEnd_2620805 < baseStart_2620805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620885 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2620885 : Nat := 118140960795 + 2620885 * 2 ^ 59
def prefixEnd_2620885 : Nat := 4983230072969 + 3 ^ 40 * 2620885 * 2
def baseEnd_2620885 : Nat := 1345773745159083509084275

theorem tailTrace_2620885 : CollatzResearch.WordTrace tailWord_2620885 prefixEnd_2620885 1345773745159083509084275 := by
  unfold tailWord_2620885
  simp only [CollatzResearch.WordTrace]
  refine ⟨95591529109988731366936109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63727686073325820911290739 95591529109988731366936109)
  ·
    refine ⟨35846823416245774262601041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95591529109988731366936109 35846823416245774262601041)
    ·
      refine ⟨26885117562184330696950781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35846823416245774262601041 26885117562184330696950781)
      ·
        refine ⟨10081919085819124011356543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26885117562184330696950781 10081919085819124011356543)
        ·
          refine ⟨15122878628728686017034815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10081919085819124011356543 15122878628728686017034815)
          ·
            refine ⟨22684317943093029025552223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15122878628728686017034815 22684317943093029025552223)
            ·
              refine ⟨34026476914639543538328335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22684317943093029025552223 34026476914639543538328335)
              ·
                refine ⟨51039715371959315307492503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34026476914639543538328335 51039715371959315307492503)
                ·
                  refine ⟨76559573057938972961238755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51039715371959315307492503 76559573057938972961238755)
                  ·
                    refine ⟨114839359586908459441858133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76559573057938972961238755 114839359586908459441858133)
                    ·
                      refine ⟨1345773745159083509084275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 114839359586908459441858133 1345773745159083509084275)
                      ·
                        rfl

theorem cell23_2620885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2620885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620885 prefixEnd_2620885 := by exact prefixLift 2620885
  have htrace : WordTrace (prefixWord ++ tailWord_2620885) baseStart_2620885 baseEnd_2620885 := by
    simpa [prefixWord, tailWord_2620885, baseEnd_2620885] using wordTrace_append hprefix tailTrace_2620885
  have hstable : (prefixWord ++ tailWord_2620885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620885).length < 2 ^ (prefixWord ++ tailWord_2620885).sum := by decide
  have hdescent : baseEnd_2620885 < baseStart_2620885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620886 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_2620886 : Nat := 118140960795 + 2620886 * 2 ^ 59
def prefixEnd_2620886 : Nat := 4983230072969 + 3 ^ 40 * 2620886 * 2
def baseEnd_2620886 : Nat := 448591419546579335057257

theorem tailTrace_2620886 : CollatzResearch.WordTrace tailWord_2620886 prefixEnd_2620886 448591419546579335057257 := by
  unfold tailWord_2620886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5974472848936569283607657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63727710388656739025148341 5974472848936569283607657)
  ·
    refine ⟨4480854636702426962705743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5974472848936569283607657 4480854636702426962705743)
    ·
      refine ⟨6721281955053640444058615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4480854636702426962705743 6721281955053640444058615)
      ·
        refine ⟨10081922932580460666087923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6721281955053640444058615 10081922932580460666087923)
        ·
          refine ⟨15122884398870690999131885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10081922932580460666087923 15122884398870690999131885)
          ·
            refine ⟨5671081649576509124674457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15122884398870690999131885 5671081649576509124674457)
            ·
              refine ⟨4253311237182381843505843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5671081649576509124674457 4253311237182381843505843)
              ·
                refine ⟨6379966855773572765258765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4253311237182381843505843 6379966855773572765258765)
                ·
                  refine ⟨2392487570915089786972037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6379966855773572765258765 2392487570915089786972037)
                  ·
                    refine ⟨448591419546579335057257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2392487570915089786972037 448591419546579335057257)
                    ·
                      rfl

theorem cell23_2620886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_2620886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620886 prefixEnd_2620886 := by exact prefixLift 2620886
  have htrace : WordTrace (prefixWord ++ tailWord_2620886) baseStart_2620886 baseEnd_2620886 := by
    simpa [prefixWord, tailWord_2620886, baseEnd_2620886] using wordTrace_append hprefix tailTrace_2620886
  have hstable : (prefixWord ++ tailWord_2620886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620886).length < 2 ^ (prefixWord ++ tailWord_2620886).sum := by decide
  have hdescent : baseEnd_2620886 < baseStart_2620886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620899 : List Nat := [1, 1, 1, 6, 2, 2, 3, 1, 6]
def baseStart_2620899 : Nat := 118140960795 + 2620899 * 2 ^ 59
def prefixEnd_2620899 : Nat := 4983230072969 + 3 ^ 40 * 2620899 * 2
def baseEnd_2620899 : Nat := 149531214876471828256579

theorem tailTrace_2620899 : CollatzResearch.WordTrace tailWord_2620899 prefixEnd_2620899 149531214876471828256579 := by
  unfold tailWord_2620899
  simp only [CollatzResearch.WordTrace]
  refine ⟨95592039731938011757945751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63728026487958674505297167 95592039731938011757945751)
  ·
    refine ⟨143388059597907017636918627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95592039731938011757945751 143388059597907017636918627)
    ·
      refine ⟨215082089396860526455377941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143388059597907017636918627 215082089396860526455377941)
      ·
        refine ⟨10081972940477837177595841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 215082089396860526455377941 10081972940477837177595841)
        ·
          refine ⟨7561479705358377883196881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10081972940477837177595841 7561479705358377883196881)
          ·
            refine ⟨5671109779018783412397661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7561479705358377883196881 5671109779018783412397661)
            ·
              refine ⟨2126666167132043779649123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5671109779018783412397661 2126666167132043779649123)
              ·
                refine ⟨3189999250698065669473685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2126666167132043779649123 3189999250698065669473685)
                ·
                  refine ⟨149531214876471828256579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3189999250698065669473685 149531214876471828256579)
                  ·
                    rfl

theorem cell23_2620899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 6].length) (baseStart_2620899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620899 prefixEnd_2620899 := by exact prefixLift 2620899
  have htrace : WordTrace (prefixWord ++ tailWord_2620899) baseStart_2620899 baseEnd_2620899 := by
    simpa [prefixWord, tailWord_2620899, baseEnd_2620899] using wordTrace_append hprefix tailTrace_2620899
  have hstable : (prefixWord ++ tailWord_2620899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620899).length < 2 ^ (prefixWord ++ tailWord_2620899).sum := by decide
  have hdescent : baseEnd_2620899 < baseStart_2620899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620912 : List Nat := [2, 1, 1, 1, 3, 4, 1, 4, 1, 5]
def baseStart_2620912 : Nat := 118140960795 + 2620912 * 2 ^ 59
def prefixEnd_2620912 : Nat := 4983230072969 + 3 ^ 40 * 2620912 * 2
def baseEnd_2620912 : Nat := 448595869712251634482217

theorem tailTrace_2620912 : CollatzResearch.WordTrace tailWord_2620912 prefixEnd_2620912 448595869712251634482217 := by
  unfold tailWord_2620912
  simp only [CollatzResearch.WordTrace]
  refine ⟨47796256940445457489084495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63728342587260609985445993 47796256940445457489084495)
  ·
    refine ⟨71694385410668186233626743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47796256940445457489084495 71694385410668186233626743)
    ·
      refine ⟨107541578116002279350440115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71694385410668186233626743 107541578116002279350440115)
      ·
        refine ⟨161312367174003419025660173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107541578116002279350440115 161312367174003419025660173)
        ·
          refine ⟨60492137690251282134622565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161312367174003419025660173 60492137690251282134622565)
          ·
            refine ⟨11342275816922115400241731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60492137690251282134622565 11342275816922115400241731)
            ·
              refine ⟨17013413725383173100362597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11342275816922115400241731 17013413725383173100362597)
              ·
                refine ⟨3190015073509344956317987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17013413725383173100362597 3190015073509344956317987)
                ·
                  refine ⟨4785022610264017434476981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3190015073509344956317987 4785022610264017434476981)
                  ·
                    refine ⟨448595869712251634482217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4785022610264017434476981 448595869712251634482217)
                    ·
                      rfl

theorem cell23_2620912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 1, 5].length) (baseStart_2620912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620912 prefixEnd_2620912 := by exact prefixLift 2620912
  have htrace : WordTrace (prefixWord ++ tailWord_2620912) baseStart_2620912 baseEnd_2620912 := by
    simpa [prefixWord, tailWord_2620912, baseEnd_2620912] using wordTrace_append hprefix tailTrace_2620912
  have hstable : (prefixWord ++ tailWord_2620912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620912).length < 2 ^ (prefixWord ++ tailWord_2620912).sum := by decide
  have hdescent : baseEnd_2620912 < baseStart_2620912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620945 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_2620945 : Nat := 118140960795 + 2620945 * 2 ^ 59
def prefixEnd_2620945 : Nat := 4983230072969 + 3 ^ 40 * 2620945 * 2
def baseEnd_2620945 : Nat := 1345804553998353274333999

theorem tailTrace_2620945 : CollatzResearch.WordTrace tailWord_2620945 prefixEnd_2620945 1345804553998353274333999 := by
  unfold tailWord_2620945
  simp only [CollatzResearch.WordTrace]
  refine ⟨95593717489771361614120289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63729144993180907742746859 95593717489771361614120289)
  ·
    refine ⟨71695288117328521210590217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95593717489771361614120289 71695288117328521210590217)
    ·
      refine ⟨53771466087996390907942663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71695288117328521210590217 53771466087996390907942663)
      ·
        refine ⟨80657199131994586361913995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53771466087996390907942663 80657199131994586361913995)
        ·
          refine ⟨120985798697991879542870993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80657199131994586361913995 120985798697991879542870993)
          ·
            refine ⟨90739349023493909657153245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120985798697991879542870993 90739349023493909657153245)
            ·
              refine ⟨34027255883810216121432467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90739349023493909657153245 34027255883810216121432467)
              ·
                refine ⟨51040883825715324182148701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34027255883810216121432467 51040883825715324182148701)
                ·
                  refine ⟨19140331434643246568305763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51040883825715324182148701 19140331434643246568305763)
                  ·
                    refine ⟨28710497151964869852458645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19140331434643246568305763 28710497151964869852458645)
                    ·
                      refine ⟨1345804553998353274333999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28710497151964869852458645 1345804553998353274333999)
                      ·
                        rfl

theorem cell23_2620945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_2620945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620945 prefixEnd_2620945 := by exact prefixLift 2620945
  have htrace : WordTrace (prefixWord ++ tailWord_2620945) baseStart_2620945 baseEnd_2620945 := by
    simpa [prefixWord, tailWord_2620945, baseEnd_2620945] using wordTrace_append hprefix tailTrace_2620945
  have hstable : (prefixWord ++ tailWord_2620945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620945).length < 2 ^ (prefixWord ++ tailWord_2620945).sum := by decide
  have hdescent : baseEnd_2620945 < baseStart_2620945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620962 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_2620962 : Nat := 118140960795 + 2620962 * 2 ^ 59
def prefixEnd_2620962 : Nat := 4983230072969 + 3 ^ 40 * 2620962 * 2
def baseEnd_2620962 : Nat := 1345813283169479707821421

theorem tailTrace_2620962 : CollatzResearch.WordTrace tailWord_2620962 prefixEnd_2620962 1345813283169479707821421 := by
  unfold tailWord_2620962
  simp only [CollatzResearch.WordTrace]
  refine ⟨23898584382677443379372285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63729558353806515678326093 23898584382677443379372285)
  ·
    refine ⟨8961969143504041267264607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23898584382677443379372285 8961969143504041267264607)
    ·
      refine ⟨13442953715256061900896911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8961969143504041267264607 13442953715256061900896911)
      ·
        refine ⟨20164430572884092851345367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13442953715256061900896911 20164430572884092851345367)
        ·
          refine ⟨30246645859326139277018051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20164430572884092851345367 30246645859326139277018051)
          ·
            refine ⟨45369968788989208915527077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30246645859326139277018051 45369968788989208915527077)
            ·
              refine ⟨8506869147935476671661327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45369968788989208915527077 8506869147935476671661327)
              ·
                refine ⟨12760303721903215007491991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8506869147935476671661327 12760303721903215007491991)
                ·
                  refine ⟨19140455582854822511237987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12760303721903215007491991 19140455582854822511237987)
                  ·
                    refine ⟨28710683374282233766856981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19140455582854822511237987 28710683374282233766856981)
                    ·
                      refine ⟨1345813283169479707821421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28710683374282233766856981 1345813283169479707821421)
                      ·
                        rfl

theorem cell23_2620962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_2620962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620962 prefixEnd_2620962 := by exact prefixLift 2620962
  have htrace : WordTrace (prefixWord ++ tailWord_2620962) baseStart_2620962 baseEnd_2620962 := by
    simpa [prefixWord, tailWord_2620962, baseEnd_2620962] using wordTrace_append hprefix tailTrace_2620962
  have hstable : (prefixWord ++ tailWord_2620962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620962).length < 2 ^ (prefixWord ++ tailWord_2620962).sum := by decide
  have hdescent : baseEnd_2620962 < baseStart_2620962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620986 : List Nat := [3, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3]
def baseStart_2620986 : Nat := 118140960795 + 2620986 * 2 ^ 59
def prefixEnd_2620986 : Nat := 4983230072969 + 3 ^ 40 * 2620986 * 2
def baseEnd_2620986 : Nat := 1345825606705187613921311

theorem tailTrace_2620986 : CollatzResearch.WordTrace tailWord_2620986 prefixEnd_2620986 1345825606705187613921311 := by
  unfold tailWord_2620986
  simp only [CollatzResearch.WordTrace]
  refine ⟨23898803220655706404090703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63730141921748550410908541 23898803220655706404090703)
  ·
    refine ⟨35848204830983559606136055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23898803220655706404090703 35848204830983559606136055)
    ·
      refine ⟨53772307246475339409204083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35848204830983559606136055 53772307246475339409204083)
      ·
        refine ⟨80658460869713009113806125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53772307246475339409204083 80658460869713009113806125)
        ·
          refine ⟨30246922826142378417677297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80658460869713009113806125 30246922826142378417677297)
          ·
            refine ⟨22685192119606783813257973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30246922826142378417677297 22685192119606783813257973)
            ·
              refine ⟨2126736761213135982492935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22685192119606783813257973 2126736761213135982492935)
              ·
                refine ⟨3190105141819703973739403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2126736761213135982492935 3190105141819703973739403)
                ·
                  refine ⟨4785157712729555960609105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3190105141819703973739403 4785157712729555960609105)
                  ·
                    refine ⟨3588868284547166970456829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4785157712729555960609105 3588868284547166970456829)
                    ·
                      refine ⟨1345825606705187613921311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3588868284547166970456829 1345825606705187613921311)
                      ·
                        rfl

theorem cell23_2620986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3].length) (baseStart_2620986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620986 prefixEnd_2620986 := by exact prefixLift 2620986
  have htrace : WordTrace (prefixWord ++ tailWord_2620986) baseStart_2620986 baseEnd_2620986 := by
    simpa [prefixWord, tailWord_2620986, baseEnd_2620986] using wordTrace_append hprefix tailTrace_2620986
  have hstable : (prefixWord ++ tailWord_2620986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620986).length < 2 ^ (prefixWord ++ tailWord_2620986).sum := by decide
  have hdescent : baseEnd_2620986 < baseStart_2620986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620995 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 7]
def baseStart_2620995 : Nat := 118140960795 + 2620995 * 2 ^ 59
def prefixEnd_2620995 : Nat := 4983230072969 + 3 ^ 40 * 2620995 * 2
def baseEnd_2620995 : Nat := 1345830228031078078708769

theorem tailTrace_2620995 : CollatzResearch.WordTrace tailWord_2620995 prefixEnd_2620995 1345830228031078078708769 := by
  unfold tailWord_2620995
  simp only [CollatzResearch.WordTrace]
  refine ⟨95595541139590220153440439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63730360759726813435626959 95595541139590220153440439)
  ·
    refine ⟨143393311709385330230160659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95595541139590220153440439 143393311709385330230160659)
    ·
      refine ⟨215089967564077995345240989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143393311709385330230160659 215089967564077995345240989)
      ·
        refine ⟨80658737836529248254465371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215089967564077995345240989 80658737836529248254465371)
        ·
          refine ⟨120988106754793872381698057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80658737836529248254465371 120988106754793872381698057)
          ·
            refine ⟨90741080066095404286273543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120988106754793872381698057 90741080066095404286273543)
            ·
              refine ⟨136111620099143106429410315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90741080066095404286273543 136111620099143106429410315)
              ·
                refine ⟨204167430148714659644115473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136111620099143106429410315 204167430148714659644115473)
                ·
                  refine ⟨153125572611535994733086605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204167430148714659644115473 153125572611535994733086605)
                  ·
                    refine ⟨57422089729325998024907477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153125572611535994733086605 57422089729325998024907477)
                    ·
                      refine ⟨1345830228031078078708769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57422089729325998024907477 1345830228031078078708769)
                      ·
                        rfl

theorem cell23_2620995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_2620995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2620995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2620995 prefixEnd_2620995 := by exact prefixLift 2620995
  have htrace : WordTrace (prefixWord ++ tailWord_2620995) baseStart_2620995 baseEnd_2620995 := by
    simpa [prefixWord, tailWord_2620995, baseEnd_2620995] using wordTrace_append hprefix tailTrace_2620995
  have hstable : (prefixWord ++ tailWord_2620995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620995).length < 2 ^ (prefixWord ++ tailWord_2620995).sum := by decide
  have hdescent : baseEnd_2620995 < baseStart_2620995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621009 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 5, 3, 2]
def baseStart_2621009 : Nat := 118140960795 + 2621009 * 2 ^ 59
def prefixEnd_2621009 : Nat := 4983230072969 + 3 ^ 40 * 2621009 * 2
def baseEnd_2621009 : Nat := 1345837416760241023933705

theorem tailTrace_2621009 : CollatzResearch.WordTrace tailWord_2621009 prefixEnd_2621009 1345837416760241023933705 := by
  unfold tailWord_2621009
  simp only [CollatzResearch.WordTrace]
  refine ⟨95596051761539500544450081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63730701174359667029633387 95596051761539500544450081)
  ·
    refine ⟨71697038821154625408337561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95596051761539500544450081 71697038821154625408337561)
    ·
      refine ⟨53772779115865969056253171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71697038821154625408337561 53772779115865969056253171)
      ·
        refine ⟨80659168673798953584379757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53772779115865969056253171 80659168673798953584379757)
        ·
          refine ⟨30247188252674607594142409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80659168673798953584379757 30247188252674607594142409)
          ·
            refine ⟨22685391189505955695606807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30247188252674607594142409 22685391189505955695606807)
            ·
              refine ⟨34028086784258933543410211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22685391189505955695606807 34028086784258933543410211)
              ·
                refine ⟨51042130176388400315115317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34028086784258933543410211 51042130176388400315115317)
                ·
                  refine ⟨4785199704036412529542061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51042130176388400315115317 4785199704036412529542061)
                  ·
                    refine ⟨1794449889013654698578273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4785199704036412529542061 1794449889013654698578273)
                    ·
                      refine ⟨1345837416760241023933705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1794449889013654698578273 1345837416760241023933705)
                      ·
                        rfl

theorem cell23_2621009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 3, 2].length) (baseStart_2621009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621009 prefixEnd_2621009 := by exact prefixLift 2621009
  have htrace : WordTrace (prefixWord ++ tailWord_2621009) baseStart_2621009 baseEnd_2621009 := by
    simpa [prefixWord, tailWord_2621009, baseEnd_2621009] using wordTrace_append hprefix tailTrace_2621009
  have hstable : (prefixWord ++ tailWord_2621009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621009).length < 2 ^ (prefixWord ++ tailWord_2621009).sum := by decide
  have hdescent : baseEnd_2621009 < baseStart_2621009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621056 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 4, 2, 2]
def baseStart_2621056 : Nat := 118140960795 + 2621056 * 2 ^ 59
def prefixEnd_2621056 : Nat := 4983230072969 + 3 ^ 40 * 2621056 * 2
def baseEnd_2621056 : Nat := 1345861550351002340045989

theorem tailTrace_2621056 : CollatzResearch.WordTrace tailWord_2621056 prefixEnd_2621056 1345861550351002340045989 := by
  unfold tailWord_2621056
  simp only [CollatzResearch.WordTrace]
  refine ⟨47798882996184613785705511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63731843994912818380940681 47798882996184613785705511)
  ·
    refine ⟨71698324494276920678558267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47798882996184613785705511 71698324494276920678558267)
    ·
      refine ⟨107547486741415381017837401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71698324494276920678558267 107547486741415381017837401)
      ·
        refine ⟨80660615056061535763378051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107547486741415381017837401 80660615056061535763378051)
        ·
          refine ⟨120990922584092303645067077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80660615056061535763378051 120990922584092303645067077)
          ·
            refine ⟨22685797984517306933450077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120990922584092303645067077 22685797984517306933450077)
            ·
              refine ⟨8507174244193990100043779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22685797984517306933450077 8507174244193990100043779)
              ·
                refine ⟨12760761366290985150065669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8507174244193990100043779 12760761366290985150065669)
                ·
                  refine ⟨2392642756179559715637313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12760761366290985150065669 2392642756179559715637313)
                  ·
                    refine ⟨1794482067134669786727985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2392642756179559715637313 1794482067134669786727985)
                    ·
                      refine ⟨1345861550351002340045989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1794482067134669786727985 1345861550351002340045989)
                      ·
                        rfl

theorem cell23_2621056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 4, 2, 2].length) (baseStart_2621056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621056 prefixEnd_2621056 := by exact prefixLift 2621056
  have htrace : WordTrace (prefixWord ++ tailWord_2621056) baseStart_2621056 baseEnd_2621056 := by
    simpa [prefixWord, tailWord_2621056, baseEnd_2621056] using wordTrace_append hprefix tailTrace_2621056
  have hstable : (prefixWord ++ tailWord_2621056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621056).length < 2 ^ (prefixWord ++ tailWord_2621056).sum := by decide
  have hdescent : baseEnd_2621056 < baseStart_2621056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621146 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4]
def baseStart_2621146 : Nat := 118140960795 + 2621146 * 2 ^ 59
def prefixEnd_2621146 : Nat := 4983230072969 + 3 ^ 40 * 2621146 * 2
def baseEnd_2621146 : Nat := 1345907763609906987920575

theorem tailTrace_2621146 : CollatzResearch.WordTrace tailWord_2621146 prefixEnd_2621146 1345907763609906987920575 := by
  unfold tailWord_2621146
  simp only [CollatzResearch.WordTrace]
  refine ⟨23900262140510793235546823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63734032374695448628124861 23900262140510793235546823)
  ·
    refine ⟨35850393210766189853320235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23900262140510793235546823 35850393210766189853320235)
    ·
      refine ⟨53775589816149284779980353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35850393210766189853320235 53775589816149284779980353)
      ·
        refine ⟨40331692362111963584985265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53775589816149284779980353 40331692362111963584985265)
        ·
          refine ⟨30248769271583972688738949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40331692362111963584985265 30248769271583972688738949)
          ·
            refine ⟨5671644238421994879138553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30248769271583972688738949 5671644238421994879138553)
            ·
              refine ⟨4253733178816496159353915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5671644238421994879138553 4253733178816496159353915)
              ·
                refine ⟨6380599768224744239030873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4253733178816496159353915 6380599768224744239030873)
                ·
                  refine ⟨4785449826168558179273155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6380599768224744239030873 4785449826168558179273155)
                  ·
                    refine ⟨7178174739252837268909733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4785449826168558179273155 7178174739252837268909733)
                    ·
                      refine ⟨1345907763609906987920575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7178174739252837268909733 1345907763609906987920575)
                      ·
                        rfl

theorem cell23_2621146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_2621146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621146 prefixEnd_2621146 := by exact prefixLift 2621146
  have htrace : WordTrace (prefixWord ++ tailWord_2621146) baseStart_2621146 baseEnd_2621146 := by
    simpa [prefixWord, tailWord_2621146, baseEnd_2621146] using wordTrace_append hprefix tailTrace_2621146
  have hstable : (prefixWord ++ tailWord_2621146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621146).length < 2 ^ (prefixWord ++ tailWord_2621146).sum := by decide
  have hdescent : baseEnd_2621146 < baseStart_2621146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621152 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 10]
def baseStart_2621152 : Nat := 118140960795 + 2621152 * 2 ^ 59
def prefixEnd_2621152 : Nat := 4983230072969 + 3 ^ 40 * 2621152 * 2
def baseEnd_2621152 : Nat := 149545649388203773827283

theorem tailTrace_2621152 : CollatzResearch.WordTrace tailWord_2621152 prefixEnd_2621152 149545649388203773827283 := by
  unfold tailWord_2621152
  simp only [CollatzResearch.WordTrace]
  refine ⟨47800633700010717983452855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63734178266680957311270473 47800633700010717983452855)
  ·
    refine ⟨71700950550016076975179283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47800633700010717983452855 71700950550016076975179283)
    ·
      refine ⟨107551425825024115462768925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71700950550016076975179283 107551425825024115462768925)
      ·
        refine ⟨40331784684384043298538347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107551425825024115462768925 40331784684384043298538347)
        ·
          refine ⟨60497677026576064947807521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40331784684384043298538347 60497677026576064947807521)
          ·
            refine ⟨45373257769932048710855641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60497677026576064947807521 45373257769932048710855641)
            ·
              refine ⟨34029943327449036533141731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45373257769932048710855641 34029943327449036533141731)
              ·
                refine ⟨51044914991173554799712597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34029943327449036533141731 51044914991173554799712597)
                ·
                  refine ⟨149545649388203773827283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 51044914991173554799712597 149545649388203773827283)
                  ·
                    rfl

theorem cell23_2621152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 10].length) (baseStart_2621152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621152 prefixEnd_2621152 := by exact prefixLift 2621152
  have htrace : WordTrace (prefixWord ++ tailWord_2621152) baseStart_2621152 baseEnd_2621152 := by
    simpa [prefixWord, tailWord_2621152, baseEnd_2621152] using wordTrace_append hprefix tailTrace_2621152
  have hstable : (prefixWord ++ tailWord_2621152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621152).length < 2 ^ (prefixWord ++ tailWord_2621152).sum := by decide
  have hdescent : baseEnd_2621152 < baseStart_2621152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621166 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_2621166 : Nat := 118140960795 + 2621166 * 2 ^ 59
def prefixEnd_2621166 : Nat := 4983230072969 + 3 ^ 40 * 2621166 * 2
def baseEnd_2621166 : Nat := 1345918033222996909670483

theorem tailTrace_2621166 : CollatzResearch.WordTrace tailWord_2621166 prefixEnd_2621166 1345918033222996909670483 := by
  unfold tailWord_2621166
  simp only [CollatzResearch.WordTrace]
  refine ⟨11950222252746339544739419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63734518681313810905276901 11950222252746339544739419)
  ·
    refine ⟨17925333379119509317109129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11950222252746339544739419 17925333379119509317109129)
    ·
      refine ⟨13444000034339631987831847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17925333379119509317109129 13444000034339631987831847)
      ·
        refine ⟨20166000051509447981747771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13444000034339631987831847 20166000051509447981747771)
        ·
          refine ⟨30249000077264171972621657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20166000051509447981747771 30249000077264171972621657)
          ·
            refine ⟨22686750057948128979466243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30249000077264171972621657 22686750057948128979466243)
            ·
              refine ⟨34030125086922193469199365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22686750057948128979466243 34030125086922193469199365)
              ·
                refine ⟨6380648453797911275474881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34030125086922193469199365 6380648453797911275474881)
                ·
                  refine ⟨4785486340348433456606161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6380648453797911275474881 4785486340348433456606161)
                  ·
                    refine ⟨3589114755261325092454621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4785486340348433456606161 3589114755261325092454621)
                    ·
                      refine ⟨1345918033222996909670483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3589114755261325092454621 1345918033222996909670483)
                      ·
                        rfl

theorem cell23_2621166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_2621166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621166 prefixEnd_2621166 := by exact prefixLift 2621166
  have htrace : WordTrace (prefixWord ++ tailWord_2621166) baseStart_2621166 baseEnd_2621166 := by
    simpa [prefixWord, tailWord_2621166, baseEnd_2621166] using wordTrace_append hprefix tailTrace_2621166
  have hstable : (prefixWord ++ tailWord_2621166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621166).length < 2 ^ (prefixWord ++ tailWord_2621166).sum := by decide
  have hdescent : baseEnd_2621166 < baseStart_2621166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621169 : List Nat := [1, 2, 2, 2, 2, 3, 1, 4, 6]
def baseStart_2621169 : Nat := 118140960795 + 2621169 * 2 ^ 59
def prefixEnd_2621169 : Nat := 4983230072969 + 3 ^ 40 * 2621169 * 2
def baseEnd_2621169 : Nat := 149546619296106710881441

theorem tailTrace_2621169 : CollatzResearch.WordTrace tailWord_2621169 prefixEnd_2621169 149546619296106710881441 := by
  unfold tailWord_2621169
  simp only [CollatzResearch.WordTrace]
  refine ⟨95601887440959847870274561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63734591627306565246849707 95601887440959847870274561)
  ·
    refine ⟨71701415580719885902705921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95601887440959847870274561 71701415580719885902705921)
    ·
      refine ⟨53776061685539914427029441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71701415580719885902705921 53776061685539914427029441)
      ·
        refine ⟨40332046264154935820272081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53776061685539914427029441 40332046264154935820272081)
        ·
          refine ⟨30249034698116201865204061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40332046264154935820272081 30249034698116201865204061)
          ·
            refine ⟨11343388011793575699451523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30249034698116201865204061 11343388011793575699451523)
            ·
              refine ⟨17015082017690363549177285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11343388011793575699451523 17015082017690363549177285)
              ·
                refine ⟨3190327878316943165470741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17015082017690363549177285 3190327878316943165470741)
                ·
                  refine ⟨149546619296106710881441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3190327878316943165470741 149546619296106710881441)
                  ·
                    rfl

theorem cell23_2621169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 6].length) (baseStart_2621169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621169 prefixEnd_2621169 := by exact prefixLift 2621169
  have htrace : WordTrace (prefixWord ++ tailWord_2621169) baseStart_2621169 baseEnd_2621169 := by
    simpa [prefixWord, tailWord_2621169, baseEnd_2621169] using wordTrace_append hprefix tailTrace_2621169
  have hstable : (prefixWord ++ tailWord_2621169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621169).length < 2 ^ (prefixWord ++ tailWord_2621169).sum := by decide
  have hdescent : baseEnd_2621169 < baseStart_2621169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621186 : List Nat := [3, 4, 1, 1, 1, 1, 1, 5, 6]
def baseStart_2621186 : Nat := 118140960795 + 2621186 * 2 ^ 59
def prefixEnd_2621186 : Nat := 4983230072969 + 3 ^ 40 * 2621186 * 2
def baseEnd_2621186 : Nat := 149547589204009647935599

theorem tailTrace_2621186 : CollatzResearch.WordTrace tailWord_2621186 prefixEnd_2621186 149547589204009647935599 := by
  unfold tailWord_2621186
  simp only [CollatzResearch.WordTrace]
  refine ⟨23900626870474564943410853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63735004987932173182428941 23900626870474564943410853)
  ·
    refine ⟨4481367538213980926889535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23900626870474564943410853 4481367538213980926889535)
    ·
      refine ⟨6722051307320971390334303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4481367538213980926889535 6722051307320971390334303)
      ·
        refine ⟨10083076960981457085501455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6722051307320971390334303 10083076960981457085501455)
        ·
          refine ⟨15124615441472185628252183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10083076960981457085501455 15124615441472185628252183)
          ·
            refine ⟨22686923162208278442378275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15124615441472185628252183 22686923162208278442378275)
            ·
              refine ⟨34030384743312417663567413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22686923162208278442378275 34030384743312417663567413)
              ·
                refine ⟨3190348569685539155959445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34030384743312417663567413 3190348569685539155959445)
                ·
                  refine ⟨149547589204009647935599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3190348569685539155959445 149547589204009647935599)
                  ·
                    rfl

theorem cell23_2621186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_2621186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621186 prefixEnd_2621186 := by exact prefixLift 2621186
  have htrace : WordTrace (prefixWord ++ tailWord_2621186) baseStart_2621186 baseEnd_2621186 := by
    simpa [prefixWord, tailWord_2621186, baseEnd_2621186] using wordTrace_append hprefix tailTrace_2621186
  have hstable : (prefixWord ++ tailWord_2621186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621186).length < 2 ^ (prefixWord ++ tailWord_2621186).sum := by decide
  have hdescent : baseEnd_2621186 < baseStart_2621186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621196 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 5, 1, 3]
def baseStart_2621196 : Nat := 118140960795 + 2621196 * 2 ^ 59
def prefixEnd_2621196 : Nat := 4983230072969 + 3 ^ 40 * 2621196 * 2
def baseEnd_2621196 : Nat := 1345933437642631792295345

theorem tailTrace_2621196 : CollatzResearch.WordTrace tailWord_2621196 prefixEnd_2621196 1345933437642631792295345 := by
  unfold tailWord_2621196
  simp only [CollatzResearch.WordTrace]
  refine ⟨47801436105931015740753721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63735248141241354321004961 47801436105931015740753721)
  ·
    refine ⟨35851077079448261805565291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47801436105931015740753721 35851077079448261805565291)
    ·
      refine ⟨53776615619172392708347937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35851077079448261805565291 53776615619172392708347937)
      ·
        refine ⟨40332461714379294531260953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53776615619172392708347937 40332461714379294531260953)
        ·
          refine ⟨30249346285784470898445715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40332461714379294531260953 30249346285784470898445715)
          ·
            refine ⟨45374019428676706347668573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30249346285784470898445715 45374019428676706347668573)
            ·
              refine ⟨17015257285753764880375715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45374019428676706347668573 17015257285753764880375715)
              ·
                refine ⟨25522885928630647320563573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17015257285753764880375715 25522885928630647320563573)
                ·
                  refine ⟨2392770555809123186302835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25522885928630647320563573 2392770555809123186302835)
                  ·
                    refine ⟨3589155833713684779454253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2392770555809123186302835 3589155833713684779454253)
                    ·
                      refine ⟨1345933437642631792295345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3589155833713684779454253 1345933437642631792295345)
                      ·
                        rfl

theorem cell23_2621196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_2621196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621196 prefixEnd_2621196 := by exact prefixLift 2621196
  have htrace : WordTrace (prefixWord ++ tailWord_2621196) baseStart_2621196 baseEnd_2621196 := by
    simpa [prefixWord, tailWord_2621196, baseEnd_2621196] using wordTrace_append hprefix tailTrace_2621196
  have hstable : (prefixWord ++ tailWord_2621196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621196).length < 2 ^ (prefixWord ++ tailWord_2621196).sum := by decide
  have hdescent : baseEnd_2621196 < baseStart_2621196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621197 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2621197 : Nat := 118140960795 + 2621197 * 2 ^ 59
def prefixEnd_2621197 : Nat := 4983230072969 + 3 ^ 40 * 2621197 * 2
def baseEnd_2621197 : Nat := 1345933951123286288382841

theorem tailTrace_2621197 : CollatzResearch.WordTrace tailWord_2621197 prefixEnd_2621197 1345933951123286288382841 := by
  unfold tailWord_2621197
  simp only [CollatzResearch.WordTrace]
  refine ⟨95602908684858408652293845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63735272456572272434862563 95602908684858408652293845)
  ·
    refine ⟨2240693172301368952788137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 95602908684858408652293845 2240693172301368952788137)
    ·
      refine ⟨1680519879226026714591103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2240693172301368952788137 1680519879226026714591103)
      ·
        refine ⟨2520779818839040071886655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680519879226026714591103 2520779818839040071886655)
        ·
          refine ⟨3781169728258560107829983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2520779818839040071886655 3781169728258560107829983)
          ·
            refine ⟨5671754592387840161744975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3781169728258560107829983 5671754592387840161744975)
            ·
              refine ⟨8507631888581760242617463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5671754592387840161744975 8507631888581760242617463)
              ·
                refine ⟨12761447832872640363926195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8507631888581760242617463 12761447832872640363926195)
                ·
                  refine ⟨19142171749308960545889293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12761447832872640363926195 19142171749308960545889293)
                  ·
                    refine ⟨7178314405990860204708485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19142171749308960545889293 7178314405990860204708485)
                    ·
                      refine ⟨1345933951123286288382841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7178314405990860204708485 1345933951123286288382841)
                      ·
                        rfl

theorem cell23_2621197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2621197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621197 prefixEnd_2621197 := by exact prefixLift 2621197
  have htrace : WordTrace (prefixWord ++ tailWord_2621197) baseStart_2621197 baseEnd_2621197 := by
    simpa [prefixWord, tailWord_2621197, baseEnd_2621197] using wordTrace_append hprefix tailTrace_2621197
  have hstable : (prefixWord ++ tailWord_2621197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621197).length < 2 ^ (prefixWord ++ tailWord_2621197).sum := by decide
  have hdescent : baseEnd_2621197 < baseStart_2621197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621216 : List Nat := [2, 1, 1, 5, 1, 1, 3, 3, 1, 5]
def baseStart_2621216 : Nat := 118140960795 + 2621216 * 2 ^ 59
def prefixEnd_2621216 : Nat := 4983230072969 + 3 ^ 40 * 2621216 * 2
def baseEnd_2621216 : Nat := 448647902418573904681751

theorem tailTrace_2621216 : CollatzResearch.WordTrace tailWord_2621216 prefixEnd_2621216 448647902418573904681751 := by
  unfold tailWord_2621216
  simp only [CollatzResearch.WordTrace]
  refine ⟨47801800835894787448617751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63735734447859716598157001 47801800835894787448617751)
  ·
    refine ⟨71702701253842181172926627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47801800835894787448617751 71702701253842181172926627)
    ·
      refine ⟨107554051880763271759389941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71702701253842181172926627 107554051880763271759389941)
      ·
        refine ⟨10083192363821556727442807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107554051880763271759389941 10083192363821556727442807)
        ·
          refine ⟨15124788545732335091164211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10083192363821556727442807 15124788545732335091164211)
          ·
            refine ⟨22687182818598502636746317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15124788545732335091164211 22687182818598502636746317)
            ·
              refine ⟨8507693556974438488779869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22687182818598502636746317 8507693556974438488779869)
              ·
                refine ⟨3190385083865414433292451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8507693556974438488779869 3190385083865414433292451)
                ·
                  refine ⟨4785577625798121649938677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3190385083865414433292451 4785577625798121649938677)
                  ·
                    refine ⟨448647902418573904681751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4785577625798121649938677 448647902418573904681751)
                    ·
                      rfl

theorem cell23_2621216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 1, 5].length) (baseStart_2621216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621216 prefixEnd_2621216 := by exact prefixLift 2621216
  have htrace : WordTrace (prefixWord ++ tailWord_2621216) baseStart_2621216 baseEnd_2621216 := by
    simpa [prefixWord, tailWord_2621216, baseEnd_2621216] using wordTrace_append hprefix tailTrace_2621216
  have hstable : (prefixWord ++ tailWord_2621216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621216).length < 2 ^ (prefixWord ++ tailWord_2621216).sum := by decide
  have hdescent : baseEnd_2621216 < baseStart_2621216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621239 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 3]
def baseStart_2621239 : Nat := 118140960795 + 2621239 * 2 ^ 59
def prefixEnd_2621239 : Nat := 4983230072969 + 3 ^ 40 * 2621239 * 2
def baseEnd_2621239 : Nat := 1345955517310775124057647

theorem tailTrace_2621239 : CollatzResearch.WordTrace tailWord_2621239 prefixEnd_2621239 1345955517310775124057647 := by
  unfold tailWord_2621239
  simp only [CollatzResearch.WordTrace]
  refine ⟨95604440550706249825322771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63736293700470833216881847 95604440550706249825322771)
  ·
    refine ⟨143406660826059374737984157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95604440550706249825322771 143406660826059374737984157)
    ·
      refine ⟨53777497809772265526744059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143406660826059374737984157 53777497809772265526744059)
      ·
        refine ⟨80666246714658398290116089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53777497809772265526744059 80666246714658398290116089)
        ·
          refine ⟨60499685035993798717587067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80666246714658398290116089 60499685035993798717587067)
          ·
            refine ⟨90749527553990698076380601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60499685035993798717587067 90749527553990698076380601)
            ·
              refine ⟨68062145665493023557285451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90749527553990698076380601 68062145665493023557285451)
              ·
                refine ⟨102093218498239535335928177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68062145665493023557285451 102093218498239535335928177)
                ·
                  refine ⟨76569913873679651501946133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102093218498239535335928177 76569913873679651501946133)
                  ·
                    refine ⟨3589214712828733664153725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76569913873679651501946133 3589214712828733664153725)
                    ·
                      refine ⟨1345955517310775124057647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3589214712828733664153725 1345955517310775124057647)
                      ·
                        rfl

theorem cell23_2621239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_2621239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621239 prefixEnd_2621239 := by exact prefixLift 2621239
  have htrace : WordTrace (prefixWord ++ tailWord_2621239) baseStart_2621239 baseEnd_2621239 := by
    simpa [prefixWord, tailWord_2621239, baseEnd_2621239] using wordTrace_append hprefix tailTrace_2621239
  have hstable : (prefixWord ++ tailWord_2621239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621239).length < 2 ^ (prefixWord ++ tailWord_2621239).sum := by decide
  have hdescent : baseEnd_2621239 < baseStart_2621239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621253 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 3, 2, 2]
def baseStart_2621253 : Nat := 118140960795 + 2621253 * 2 ^ 59
def prefixEnd_2621253 : Nat := 4983230072969 + 3 ^ 40 * 2621253 * 2
def baseEnd_2621253 : Nat := 1345962706039938069282583

theorem tailTrace_2621253 : CollatzResearch.WordTrace tailWord_2621253 prefixEnd_2621253 1345962706039938069282583 := by
  unfold tailWord_2621253
  simp only [CollatzResearch.WordTrace]
  refine ⟨95604951172655530216332413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63736634115103686810888275 95604951172655530216332413)
  ·
    refine ⟨35851856689745823831124655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95604951172655530216332413 35851856689745823831124655)
    ·
      refine ⟨53777785034618735746686983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35851856689745823831124655 53777785034618735746686983)
      ·
        refine ⟨80666677551928103620030475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53777785034618735746686983 80666677551928103620030475)
        ·
          refine ⟨121000016327892155430045713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80666677551928103620030475 121000016327892155430045713)
          ·
            refine ⟨90750012245919116572534285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121000016327892155430045713 90750012245919116572534285)
            ·
              refine ⟨34031254592219668714700357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90750012245919116572534285 34031254592219668714700357)
              ·
                refine ⟨6380860236041187884006317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34031254592219668714700357 6380860236041187884006317)
                ·
                  refine ⟨2392822588515445456502369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6380860236041187884006317 2392822588515445456502369)
                  ·
                    refine ⟨1794616941386584092376777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2392822588515445456502369 1794616941386584092376777)
                    ·
                      refine ⟨1345962706039938069282583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1794616941386584092376777 1345962706039938069282583)
                      ·
                        rfl

theorem cell23_2621253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 2, 2].length) (baseStart_2621253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621253 prefixEnd_2621253 := by exact prefixLift 2621253
  have htrace : WordTrace (prefixWord ++ tailWord_2621253) baseStart_2621253 baseEnd_2621253 := by
    simpa [prefixWord, tailWord_2621253, baseEnd_2621253] using wordTrace_append hprefix tailTrace_2621253
  have hstable : (prefixWord ++ tailWord_2621253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621253).length < 2 ^ (prefixWord ++ tailWord_2621253).sum := by decide
  have hdescent : baseEnd_2621253 < baseStart_2621253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621296 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 2, 7, 2]
def baseStart_2621296 : Nat := 118140960795 + 2621296 * 2 ^ 59
def prefixEnd_2621296 : Nat := 4983230072969 + 3 ^ 40 * 2621296 * 2
def baseEnd_2621296 : Nat := 1345984785708081401044885

theorem tailTrace_2621296 : CollatzResearch.WordTrace tailWord_2621296 prefixEnd_2621296 1345984785708081401044885 := by
  unfold tailWord_2621296
  simp only [CollatzResearch.WordTrace]
  refine ⟨47803259755749874280073871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63737679674333165706765161 47803259755749874280073871)
  ·
    refine ⟨71704889633624811420110807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47803259755749874280073871 71704889633624811420110807)
    ·
      refine ⟨107557334450437217130166211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71704889633624811420110807 107557334450437217130166211)
      ·
        refine ⟨161336001675655825695249317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107557334450437217130166211 161336001675655825695249317)
        ·
          refine ⟨30250500314185467317859247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161336001675655825695249317 30250500314185467317859247)
          ·
            refine ⟨45375750471278200976788871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30250500314185467317859247 45375750471278200976788871)
            ·
              refine ⟨68063625706917301465183307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45375750471278200976788871 68063625706917301465183307)
              ·
                refine ⟨102095438560375952197774961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68063625706917301465183307 102095438560375952197774961)
                ·
                  refine ⟨76571578920281964148331221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102095438560375952197774961 76571578920281964148331221)
                  ·
                    refine ⟨1794646380944108534726513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 76571578920281964148331221 1794646380944108534726513)
                    ·
                      refine ⟨1345984785708081401044885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1794646380944108534726513 1345984785708081401044885)
                      ·
                        rfl

theorem cell23_2621296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 7, 2].length) (baseStart_2621296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621296 prefixEnd_2621296 := by exact prefixLift 2621296
  have htrace : WordTrace (prefixWord ++ tailWord_2621296) baseStart_2621296 baseEnd_2621296 := by
    simpa [prefixWord, tailWord_2621296, baseEnd_2621296] using wordTrace_append hprefix tailTrace_2621296
  have hstable : (prefixWord ++ tailWord_2621296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621296).length < 2 ^ (prefixWord ++ tailWord_2621296).sum := by decide
  have hdescent : baseEnd_2621296 < baseStart_2621296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621309 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_2621309 : Nat := 118140960795 + 2621309 * 2 ^ 59
def prefixEnd_2621309 : Nat := 4983230072969 + 3 ^ 40 * 2621309 * 2
def baseEnd_2621309 : Nat := 1345991460956589850182325

theorem tailTrace_2621309 : CollatzResearch.WordTrace tailWord_2621309 prefixEnd_2621309 1345991460956589850182325 := by
  unfold tailWord_2621309
  simp only [CollatzResearch.WordTrace]
  refine ⟨95606993660452651780370981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63737995773635101186913987 95606993660452651780370981)
  ·
    refine ⟨17926311311334872208819559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95606993660452651780370981 17926311311334872208819559)
    ·
      refine ⟨26889466967002308313229339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17926311311334872208819559 26889466967002308313229339)
      ·
        refine ⟨40334200450503462469844009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26889466967002308313229339 40334200450503462469844009)
        ·
          refine ⟨30250650337877596852383007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40334200450503462469844009 30250650337877596852383007)
          ·
            refine ⟨45375975506816395278574511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30250650337877596852383007 45375975506816395278574511)
            ·
              refine ⟨68063963260224592917861767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45375975506816395278574511 68063963260224592917861767)
              ·
                refine ⟨102095944890336889376792651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68063963260224592917861767 102095944890336889376792651)
                ·
                  refine ⟨153143917335505334065188977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102095944890336889376792651 153143917335505334065188977)
                  ·
                    refine ⟨114857938001629000548891733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 153143917335505334065188977 114857938001629000548891733)
                    ·
                      refine ⟨1345991460956589850182325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 114857938001629000548891733 1345991460956589850182325)
                      ·
                        rfl

theorem cell23_2621309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_2621309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621309 prefixEnd_2621309 := by exact prefixLift 2621309
  have htrace : WordTrace (prefixWord ++ tailWord_2621309) baseStart_2621309 baseEnd_2621309 := by
    simpa [prefixWord, tailWord_2621309, baseEnd_2621309] using wordTrace_append hprefix tailTrace_2621309
  have hstable : (prefixWord ++ tailWord_2621309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621309).length < 2 ^ (prefixWord ++ tailWord_2621309).sum := by decide
  have hdescent : baseEnd_2621309 < baseStart_2621309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621349 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 11]
def baseStart_2621349 : Nat := 118140960795 + 2621349 * 2 ^ 59
def prefixEnd_2621349 : Nat := 4983230072969 + 3 ^ 40 * 2621349 * 2
def baseEnd_2621349 : Nat := 149556888909196632631349

theorem tailTrace_2621349 : CollatzResearch.WordTrace tailWord_2621349 prefixEnd_2621349 149556888909196632631349 := by
  unfold tailWord_2621349
  simp only [CollatzResearch.WordTrace]
  refine ⟨95608452580307738611827101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63738968386871825741218067 95608452580307738611827101)
  ·
    refine ⟨35853169717615401979435163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95608452580307738611827101 35853169717615401979435163)
    ·
      refine ⟨53779754576423102969152745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35853169717615401979435163 53779754576423102969152745)
      ·
        refine ⟨40334815932317327226864559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53779754576423102969152745 40334815932317327226864559)
        ·
          refine ⟨60502223898475990840296839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40334815932317327226864559 60502223898475990840296839)
          ·
            refine ⟨90753335847713986260445259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60502223898475990840296839 90753335847713986260445259)
            ·
              refine ⟨136130003771570979390667889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90753335847713986260445259 136130003771570979390667889)
              ·
                refine ⟨102097502828678234543000917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136130003771570979390667889 102097502828678234543000917)
                ·
                  refine ⟨149556888909196632631349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 102097502828678234543000917 149556888909196632631349)
                  ·
                    rfl

theorem cell23_2621349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_2621349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621349 prefixEnd_2621349 := by exact prefixLift 2621349
  have htrace : WordTrace (prefixWord ++ tailWord_2621349) baseStart_2621349 baseEnd_2621349 := by
    simpa [prefixWord, tailWord_2621349, baseEnd_2621349] using wordTrace_append hprefix tailTrace_2621349
  have hstable : (prefixWord ++ tailWord_2621349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621349).length < 2 ^ (prefixWord ++ tailWord_2621349).sum := by decide
  have hdescent : baseEnd_2621349 < baseStart_2621349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621376 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 3]
def baseStart_2621376 : Nat := 118140960795 + 2621376 * 2 ^ 59
def prefixEnd_2621376 : Nat := 4983230072969 + 3 ^ 40 * 2621376 * 2
def baseEnd_2621376 : Nat := 1346025864160441088044517

theorem tailTrace_2621376 : CollatzResearch.WordTrace tailWord_2621376 prefixEnd_2621376 1346025864160441088044517 := by
  unfold tailWord_2621376
  simp only [CollatzResearch.WordTrace]
  refine ⟨47804718675604961111529991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63739624900806614815373321 47804718675604961111529991)
  ·
    refine ⟨71707078013407441667294987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47804718675604961111529991 71707078013407441667294987)
    ·
      refine ⟨107560617020111162500942481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71707078013407441667294987 107560617020111162500942481)
      ·
        refine ⟨80670462765083371875706861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107560617020111162500942481 80670462765083371875706861)
        ·
          refine ⟨30251423536906264453390073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80670462765083371875706861 30251423536906264453390073)
          ·
            refine ⟨22688567652679698340042555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30251423536906264453390073 22688567652679698340042555)
            ·
              refine ⟨34032851479019547510063833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22688567652679698340042555 34032851479019547510063833)
              ·
                refine ⟨25524638609264660632547875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34032851479019547510063833 25524638609264660632547875)
                ·
                  refine ⟨38286957913896990948821813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25524638609264660632547875 38286957913896990948821813)
                  ·
                    refine ⟨3589402304427842901452045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38286957913896990948821813 3589402304427842901452045)
                    ·
                      refine ⟨1346025864160441088044517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3589402304427842901452045 1346025864160441088044517)
                      ·
                        rfl

theorem cell23_2621376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_2621376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621376 prefixEnd_2621376 := by exact prefixLift 2621376
  have htrace : WordTrace (prefixWord ++ tailWord_2621376) baseStart_2621376 baseEnd_2621376 := by
    simpa [prefixWord, tailWord_2621376, baseEnd_2621376] using wordTrace_append hprefix tailTrace_2621376
  have hstable : (prefixWord ++ tailWord_2621376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621376).length < 2 ^ (prefixWord ++ tailWord_2621376).sum := by decide
  have hdescent : baseEnd_2621376 < baseStart_2621376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621450 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_2621450 : Nat := 118140960795 + 2621450 * 2 ^ 59
def prefixEnd_2621450 : Nat := 4983230072969 + 3 ^ 40 * 2621450 * 2
def baseEnd_2621450 : Nat := 1346063861728873798519177

theorem tailTrace_2621450 : CollatzResearch.WordTrace tailWord_2621450 prefixEnd_2621450 1346063861728873798519177 := by
  unfold tailWord_2621450
  simp only [CollatzResearch.WordTrace]
  refine ⟨23903034088235458215313451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63741424235294555240835869 23903034088235458215313451)
  ·
    refine ⟨35854551132353187322970177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23903034088235458215313451 35854551132353187322970177)
    ·
      refine ⟨26890913349264890492227633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35854551132353187322970177 26890913349264890492227633)
      ·
        refine ⟨20168185011948667869170725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26890913349264890492227633 20168185011948667869170725)
        ·
          refine ⟨3781534689740375225469511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20168185011948667869170725 3781534689740375225469511)
          ·
            refine ⟨5672302034610562838204267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3781534689740375225469511 5672302034610562838204267)
            ·
              refine ⟨8508453051915844257306401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5672302034610562838204267 8508453051915844257306401)
              ·
                refine ⟨6381339788936883192979801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8508453051915844257306401 6381339788936883192979801)
                ·
                  refine ⟨4786004841702662394734851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6381339788936883192979801 4786004841702662394734851)
                  ·
                    refine ⟨7179007262553993592102277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4786004841702662394734851 7179007262553993592102277)
                    ·
                      refine ⟨1346063861728873798519177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7179007262553993592102277 1346063861728873798519177)
                      ·
                        rfl

theorem cell23_2621450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_2621450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621450 prefixEnd_2621450 := by exact prefixLift 2621450
  have htrace : WordTrace (prefixWord ++ tailWord_2621450) baseStart_2621450 baseEnd_2621450 := by
    simpa [prefixWord, tailWord_2621450, baseEnd_2621450] using wordTrace_append hprefix tailTrace_2621450
  have hstable : (prefixWord ++ tailWord_2621450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621450).length < 2 ^ (prefixWord ++ tailWord_2621450).sum := by decide
  have hdescent : baseEnd_2621450 < baseStart_2621450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621503 : List Nat := [1, 1, 2, 2, 3, 1, 2, 5, 1, 5]
def baseStart_2621503 : Nat := 118140960795 + 2621503 * 2 ^ 59
def prefixEnd_2621503 : Nat := 4983230072969 + 3 ^ 40 * 2621503 * 2
def baseEnd_2621503 : Nat := 448697025401187363718811

theorem tailTrace_2621503 : CollatzResearch.WordTrace tailWord_2621503 prefixEnd_2621503 448697025401187363718811 := by
  unfold tailWord_2621503
  simp only [CollatzResearch.WordTrace]
  refine ⟨95614069421749822912933163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63742712947833215275288775 95614069421749822912933163)
  ·
    refine ⟨143421104132624734369399745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95614069421749822912933163 143421104132624734369399745)
    ·
      refine ⟨107565828099468550777049809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143421104132624734369399745 107565828099468550777049809)
      ·
        refine ⟨80674371074601413082787357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107565828099468550777049809 80674371074601413082787357)
        ·
          refine ⟨30252889152975529906045259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80674371074601413082787357 30252889152975529906045259)
          ·
            refine ⟨45379333729463294859067889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30252889152975529906045259 45379333729463294859067889)
            ·
              refine ⟨34034500297097471144300917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45379333729463294859067889 34034500297097471144300917)
              ·
                refine ⟨3190734402852887919778211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34034500297097471144300917 3190734402852887919778211)
                ·
                  refine ⟨4786101604279331879667317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3190734402852887919778211 4786101604279331879667317)
                  ·
                    refine ⟨448697025401187363718811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4786101604279331879667317 448697025401187363718811)
                    ·
                      rfl

theorem cell23_2621503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 5].length) (baseStart_2621503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621503 prefixEnd_2621503 := by exact prefixLift 2621503
  have htrace : WordTrace (prefixWord ++ tailWord_2621503) baseStart_2621503 baseEnd_2621503 := by
    simpa [prefixWord, tailWord_2621503, baseEnd_2621503] using wordTrace_append hprefix tailTrace_2621503
  have hstable : (prefixWord ++ tailWord_2621503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621503).length < 2 ^ (prefixWord ++ tailWord_2621503).sum := by decide
  have hdescent : baseEnd_2621503 < baseStart_2621503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621510 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2621510 : Nat := 118140960795 + 2621510 * 2 ^ 59
def prefixEnd_2621510 : Nat := 4983230072969 + 3 ^ 40 * 2621510 * 2
def baseEnd_2621510 : Nat := 1346094670568143563768901

theorem tailTrace_2621510 : CollatzResearch.WordTrace tailWord_2621510 prefixEnd_2621510 1346094670568143563768901 := by
  unfold tailWord_2621510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2987947647897639472138687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63742883155149642072291989 2987947647897639472138687)
  ·
    refine ⟨4481921471846459208208031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2987947647897639472138687 4481921471846459208208031)
    ·
      refine ⟨6722882207769688812312047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4481921471846459208208031 6722882207769688812312047)
      ·
        refine ⟨10084323311654533218468071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6722882207769688812312047 10084323311654533218468071)
        ·
          refine ⟨15126484967481799827702107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10084323311654533218468071 15126484967481799827702107)
          ·
            refine ⟨22689727451222699741553161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15126484967481799827702107 22689727451222699741553161)
            ·
              refine ⟨17017295588417024806164871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22689727451222699741553161 17017295588417024806164871)
              ·
                refine ⟨25525943382625537209247307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17017295588417024806164871 25525943382625537209247307)
                ·
                  refine ⟨38288915073938305813870961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25525943382625537209247307 38288915073938305813870961)
                  ·
                    refine ⟨28716686305453729360403221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38288915073938305813870961 28716686305453729360403221)
                    ·
                      refine ⟨1346094670568143563768901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28716686305453729360403221 1346094670568143563768901)
                      ·
                        rfl

theorem cell23_2621510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2621510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621510 prefixEnd_2621510 := by exact prefixLift 2621510
  have htrace : WordTrace (prefixWord ++ tailWord_2621510) baseStart_2621510 baseEnd_2621510 := by
    simpa [prefixWord, tailWord_2621510, baseEnd_2621510] using wordTrace_append hprefix tailTrace_2621510
  have hstable : (prefixWord ++ tailWord_2621510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621510).length < 2 ^ (prefixWord ++ tailWord_2621510).sum := by decide
  have hdescent : baseEnd_2621510 < baseStart_2621510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621517 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_2621517 : Nat := 118140960795 + 2621517 * 2 ^ 59
def prefixEnd_2621517 : Nat := 4983230072969 + 3 ^ 40 * 2621517 * 2
def baseEnd_2621517 : Nat := 1346098264932725036381369

theorem tailTrace_2621517 : CollatzResearch.WordTrace tailWord_2621517 prefixEnd_2621517 1346098264932725036381369 := by
  unfold tailWord_2621517
  simp only [CollatzResearch.WordTrace]
  refine ⟨95614580043699103303942805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63743053362466068869295203 95614580043699103303942805)
  ·
    refine ⟨4481933439548395467372319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95614580043699103303942805 4481933439548395467372319)
    ·
      refine ⟨6722900159322593201058479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4481933439548395467372319 6722900159322593201058479)
      ·
        refine ⟨10084350238983889801587719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6722900159322593201058479 10084350238983889801587719)
        ·
          refine ⟨15126525358475834702381579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10084350238983889801587719 15126525358475834702381579)
          ·
            refine ⟨22689788037713752053572369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15126525358475834702381579 22689788037713752053572369)
            ·
              refine ⟨17017341028285314040179277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22689788037713752053572369 17017341028285314040179277)
              ·
                refine ⟨6381502885606992765067229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17017341028285314040179277 6381502885606992765067229)
                ·
                  refine ⟨2393063582102622286900211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6381502885606992765067229 2393063582102622286900211)
                  ·
                    refine ⟨3589595373153933430350317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2393063582102622286900211 3589595373153933430350317)
                    ·
                      refine ⟨1346098264932725036381369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3589595373153933430350317 1346098264932725036381369)
                      ·
                        rfl

theorem cell23_2621517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_2621517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621517 prefixEnd_2621517 := by exact prefixLift 2621517
  have htrace : WordTrace (prefixWord ++ tailWord_2621517) baseStart_2621517 baseEnd_2621517 := by
    simpa [prefixWord, tailWord_2621517, baseEnd_2621517] using wordTrace_append hprefix tailTrace_2621517
  have hstable : (prefixWord ++ tailWord_2621517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621517).length < 2 ^ (prefixWord ++ tailWord_2621517).sum := by decide
  have hdescent : baseEnd_2621517 < baseStart_2621517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621550 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_2621550 : Nat := 118140960795 + 2621550 * 2 ^ 59
def prefixEnd_2621550 : Nat := 4983230072969 + 3 ^ 40 * 2621550 * 2
def baseEnd_2621550 : Nat := 448705069931441135756239

theorem tailTrace_2621550 : CollatzResearch.WordTrace tailWord_2621550 prefixEnd_2621550 448705069931441135756239 := by
  unfold tailWord_2621550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11951972956572443742486763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63743855768386366626596069 11951972956572443742486763)
  ·
    refine ⟨17927959434858665613730145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11951972956572443742486763 17927959434858665613730145)
    ·
      refine ⟨13445969576143999210297609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17927959434858665613730145 13445969576143999210297609)
      ·
        refine ⟨10084477182107999407723207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13445969576143999210297609 10084477182107999407723207)
        ·
          refine ⟨15126715773161999111584811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10084477182107999407723207 15126715773161999111584811)
          ·
            refine ⟨22690073659742998667377217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15126715773161999111584811 22690073659742998667377217)
            ·
              refine ⟨17017555244807249000532913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22690073659742998667377217 17017555244807249000532913)
              ·
                refine ⟨12763166433605436750399685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17017555244807249000532913 12763166433605436750399685)
                ·
                  refine ⟨2393093706301019390699941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12763166433605436750399685 2393093706301019390699941)
                  ·
                    refine ⟨448705069931441135756239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2393093706301019390699941 448705069931441135756239)
                    ·
                      rfl

theorem cell23_2621550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_2621550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621550 prefixEnd_2621550 := by exact prefixLift 2621550
  have htrace : WordTrace (prefixWord ++ tailWord_2621550) baseStart_2621550 baseEnd_2621550 := by
    simpa [prefixWord, tailWord_2621550, baseEnd_2621550] using wordTrace_append hprefix tailTrace_2621550
  have hstable : (prefixWord ++ tailWord_2621550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621550).length < 2 ^ (prefixWord ++ tailWord_2621550).sum := by decide
  have hdescent : baseEnd_2621550 < baseStart_2621550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621553 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_2621553 : Nat := 118140960795 + 2621553 * 2 ^ 59
def prefixEnd_2621553 : Nat := 4983230072969 + 3 ^ 40 * 2621553 * 2
def baseEnd_2621553 : Nat := 1346116750236286895531203

theorem tailTrace_2621553 : CollatzResearch.WordTrace tailWord_2621553 prefixEnd_2621553 1346116750236286895531203 := by
  unfold tailWord_2621553
  simp only [CollatzResearch.WordTrace]
  refine ⟨95615893071568681452253313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63743928714379120968168875 95615893071568681452253313)
  ·
    refine ⟨71711919803676511089189985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95615893071568681452253313 71711919803676511089189985)
    ·
      refine ⟨53783939852757383316892489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71711919803676511089189985 53783939852757383316892489)
      ·
        refine ⟨40337954889568037487669367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53783939852757383316892489 40337954889568037487669367)
        ·
          refine ⟨60506932334352056231504051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40337954889568037487669367 60506932334352056231504051)
          ·
            refine ⟨90760398501528084347256077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60506932334352056231504051 90760398501528084347256077)
            ·
              refine ⟨34035149438073031630221029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90760398501528084347256077 34035149438073031630221029)
              ·
                refine ⟨6381590519638693430666443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34035149438073031630221029 6381590519638693430666443)
                ·
                  refine ⟨9572385779458040145999665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6381590519638693430666443 9572385779458040145999665)
                  ·
                    refine ⟨7179289334593530109499749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9572385779458040145999665 7179289334593530109499749)
                    ·
                      refine ⟨1346116750236286895531203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7179289334593530109499749 1346116750236286895531203)
                      ·
                        rfl

theorem cell23_2621553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_2621553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621553 prefixEnd_2621553 := by exact prefixLift 2621553
  have htrace : WordTrace (prefixWord ++ tailWord_2621553) baseStart_2621553 baseEnd_2621553 := by
    simpa [prefixWord, tailWord_2621553, baseEnd_2621553] using wordTrace_append hprefix tailTrace_2621553
  have hstable : (prefixWord ++ tailWord_2621553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621553).length < 2 ^ (prefixWord ++ tailWord_2621553).sum := by decide
  have hdescent : baseEnd_2621553 < baseStart_2621553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621594 : List Nat := [3, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2621594 : Nat := 118140960795 + 2621594 * 2 ^ 59
def prefixEnd_2621594 : Nat := 4983230072969 + 3 ^ 40 * 2621594 * 2
def baseEnd_2621594 : Nat := 1346137802943121235118515

theorem tailTrace_2621594 : CollatzResearch.WordTrace tailWord_2621594 prefixEnd_2621594 1346137802943121235118515 := by
  unfold tailWord_2621594
  simp only [CollatzResearch.WordTrace]
  refine ⟨23904347116105036363623959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63744925642946763636330557 23904347116105036363623959)
  ·
    refine ⟨35856520674157554545435939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23904347116105036363623959 35856520674157554545435939)
    ·
      refine ⟨53784781011236331818153909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35856520674157554545435939 53784781011236331818153909)
      ·
        refine ⟨5042323219803406107951929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53784781011236331818153909 5042323219803406107951929)
        ·
          refine ⟨3781742414852554580963947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5042323219803406107951929 3781742414852554580963947)
          ·
            refine ⟨5672613622278831871445921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3781742414852554580963947 5672613622278831871445921)
            ·
              refine ⟨4254460216709123903584441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5672613622278831871445921 4254460216709123903584441)
              ·
                refine ⟨3190845162531842927688331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4254460216709123903584441 3190845162531842927688331)
                ·
                  refine ⟨4786267743797764391532497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3190845162531842927688331 4786267743797764391532497)
                  ·
                    refine ⟨3589700807848323293649373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4786267743797764391532497 3589700807848323293649373)
                    ·
                      refine ⟨1346137802943121235118515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3589700807848323293649373 1346137802943121235118515)
                      ·
                        rfl

theorem cell23_2621594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2621594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621594 prefixEnd_2621594 := by exact prefixLift 2621594
  have htrace : WordTrace (prefixWord ++ tailWord_2621594) baseStart_2621594 baseEnd_2621594 := by
    simpa [prefixWord, tailWord_2621594, baseEnd_2621594] using wordTrace_append hprefix tailTrace_2621594
  have hstable : (prefixWord ++ tailWord_2621594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621594).length < 2 ^ (prefixWord ++ tailWord_2621594).sum := by decide
  have hdescent : baseEnd_2621594 < baseStart_2621594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621614 : List Nat := [4, 1, 4, 2, 2, 1, 9]
def baseStart_2621614 : Nat := 118140960795 + 2621614 * 2 ^ 59
def prefixEnd_2621614 : Nat := 4983230072969 + 3 ^ 40 * 2621614 * 2
def baseEnd_2621614 : Nat := 16619112006866804405783

theorem tailTrace_2621614 : CollatzResearch.WordTrace tailWord_2621614 prefixEnd_2621614 16619112006866804405783 := by
  unfold tailWord_2621614
  simp only [CollatzResearch.WordTrace]
  refine ⟨11952264740543461108777987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63745411949565125913482597 11952264740543461108777987)
  ·
    refine ⟨17928397110815191663166981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11952264740543461108777987 17928397110815191663166981)
    ·
      refine ⟨3361574458277848436843809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17928397110815191663166981 3361574458277848436843809)
      ·
        refine ⟨2521180843708386327632857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3361574458277848436843809 2521180843708386327632857)
        ·
          refine ⟨1890885632781289745724643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2521180843708386327632857 1890885632781289745724643)
          ·
            refine ⟨2836328449171934618586965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890885632781289745724643 2836328449171934618586965)
            ·
              refine ⟨16619112006866804405783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2836328449171934618586965 16619112006866804405783)
              ·
                rfl

theorem cell23_2621614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 9].length) (baseStart_2621614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621614 prefixEnd_2621614 := by exact prefixLift 2621614
  have htrace : WordTrace (prefixWord ++ tailWord_2621614) baseStart_2621614 baseEnd_2621614 := by
    simpa [prefixWord, tailWord_2621614, baseEnd_2621614] using wordTrace_append hprefix tailTrace_2621614
  have hstable : (prefixWord ++ tailWord_2621614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621614).length < 2 ^ (prefixWord ++ tailWord_2621614).sum := by decide
  have hdescent : baseEnd_2621614 < baseStart_2621614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621643 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 4]
def baseStart_2621643 : Nat := 118140960795 + 2621643 * 2 ^ 59
def prefixEnd_2621643 : Nat := 4983230072969 + 3 ^ 40 * 2621643 * 2
def baseEnd_2621643 : Nat := 1346162963495191543405789

theorem tailTrace_2621643 : CollatzResearch.WordTrace tailWord_2621643 prefixEnd_2621643 1346162963495191543405789 := by
  unfold tailWord_2621643
  simp only [CollatzResearch.WordTrace]
  refine ⟨95619175641242626823029583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63746117094161751215353055 95619175641242626823029583)
  ·
    refine ⟨143428763461863940234544375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95619175641242626823029583 143428763461863940234544375)
    ·
      refine ⟨215143145192795910351816563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143428763461863940234544375 215143145192795910351816563)
      ·
        refine ⟨322714717789193865527724845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215143145192795910351816563 322714717789193865527724845)
        ·
          refine ⟨121018019170947699572896817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322714717789193865527724845 121018019170947699572896817)
          ·
            refine ⟨90763514378210774679672613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121018019170947699572896817 90763514378210774679672613)
            ·
              refine ⟨17018158945914520252438615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90763514378210774679672613 17018158945914520252438615)
              ·
                refine ⟨25527238418871780378657923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17018158945914520252438615 25527238418871780378657923)
                ·
                  refine ⟨38290857628307670567986885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25527238418871780378657923 38290857628307670567986885)
                  ·
                    refine ⟨7179535805307688231497541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38290857628307670567986885 7179535805307688231497541)
                    ·
                      refine ⟨1346162963495191543405789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7179535805307688231497541 1346162963495191543405789)
                      ·
                        rfl

theorem cell23_2621643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 4].length) (baseStart_2621643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621643 prefixEnd_2621643 := by exact prefixLift 2621643
  have htrace : WordTrace (prefixWord ++ tailWord_2621643) baseStart_2621643 baseEnd_2621643 := by
    simpa [prefixWord, tailWord_2621643, baseEnd_2621643] using wordTrace_append hprefix tailTrace_2621643
  have hstable : (prefixWord ++ tailWord_2621643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621643).length < 2 ^ (prefixWord ++ tailWord_2621643).sum := by decide
  have hdescent : baseEnd_2621643 < baseStart_2621643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621650 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2621650 : Nat := 118140960795 + 2621650 * 2 ^ 59
def prefixEnd_2621650 : Nat := 4983230072969 + 3 ^ 40 * 2621650 * 2
def baseEnd_2621650 : Nat := 1346166557859773016018257

theorem tailTrace_2621650 : CollatzResearch.WordTrace tailWord_2621650 prefixEnd_2621650 1346166557859773016018257 := by
  unfold tailWord_2621650
  simp only [CollatzResearch.WordTrace]
  refine ⟨23904857738054316754633601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63746287301478178012356269 23904857738054316754633601)
  ·
    refine ⟨17928643303540737565975201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23904857738054316754633601 17928643303540737565975201)
    ·
      refine ⟨13446482477655553174481401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17928643303540737565975201 13446482477655553174481401)
      ·
        refine ⟨10084861858241664880861051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13446482477655553174481401 10084861858241664880861051)
        ·
          refine ⟨15127292787362497321291577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10084861858241664880861051 15127292787362497321291577)
          ·
            refine ⟨11345469590521872990968683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15127292787362497321291577 11345469590521872990968683)
            ·
              refine ⟨17018204385782809486453025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11345469590521872990968683 17018204385782809486453025)
              ·
                refine ⟨12763653289337107114839769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17018204385782809486453025 12763653289337107114839769)
                ·
                  refine ⟨9572739967002830336129827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12763653289337107114839769 9572739967002830336129827)
                  ·
                    refine ⟨14359109950504245504194741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9572739967002830336129827 14359109950504245504194741)
                    ·
                      refine ⟨1346166557859773016018257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14359109950504245504194741 1346166557859773016018257)
                      ·
                        rfl

theorem cell23_2621650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2621650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621650 prefixEnd_2621650 := by exact prefixLift 2621650
  have htrace : WordTrace (prefixWord ++ tailWord_2621650) baseStart_2621650 baseEnd_2621650 := by
    simpa [prefixWord, tailWord_2621650, baseEnd_2621650] using wordTrace_append hprefix tailTrace_2621650
  have hstable : (prefixWord ++ tailWord_2621650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621650).length < 2 ^ (prefixWord ++ tailWord_2621650).sum := by decide
  have hdescent : baseEnd_2621650 < baseStart_2621650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621720 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_2621720 : Nat := 118140960795 + 2621720 * 2 ^ 59
def prefixEnd_2621720 : Nat := 4983230072969 + 3 ^ 40 * 2621720 * 2
def baseEnd_2621720 : Nat := 1346202501505587742142935

theorem tailTrace_2621720 : CollatzResearch.WordTrace tailWord_2621720 prefixEnd_2621720 1346202501505587742142935 := by
  unfold tailWord_2621720
  simp only [CollatzResearch.WordTrace]
  refine ⟨47810992030981834486791307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63747989374642445982388409 47810992030981834486791307)
  ·
    refine ⟨71716488046472751730186961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47810992030981834486791307 71716488046472751730186961)
    ·
      refine ⟨53787366034854563797640221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71716488046472751730186961 53787366034854563797640221)
      ·
        refine ⟨20170262263070461424115083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53787366034854563797640221 20170262263070461424115083)
        ·
          refine ⟨30255393394605692136172625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20170262263070461424115083 30255393394605692136172625)
          ·
            refine ⟨22691545045954269102129469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30255393394605692136172625 22691545045954269102129469)
            ·
              refine ⟨8509329392232850913298551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22691545045954269102129469 8509329392232850913298551)
              ·
                refine ⟨12763994088349276369947827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8509329392232850913298551 12763994088349276369947827)
                ·
                  refine ⟨19145991132523914554921741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12763994088349276369947827 19145991132523914554921741)
                  ·
                    refine ⟨7179746674696467958095653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19145991132523914554921741 7179746674696467958095653)
                    ·
                      refine ⟨1346202501505587742142935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7179746674696467958095653 1346202501505587742142935)
                      ·
                        rfl

theorem cell23_2621720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_2621720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621720 prefixEnd_2621720 := by exact prefixLift 2621720
  have htrace : WordTrace (prefixWord ++ tailWord_2621720) baseStart_2621720 baseEnd_2621720 := by
    simpa [prefixWord, tailWord_2621720, baseEnd_2621720] using wordTrace_append hprefix tailTrace_2621720
  have hstable : (prefixWord ++ tailWord_2621720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621720).length < 2 ^ (prefixWord ++ tailWord_2621720).sum := by decide
  have hdescent : baseEnd_2621720 < baseStart_2621720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621747 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 3, 4]
def baseStart_2621747 : Nat := 118140960795 + 2621747 * 2 ^ 59
def prefixEnd_2621747 : Nat := 4983230072969 + 3 ^ 40 * 2621747 * 2
def baseEnd_2621747 : Nat := 448738788494419712168437

theorem tailTrace_2621747 : CollatzResearch.WordTrace tailWord_2621747 prefixEnd_2621747 448738788494419712168437 := by
  unfold tailWord_2621747
  simp only [CollatzResearch.WordTrace]
  refine ⟨95622968832865852584815495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63748645888577235056543663 95622968832865852584815495)
  ·
    refine ⟨143434453249298778877223243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95622968832865852584815495 143434453249298778877223243)
    ·
      refine ⟨215151679873948168315834865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143434453249298778877223243 215151679873948168315834865)
      ·
        refine ⟨161363759905461126236876149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215151679873948168315834865 161363759905461126236876149)
        ·
          refine ⟨15127852491136980584707139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161363759905461126236876149 15127852491136980584707139)
          ·
            refine ⟨22691778736705470877060709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15127852491136980584707139 22691778736705470877060709)
            ·
              refine ⟨4254708513132275789448883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22691778736705470877060709 4254708513132275789448883)
              ·
                refine ⟨6382062769698413684173325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4254708513132275789448883 6382062769698413684173325)
                ·
                  refine ⟨2393273538636905131564997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6382062769698413684173325 2393273538636905131564997)
                  ·
                    refine ⟨448738788494419712168437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2393273538636905131564997 448738788494419712168437)
                    ·
                      rfl

theorem cell23_2621747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 4].length) (baseStart_2621747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621747 prefixEnd_2621747 := by exact prefixLift 2621747
  have htrace : WordTrace (prefixWord ++ tailWord_2621747) baseStart_2621747 baseEnd_2621747 := by
    simpa [prefixWord, tailWord_2621747, baseEnd_2621747] using wordTrace_append hprefix tailTrace_2621747
  have hstable : (prefixWord ++ tailWord_2621747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621747).length < 2 ^ (prefixWord ++ tailWord_2621747).sum := by decide
  have hdescent : baseEnd_2621747 < baseStart_2621747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621847 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 5]
def baseStart_2621847 : Nat := 118140960795 + 2621847 * 2 ^ 59
def prefixEnd_2621847 : Nat := 4983230072969 + 3 ^ 40 * 2621847 * 2
def baseEnd_2621847 : Nat := 1346267713548708745254851

theorem tailTrace_2621847 : CollatzResearch.WordTrace tailWord_2621847 prefixEnd_2621847 1346267713548708745254851 := by
  unfold tailWord_2621847
  simp only [CollatzResearch.WordTrace]
  refine ⟨95626616132503569663455795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63751077421669046442303863 95626616132503569663455795)
  ·
    refine ⟨143439924198755354495183693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95626616132503569663455795 143439924198755354495183693)
    ·
      refine ⟨53789971574533257935693885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143439924198755354495183693 53789971574533257935693885)
      ·
        refine ⟨20171239340449971725885207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53789971574533257935693885 20171239340449971725885207)
        ·
          refine ⟨30256859010674957588827811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20171239340449971725885207 30256859010674957588827811)
          ·
            refine ⟨45385288516012436383241717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30256859010674957588827811 45385288516012436383241717)
            ·
              refine ⟨4254870798376165910928911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45385288516012436383241717 4254870798376165910928911)
              ·
                refine ⟨6382306197564248866393367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4254870798376165910928911 6382306197564248866393367)
                ·
                  refine ⟨9573459296346373299590051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6382306197564248866393367 9573459296346373299590051)
                  ·
                    refine ⟨14360188944519559949385077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9573459296346373299590051 14360188944519559949385077)
                    ·
                      refine ⟨1346267713548708745254851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14360188944519559949385077 1346267713548708745254851)
                      ·
                        rfl

theorem cell23_2621847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_2621847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621847 prefixEnd_2621847 := by exact prefixLift 2621847
  have htrace : WordTrace (prefixWord ++ tailWord_2621847) baseStart_2621847 baseEnd_2621847 := by
    simpa [prefixWord, tailWord_2621847, baseEnd_2621847] using wordTrace_append hprefix tailTrace_2621847
  have hstable : (prefixWord ++ tailWord_2621847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621847).length < 2 ^ (prefixWord ++ tailWord_2621847).sum := by decide
  have hdescent : baseEnd_2621847 < baseStart_2621847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621850 : List Nat := [3, 1, 1, 4, 1, 13]
def baseStart_2621850 : Nat := 118140960795 + 2621850 * 2 ^ 59
def prefixEnd_2621850 : Nat := 4983230072969 + 3 ^ 40 * 2621850 * 2
def baseEnd_2621850 : Nat := 5540202691319638821059

theorem tailTrace_2621850 : CollatzResearch.WordTrace tailWord_2621850 prefixEnd_2621850 5540202691319638821059 := by
  unfold tailWord_2621850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23906681387873175293953751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63751150367661800783876669 23906681387873175293953751)
  ·
    refine ⟨35860022081809762940930627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23906681387873175293953751 35860022081809762940930627)
    ·
      refine ⟨53790033122714644411395941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35860022081809762940930627 53790033122714644411395941)
      ·
        refine ⟨10085631210508995827136739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53790033122714644411395941 10085631210508995827136739)
        ·
          refine ⟨15128446815763493740705109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10085631210508995827136739 15128446815763493740705109)
          ·
            refine ⟨5540202691319638821059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 15128446815763493740705109 5540202691319638821059)
            ·
              rfl

theorem cell23_2621850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 13].length) (baseStart_2621850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621850 prefixEnd_2621850 := by exact prefixLift 2621850
  have htrace : WordTrace (prefixWord ++ tailWord_2621850) baseStart_2621850 baseEnd_2621850 := by
    simpa [prefixWord, tailWord_2621850, baseEnd_2621850] using wordTrace_append hprefix tailTrace_2621850
  have hstable : (prefixWord ++ tailWord_2621850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621850).length < 2 ^ (prefixWord ++ tailWord_2621850).sum := by decide
  have hdescent : baseEnd_2621850 < baseStart_2621850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621880 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 4, 7]
def baseStart_2621880 : Nat := 118140960795 + 2621880 * 2 ^ 59
def prefixEnd_2621880 : Nat := 4983230072969 + 3 ^ 40 * 2621880 * 2
def baseEnd_2621880 : Nat := 448761552803435705380733

theorem tailTrace_2621880 : CollatzResearch.WordTrace tailWord_2621880 prefixEnd_2621880 448761552803435705380733 := by
  unfold tailWord_2621880
  simp only [CollatzResearch.WordTrace]
  refine ⟨47813909870692008149703547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63751879827589344199604729 47813909870692008149703547)
  ·
    refine ⟨71720864806038012224555321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47813909870692008149703547 71720864806038012224555321)
    ·
      refine ⟨53790648604528509168416491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71720864806038012224555321 53790648604528509168416491)
      ·
        refine ⟨80685972906792763752624737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53790648604528509168416491 80685972906792763752624737)
        ·
          refine ⟨60514479680094572814468553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80685972906792763752624737 60514479680094572814468553)
          ·
            refine ⟨45385859760070929610851415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60514479680094572814468553 45385859760070929610851415)
            ·
              refine ⟨68078789640106394416277123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45385859760070929610851415 68078789640106394416277123)
              ·
                refine ⟨102118184460159591624415685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68078789640106394416277123 102118184460159591624415685)
                ·
                  refine ⟨19147159586279923429577941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102118184460159591624415685 19147159586279923429577941)
                  ·
                    refine ⟨448761552803435705380733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19147159586279923429577941 448761552803435705380733)
                    ·
                      rfl

theorem cell23_2621880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_2621880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621880 prefixEnd_2621880 := by exact prefixLift 2621880
  have htrace : WordTrace (prefixWord ++ tailWord_2621880) baseStart_2621880 baseEnd_2621880 := by
    simpa [prefixWord, tailWord_2621880, baseEnd_2621880] using wordTrace_append hprefix tailTrace_2621880
  have hstable : (prefixWord ++ tailWord_2621880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621880).length < 2 ^ (prefixWord ++ tailWord_2621880).sum := by decide
  have hdescent : baseEnd_2621880 < baseStart_2621880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621884 : List Nat := [2, 2, 2, 4, 1, 2, 3, 7]
def baseStart_2621884 : Nat := 118140960795 + 2621884 * 2 ^ 59
def prefixEnd_2621884 : Nat := 4983230072969 + 3 ^ 40 * 2621884 * 2
def baseEnd_2621884 : Nat := 49862470827145374092303

theorem tailTrace_2621884 : CollatzResearch.WordTrace tailWord_2621884 prefixEnd_2621884 49862470827145374092303 := by
  unfold tailWord_2621884
  simp only [CollatzResearch.WordTrace]
  refine ⟨47813982816684762491276353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63751977088913016655035137 47813982816684762491276353)
  ·
    refine ⟨35860487112513571868457265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47813982816684762491276353 35860487112513571868457265)
    ·
      refine ⟨26895365334385178901342949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35860487112513571868457265 26895365334385178901342949)
      ·
        refine ⟨5042881000197221044001803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26895365334385178901342949 5042881000197221044001803)
        ·
          refine ⟨7564321500295831566002705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5042881000197221044001803 7564321500295831566002705)
          ·
            refine ⟨5673241125221873674502029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7564321500295831566002705 5673241125221873674502029)
            ·
              refine ⟨2127465421958202627938261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5673241125221873674502029 2127465421958202627938261)
              ·
                refine ⟨49862470827145374092303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2127465421958202627938261 49862470827145374092303)
                ·
                  rfl

theorem cell23_2621884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 7].length) (baseStart_2621884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621884 prefixEnd_2621884 := by exact prefixLift 2621884
  have htrace : WordTrace (prefixWord ++ tailWord_2621884) baseStart_2621884 baseEnd_2621884 := by
    simpa [prefixWord, tailWord_2621884, baseEnd_2621884] using wordTrace_append hprefix tailTrace_2621884
  have hstable : (prefixWord ++ tailWord_2621884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621884).length < 2 ^ (prefixWord ++ tailWord_2621884).sum := by decide
  have hdescent : baseEnd_2621884 < baseStart_2621884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621927 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 2, 6]
def baseStart_2621927 : Nat := 118140960795 + 2621927 * 2 ^ 59
def prefixEnd_2621927 : Nat := 4983230072969 + 3 ^ 40 * 2621927 * 2
def baseEnd_2621927 : Nat := 448769597333689477418161

theorem tailTrace_2621927 : CollatzResearch.WordTrace tailWord_2621927 prefixEnd_2621927 448769597333689477418161 := by
  unfold tailWord_2621927
  simp only [CollatzResearch.WordTrace]
  refine ⟨95629533972213743326368035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63753022648142495550912023 95629533972213743326368035)
  ·
    refine ⟨143444300958320614989552053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95629533972213743326368035 143444300958320614989552053)
    ·
      refine ⟨13447903214842557655270505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143444300958320614989552053 13447903214842557655270505)
      ·
        refine ⟨10085927411131918241452879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13447903214842557655270505 10085927411131918241452879)
        ·
          refine ⟨15128891116697877362179319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10085927411131918241452879 15128891116697877362179319)
          ·
            refine ⟨22693336675046816043268979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15128891116697877362179319 22693336675046816043268979)
            ·
              refine ⟨34040005012570224064903469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22693336675046816043268979 34040005012570224064903469)
              ·
                refine ⟨12765001879713834024338801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34040005012570224064903469 12765001879713834024338801)
                ·
                  refine ⟨9573751409785375518254101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12765001879713834024338801 9573751409785375518254101)
                  ·
                    refine ⟨448769597333689477418161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9573751409785375518254101 448769597333689477418161)
                    ·
                      rfl

theorem cell23_2621927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_2621927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621927 prefixEnd_2621927 := by exact prefixLift 2621927
  have htrace : WordTrace (prefixWord ++ tailWord_2621927) baseStart_2621927 baseEnd_2621927 := by
    simpa [prefixWord, tailWord_2621927, baseEnd_2621927] using wordTrace_append hprefix tailTrace_2621927
  have hstable : (prefixWord ++ tailWord_2621927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621927).length < 2 ^ (prefixWord ++ tailWord_2621927).sum := by decide
  have hdescent : baseEnd_2621927 < baseStart_2621927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621928 : List Nat := [2, 1, 4, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_2621928 : Nat := 118140960795 + 2621928 * 2 ^ 59
def prefixEnd_2621928 : Nat := 4983230072969 + 3 ^ 40 * 2621928 * 2
def baseEnd_2621928 : Nat := 1346309305481722928341979

theorem tailTrace_2621928 : CollatzResearch.WordTrace tailWord_2621928 prefixEnd_2621928 1346309305481722928341979 := by
  unfold tailWord_2621928
  simp only [CollatzResearch.WordTrace]
  refine ⟨47814785222605060248577219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63753046963473413664769625 47814785222605060248577219)
  ·
    refine ⟨71722177833907590372865829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47814785222605060248577219 71722177833907590372865829)
    ·
      refine ⟨13447908343857673194912343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71722177833907590372865829 13447908343857673194912343)
      ·
        refine ⟨20171862515786509792368515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13447908343857673194912343 20171862515786509792368515)
        ·
          refine ⟨30257793773679764688552773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20171862515786509792368515 30257793773679764688552773)
          ·
            refine ⟨5673336332564955879103645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30257793773679764688552773 5673336332564955879103645)
            ·
              refine ⟨2127501124711858454663867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5673336332564955879103645 2127501124711858454663867)
              ·
                refine ⟨3191251687067787681995801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127501124711858454663867 3191251687067787681995801)
                ·
                  refine ⟨2393438765300840761496851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3191251687067787681995801 2393438765300840761496851)
                  ·
                    refine ⟨3590158147951261142245277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2393438765300840761496851 3590158147951261142245277)
                    ·
                      refine ⟨1346309305481722928341979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3590158147951261142245277 1346309305481722928341979)
                      ·
                        rfl

theorem cell23_2621928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_2621928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621928 prefixEnd_2621928 := by exact prefixLift 2621928
  have htrace : WordTrace (prefixWord ++ tailWord_2621928) baseStart_2621928 baseEnd_2621928 := by
    simpa [prefixWord, tailWord_2621928, baseEnd_2621928] using wordTrace_append hprefix tailTrace_2621928
  have hstable : (prefixWord ++ tailWord_2621928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621928).length < 2 ^ (prefixWord ++ tailWord_2621928).sum := by decide
  have hdescent : baseEnd_2621928 < baseStart_2621928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621937 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_2621937 : Nat := 118140960795 + 2621937 * 2 ^ 59
def prefixEnd_2621937 : Nat := 4983230072969 + 3 ^ 40 * 2621937 * 2
def baseEnd_2621937 : Nat := 1346313926807613393129437

theorem tailTrace_2621937 : CollatzResearch.WordTrace tailWord_2621937 prefixEnd_2621937 1346313926807613393129437 := by
  unfold tailWord_2621937
  simp only [CollatzResearch.WordTrace]
  refine ⟨95629898702177515034232065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63753265801451676689488043 95629898702177515034232065)
  ·
    refine ⟨71722424026633136275674049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95629898702177515034232065 71722424026633136275674049)
    ·
      refine ⟨53791818019974852206755537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71722424026633136275674049 53791818019974852206755537)
      ·
        refine ⟨40343863514981139155066653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53791818019974852206755537 40343863514981139155066653)
        ·
          refine ⟨15128948818117927183149995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40343863514981139155066653 15128948818117927183149995)
          ·
            refine ⟨22693423227176890774724993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15128948818117927183149995 22693423227176890774724993)
            ·
              refine ⟨17020067420382668081043745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22693423227176890774724993 17020067420382668081043745)
              ·
                refine ⟨12765050565287001060782809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17020067420382668081043745 12765050565287001060782809)
                ·
                  refine ⟨9573787923965250795587107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12765050565287001060782809 9573787923965250795587107)
                  ·
                    refine ⟨14360681885947876193380661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9573787923965250795587107 14360681885947876193380661)
                    ·
                      refine ⟨1346313926807613393129437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14360681885947876193380661 1346313926807613393129437)
                      ·
                        rfl

theorem cell23_2621937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_2621937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2621937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2621937 prefixEnd_2621937 := by exact prefixLift 2621937
  have htrace : WordTrace (prefixWord ++ tailWord_2621937) baseStart_2621937 baseEnd_2621937 := by
    simpa [prefixWord, tailWord_2621937, baseEnd_2621937] using wordTrace_append hprefix tailTrace_2621937
  have hstable : (prefixWord ++ tailWord_2621937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621937).length < 2 ^ (prefixWord ++ tailWord_2621937).sum := by decide
  have hdescent : baseEnd_2621937 < baseStart_2621937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622024 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 3, 6, 2]
def baseStart_2622024 : Nat := 118140960795 + 2622024 * 2 ^ 59
def prefixEnd_2622024 : Nat := 4983230072969 + 3 ^ 40 * 2622024 * 2
def baseEnd_2622024 : Nat := 1346358599624554552741537

theorem tailTrace_2622024 : CollatzResearch.WordTrace tailWord_2622024 prefixEnd_2622024 1346358599624554552741537 := by
  unfold tailWord_2622024
  simp only [CollatzResearch.WordTrace]
  refine ⟨47816535926431164446324563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63755381235241552595099417 47816535926431164446324563)
  ·
    refine ⟨71724803889646746669486845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47816535926431164446324563 71724803889646746669486845)
    ·
      refine ⟨26896801458617530001057567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71724803889646746669486845 26896801458617530001057567)
      ·
        refine ⟨40345202187926295001586351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26896801458617530001057567 40345202187926295001586351)
        ·
          refine ⟨60517803281889442502379527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40345202187926295001586351 60517803281889442502379527)
          ·
            refine ⟨90776704922834163753569291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60517803281889442502379527 90776704922834163753569291)
            ·
              refine ⟨136165057384251245630353937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90776704922834163753569291 136165057384251245630353937)
              ·
                refine ⟨102123793038188434222765453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136165057384251245630353937 102123793038188434222765453)
                ·
                  refine ⟨38296422389320662833537045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102123793038188434222765453 38296422389320662833537045)
                  ·
                    refine ⟨1795144799499406070322049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38296422389320662833537045 1795144799499406070322049)
                    ·
                      refine ⟨1346358599624554552741537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1795144799499406070322049 1346358599624554552741537)
                      ·
                        rfl

theorem cell23_2622024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_2622024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622024 prefixEnd_2622024 := by exact prefixLift 2622024
  have htrace : WordTrace (prefixWord ++ tailWord_2622024) baseStart_2622024 baseEnd_2622024 := by
    simpa [prefixWord, tailWord_2622024, baseEnd_2622024] using wordTrace_append hprefix tailTrace_2622024
  have hstable : (prefixWord ++ tailWord_2622024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622024).length < 2 ^ (prefixWord ++ tailWord_2622024).sum := by decide
  have hdescent : baseEnd_2622024 < baseStart_2622024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622061 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_2622061 : Nat := 118140960795 + 2622061 * 2 ^ 59
def prefixEnd_2622061 : Nat := 4983230072969 + 3 ^ 40 * 2622061 * 2
def baseEnd_2622061 : Nat := 1346377598408770907978867

theorem tailTrace_2622061 : CollatzResearch.WordTrace tailWord_2622061 prefixEnd_2622061 1346377598408770907978867 := by
  unfold tailWord_2622061
  simp only [CollatzResearch.WordTrace]
  refine ⟨95634421353728284211746037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63756280902485522807830691 95634421353728284211746037)
  ·
    refine ⟨8965727001912026644851191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95634421353728284211746037 8965727001912026644851191)
    ·
      refine ⟨13448590502868039967276787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8965727001912026644851191 13448590502868039967276787)
      ·
        refine ⟨20172885754302059950915181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13448590502868039967276787 20172885754302059950915181)
        ·
          refine ⟨7564832157863272481593193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20172885754302059950915181 7564832157863272481593193)
          ·
            refine ⟨5673624118397454361194895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7564832157863272481593193 5673624118397454361194895)
            ·
              refine ⟨8510436177596181541792343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5673624118397454361194895 8510436177596181541792343)
              ·
                refine ⟨12765654266394272312688515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8510436177596181541792343 12765654266394272312688515)
                ·
                  refine ⟨19148481399591408469032773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12765654266394272312688515 19148481399591408469032773)
                  ·
                    refine ⟨3590340262423389087943645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19148481399591408469032773 3590340262423389087943645)
                    ·
                      refine ⟨1346377598408770907978867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3590340262423389087943645 1346377598408770907978867)
                      ·
                        rfl

theorem cell23_2622061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_2622061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622061 prefixEnd_2622061 := by exact prefixLift 2622061
  have htrace : WordTrace (prefixWord ++ tailWord_2622061) baseStart_2622061 baseEnd_2622061 := by
    simpa [prefixWord, tailWord_2622061, baseEnd_2622061] using wordTrace_append hprefix tailTrace_2622061
  have hstable : (prefixWord ++ tailWord_2622061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622061).length < 2 ^ (prefixWord ++ tailWord_2622061).sum := by decide
  have hdescent : baseEnd_2622061 < baseStart_2622061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622084 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_2622084 : Nat := 118140960795 + 2622084 * 2 ^ 59
def prefixEnd_2622084 : Nat := 4983230072969 + 3 ^ 40 * 2622084 * 2
def baseEnd_2622084 : Nat := 1346389408463824317991261

theorem tailTrace_2622084 : CollatzResearch.WordTrace tailWord_2622084 prefixEnd_2622084 1346389408463824317991261 := by
  unfold tailWord_2622084
  simp only [CollatzResearch.WordTrace]
  refine ⟨47817630116322479569916653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63756840155096639426555537 47817630116322479569916653)
  ·
    refine ⟨17931611293620929838718745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47817630116322479569916653 17931611293620929838718745)
    ·
      refine ⟨13448708470215697379039059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17931611293620929838718745 13448708470215697379039059)
      ·
        refine ⟨20173062705323546068558589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13448708470215697379039059 20173062705323546068558589)
        ·
          refine ⟨7564898514496329775709471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20173062705323546068558589 7564898514496329775709471)
          ·
            refine ⟨11347347771744494663564207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7564898514496329775709471 11347347771744494663564207)
            ·
              refine ⟨17021021657616741995346311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11347347771744494663564207 17021021657616741995346311)
              ·
                refine ⟨25531532486425112993019467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17021021657616741995346311 25531532486425112993019467)
                ·
                  refine ⟨38297298729637669489529201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25531532486425112993019467 38297298729637669489529201)
                  ·
                    refine ⟨28722974047228252117146901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38297298729637669489529201 28722974047228252117146901)
                    ·
                      refine ⟨1346389408463824317991261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28722974047228252117146901 1346389408463824317991261)
                      ·
                        rfl

theorem cell23_2622084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_2622084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622084 prefixEnd_2622084 := by exact prefixLift 2622084
  have htrace : WordTrace (prefixWord ++ tailWord_2622084) baseStart_2622084 baseEnd_2622084 := by
    simpa [prefixWord, tailWord_2622084, baseEnd_2622084] using wordTrace_append hprefix tailTrace_2622084
  have hstable : (prefixWord ++ tailWord_2622084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622084).length < 2 ^ (prefixWord ++ tailWord_2622084).sum := by decide
  have hdescent : baseEnd_2622084 < baseStart_2622084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622098 : List Nat := [3, 2, 3, 1, 2, 2, 3, 1, 6]
def baseStart_2622098 : Nat := 118140960795 + 2622098 * 2 ^ 59
def prefixEnd_2622098 : Nat := 4983230072969 + 3 ^ 40 * 2622098 * 2
def baseEnd_2622098 : Nat := 149599621910331918135133

theorem tailTrace_2622098 : CollatzResearch.WordTrace tailWord_2622098 prefixEnd_2622098 149599621910331918135133 := by
  unfold tailWord_2622098
  simp only [CollatzResearch.WordTrace]
  refine ⟨23908942713648559882710737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63757180569729493020561965 23908942713648559882710737)
  ·
    refine ⟨17931707035236419912033053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23908942713648559882710737 17931707035236419912033053)
    ·
      refine ⟨6724390138213657467012395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17931707035236419912033053 6724390138213657467012395)
      ·
        refine ⟨10086585207320486200518593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6724390138213657467012395 10086585207320486200518593)
        ·
          refine ⟨7564938905490364650388945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10086585207320486200518593 7564938905490364650388945)
          ·
            refine ⟨5673704179117773487791709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7564938905490364650388945 5673704179117773487791709)
            ·
              refine ⟨2127639067169165057921891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5673704179117773487791709 2127639067169165057921891)
              ·
                refine ⟨3191458600753747586882837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127639067169165057921891 3191458600753747586882837)
                ·
                  refine ⟨149599621910331918135133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3191458600753747586882837 149599621910331918135133)
                  ·
                    rfl

theorem cell23_2622098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_2622098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622098 prefixEnd_2622098 := by exact prefixLift 2622098
  have htrace : WordTrace (prefixWord ++ tailWord_2622098) baseStart_2622098 baseEnd_2622098 := by
    simpa [prefixWord, tailWord_2622098, baseEnd_2622098] using wordTrace_append hprefix tailTrace_2622098
  have hstable : (prefixWord ++ tailWord_2622098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622098).length < 2 ^ (prefixWord ++ tailWord_2622098).sum := by decide
  have hdescent : baseEnd_2622098 < baseStart_2622098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622108 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_2622108 : Nat := 118140960795 + 2622108 * 2 ^ 59
def prefixEnd_2622108 : Nat := 4983230072969 + 3 ^ 40 * 2622108 * 2
def baseEnd_2622108 : Nat := 1346401731999532224091151

theorem tailTrace_2622108 : CollatzResearch.WordTrace tailWord_2622108 prefixEnd_2622108 1346401731999532224091151 := by
  unfold tailWord_2622108
  simp only [CollatzResearch.WordTrace]
  refine ⟨47818067792279005619353489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63757423723038674159137985 47818067792279005619353489)
  ·
    refine ⟨35863550844209254214515117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47818067792279005619353489 35863550844209254214515117)
    ·
      refine ⟨13448831566578470330443169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35863550844209254214515117 13448831566578470330443169)
      ·
        refine ⟨10086623674933852747832377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13448831566578470330443169 10086623674933852747832377)
        ·
          refine ⟨7564967756200389560874283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10086623674933852747832377 7564967756200389560874283)
          ·
            refine ⟨11347451634300584341311425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7564967756200389560874283 11347451634300584341311425)
            ·
              refine ⟨8510588725725438255983569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11347451634300584341311425 8510588725725438255983569)
              ·
                refine ⟨6382941544294078691987677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8510588725725438255983569 6382941544294078691987677)
                ·
                  refine ⟨2393603079110279509495379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6382941544294078691987677 2393603079110279509495379)
                  ·
                    refine ⟨3590404618665419264243069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2393603079110279509495379 3590404618665419264243069)
                    ·
                      refine ⟨1346401731999532224091151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3590404618665419264243069 1346401731999532224091151)
                      ·
                        rfl

theorem cell23_2622108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_2622108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622108 prefixEnd_2622108 := by exact prefixLift 2622108
  have htrace : WordTrace (prefixWord ++ tailWord_2622108) baseStart_2622108 baseEnd_2622108 := by
    simpa [prefixWord, tailWord_2622108, baseEnd_2622108] using wordTrace_append hprefix tailTrace_2622108
  have hstable : (prefixWord ++ tailWord_2622108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622108).length < 2 ^ (prefixWord ++ tailWord_2622108).sum := by decide
  have hdescent : baseEnd_2622108 < baseStart_2622108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622119 : List Nat := [1, 1, 6, 3, 2, 1, 1, 3, 1, 4]
def baseStart_2622119 : Nat := 118140960795 + 2622119 * 2 ^ 59
def prefixEnd_2622119 : Nat := 4983230072969 + 3 ^ 40 * 2622119 * 2
def baseEnd_2622119 : Nat := 448802460095577227017867

theorem tailTrace_2622119 : CollatzResearch.WordTrace tailWord_2622119 prefixEnd_2622119 448802460095577227017867 := by
  unfold tailWord_2622119
  simp only [CollatzResearch.WordTrace]
  refine ⟨95636536787518160117357411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63757691191678773411571607 95636536787518160117357411)
  ·
    refine ⟨143454805181277240176036117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95636536787518160117357411 143454805181277240176036117)
    ·
      refine ⟨6724443992872370633251693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 143454805181277240176036117 6724443992872370633251693)
      ·
        refine ⟨2521666497327138987469385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6724443992872370633251693 2521666497327138987469385)
        ·
          refine ⟨1891249872995354240602039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2521666497327138987469385 1891249872995354240602039)
          ·
            refine ⟨2836874809493031360903059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891249872995354240602039 2836874809493031360903059)
            ·
              refine ⟨4255312214239547041354589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2836874809493031360903059 4255312214239547041354589)
              ·
                refine ⟨1595742080339830140507971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4255312214239547041354589 1595742080339830140507971)
                ·
                  refine ⟨2393613120509745210761957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595742080339830140507971 2393613120509745210761957)
                  ·
                    refine ⟨448802460095577227017867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2393613120509745210761957 448802460095577227017867)
                    ·
                      rfl

theorem cell23_2622119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_2622119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622119 prefixEnd_2622119 := by exact prefixLift 2622119
  have htrace : WordTrace (prefixWord ++ tailWord_2622119) baseStart_2622119 baseEnd_2622119 := by
    simpa [prefixWord, tailWord_2622119, baseEnd_2622119] using wordTrace_append hprefix tailTrace_2622119
  have hstable : (prefixWord ++ tailWord_2622119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622119).length < 2 ^ (prefixWord ++ tailWord_2622119).sum := by decide
  have hdescent : baseEnd_2622119 < baseStart_2622119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622131 : List Nat := [1, 1, 1, 2, 3, 4, 2, 3, 1, 1, 4]
def baseStart_2622131 : Nat := 118140960795 + 2622131 * 2 ^ 59
def prefixEnd_2622131 : Nat := 4983230072969 + 3 ^ 40 * 2622131 * 2
def baseEnd_2622131 : Nat := 1346413542054585634103545

theorem tailTrace_2622131 : CollatzResearch.WordTrace tailWord_2622131 prefixEnd_2622131 1346413542054585634103545 := by
  unfold tailWord_2622131
  simp only [CollatzResearch.WordTrace]
  refine ⟨95636974463474686166794247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63757982975649790777862831 95636974463474686166794247)
  ·
    refine ⟨143455461695212029250191371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95636974463474686166794247 143455461695212029250191371)
    ·
      refine ⟨215183192542818043875287057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143455461695212029250191371 215183192542818043875287057)
      ·
        refine ⟨161387394407113532906465293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215183192542818043875287057 161387394407113532906465293)
        ·
          refine ⟨60520272902667574839924485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161387394407113532906465293 60520272902667574839924485)
          ·
            refine ⟨11347551169250170282485841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60520272902667574839924485 11347551169250170282485841)
            ·
              refine ⟨8510663376937627711864381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11347551169250170282485841 8510663376937627711864381)
              ·
                refine ⟨3191498766351610391949143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8510663376937627711864381 3191498766351610391949143)
                ·
                  refine ⟨4787248149527415587923715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3191498766351610391949143 4787248149527415587923715)
                  ·
                    refine ⟨7180872224291123381885573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4787248149527415587923715 7180872224291123381885573)
                    ·
                      refine ⟨1346413542054585634103545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7180872224291123381885573 1346413542054585634103545)
                      ·
                        rfl

theorem cell23_2622131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 1, 4].length) (baseStart_2622131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622131 prefixEnd_2622131 := by exact prefixLift 2622131
  have htrace : WordTrace (prefixWord ++ tailWord_2622131) baseStart_2622131 baseEnd_2622131 := by
    simpa [prefixWord, tailWord_2622131, baseEnd_2622131] using wordTrace_append hprefix tailTrace_2622131
  have hstable : (prefixWord ++ tailWord_2622131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622131).length < 2 ^ (prefixWord ++ tailWord_2622131).sum := by decide
  have hdescent : baseEnd_2622131 < baseStart_2622131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622141 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_2622141 : Nat := 118140960795 + 2622141 * 2 ^ 59
def prefixEnd_2622141 : Nat := 4983230072969 + 3 ^ 40 * 2622141 * 2
def baseEnd_2622141 : Nat := 448806225620376864992833

theorem tailTrace_2622141 : CollatzResearch.WordTrace tailWord_2622141 prefixEnd_2622141 448806225620376864992833 := by
  unfold tailWord_2622141
  simp only [CollatzResearch.WordTrace]
  refine ⟨95637339193438457874658277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63758226128958971916438851 95637339193438457874658277)
  ·
    refine ⟨17932001098769710851498427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95637339193438457874658277 17932001098769710851498427)
    ·
      refine ⟨26898001648154566277247641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17932001098769710851498427 26898001648154566277247641)
      ·
        refine ⟨20173501236115924707935731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26898001648154566277247641 20173501236115924707935731)
        ·
          refine ⟨30260251854173887061903597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20173501236115924707935731 30260251854173887061903597)
          ·
            refine ⟨11347594445315207648213849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30260251854173887061903597 11347594445315207648213849)
            ·
              refine ⟨8510695833986405736160387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11347594445315207648213849 8510695833986405736160387)
              ·
                refine ⟨12766043750979608604240581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8510695833986405736160387 12766043750979608604240581)
                ·
                  refine ⟨2393633203308676613295109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12766043750979608604240581 2393633203308676613295109)
                  ·
                    refine ⟨448806225620376864992833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2393633203308676613295109 448806225620376864992833)
                    ·
                      rfl

theorem cell23_2622141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_2622141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622141 prefixEnd_2622141 := by exact prefixLift 2622141
  have htrace : WordTrace (prefixWord ++ tailWord_2622141) baseStart_2622141 baseEnd_2622141 := by
    simpa [prefixWord, tailWord_2622141, baseEnd_2622141] using wordTrace_append hprefix tailTrace_2622141
  have hstable : (prefixWord ++ tailWord_2622141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622141).length < 2 ^ (prefixWord ++ tailWord_2622141).sum := by decide
  have hdescent : baseEnd_2622141 < baseStart_2622141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622142 : List Nat := [4, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_2622142 : Nat := 118140960795 + 2622142 * 2 ^ 59
def prefixEnd_2622142 : Nat := 4983230072969 + 3 ^ 40 * 2622142 * 2
def baseEnd_2622142 : Nat := 1346419190341785091065995

theorem tailTrace_2622142 : CollatzResearch.WordTrace tailWord_2622142 prefixEnd_2622142 1346419190341785091065995 := by
  unfold tailWord_2622142
  simp only [CollatzResearch.WordTrace]
  refine ⟨11954671958304354380680585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63758250444289890030296453 11954671958304354380680585)
  ·
    refine ⟨8966003968728265785510439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11954671958304354380680585 8966003968728265785510439)
    ·
      refine ⟨13449005953092398678265659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8966003968728265785510439 13449005953092398678265659)
      ·
        refine ⟨20173508929638598017398489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13449005953092398678265659 20173508929638598017398489)
        ·
          refine ⟨15130131697228948513048867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20173508929638598017398489 15130131697228948513048867)
          ·
            refine ⟨22695197545843422769573301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15130131697228948513048867 22695197545843422769573301)
            ·
              refine ⟨2127674769922820884647497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22695197545843422769573301 2127674769922820884647497)
              ·
                refine ⟨1595756077442115663485623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2127674769922820884647497 1595756077442115663485623)
                ·
                  refine ⟨2393634116163173495228435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595756077442115663485623 2393634116163173495228435)
                  ·
                    refine ⟨3590451174244760242842653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2393634116163173495228435 3590451174244760242842653)
                    ·
                      refine ⟨1346419190341785091065995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3590451174244760242842653 1346419190341785091065995)
                      ·
                        rfl

theorem cell23_2622142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_2622142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622142 prefixEnd_2622142 := by exact prefixLift 2622142
  have htrace : WordTrace (prefixWord ++ tailWord_2622142) baseStart_2622142 baseEnd_2622142 := by
    simpa [prefixWord, tailWord_2622142, baseEnd_2622142] using wordTrace_append hprefix tailTrace_2622142
  have hstable : (prefixWord ++ tailWord_2622142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622142).length < 2 ^ (prefixWord ++ tailWord_2622142).sum := by decide
  have hdescent : baseEnd_2622142 < baseStart_2622142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622144 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 6]
def baseStart_2622144 : Nat := 118140960795 + 2622144 * 2 ^ 59
def prefixEnd_2622144 : Nat := 4983230072969 + 3 ^ 40 * 2622144 * 2
def baseEnd_2622144 : Nat := 1346420217303094083240985

theorem tailTrace_2622144 : CollatzResearch.WordTrace tailWord_2622144 prefixEnd_2622144 1346420217303094083240985 := by
  unfold tailWord_2622144
  simp only [CollatzResearch.WordTrace]
  refine ⟨47818724306213794693508743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63758299074951726258011657 47818724306213794693508743)
  ·
    refine ⟨71728086459320692040263115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47818724306213794693508743 71728086459320692040263115)
    ·
      refine ⟨107592129688981038060394673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71728086459320692040263115 107592129688981038060394673)
      ·
        refine ⟨80694097266735778545296005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107592129688981038060394673 80694097266735778545296005)
        ·
          refine ⟨15130143237512958477243001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80694097266735778545296005 15130143237512958477243001)
          ·
            refine ⟨11347607428134718857932251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15130143237512958477243001 11347607428134718857932251)
            ·
              refine ⟨17021411142202078286898377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11347607428134718857932251 17021411142202078286898377)
              ·
                refine ⟨12766058356651558715173783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17021411142202078286898377 12766058356651558715173783)
                ·
                  refine ⟨19149087534977338072760675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12766058356651558715173783 19149087534977338072760675)
                  ·
                    refine ⟨28723631302466007109141013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19149087534977338072760675 28723631302466007109141013)
                    ·
                      refine ⟨1346420217303094083240985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28723631302466007109141013 1346420217303094083240985)
                      ·
                        rfl

theorem cell23_2622144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_2622144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622144 prefixEnd_2622144 := by exact prefixLift 2622144
  have htrace : WordTrace (prefixWord ++ tailWord_2622144) baseStart_2622144 baseEnd_2622144 := by
    simpa [prefixWord, tailWord_2622144, baseEnd_2622144] using wordTrace_append hprefix tailTrace_2622144
  have hstable : (prefixWord ++ tailWord_2622144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622144).length < 2 ^ (prefixWord ++ tailWord_2622144).sum := by decide
  have hdescent : baseEnd_2622144 < baseStart_2622144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622154 : List Nat := [3, 1, 2, 1, 4, 1, 1, 10]
def baseStart_2622154 : Nat := 118140960795 + 2622154 * 2 ^ 59
def prefixEnd_2622154 : Nat := 4983230072969 + 3 ^ 40 * 2622154 * 2
def baseEnd_2622154 : Nat := 49867605633690334967257

theorem tailTrace_2622154 : CollatzResearch.WordTrace tailWord_2622154 prefixEnd_2622154 49867605633690334967257 := by
  unfold tailWord_2622154
  simp only [CollatzResearch.WordTrace]
  refine ⟨23909453335597840273720379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63758542228260907396587677 23909453335597840273720379)
  ·
    refine ⟨35864180003396760410580569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23909453335597840273720379 35864180003396760410580569)
    ·
      refine ⟨26898135002547570307935427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35864180003396760410580569 26898135002547570307935427)
      ·
        refine ⟨40347202503821355461903141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26898135002547570307935427 40347202503821355461903141)
        ·
          refine ⟨7565100469466504149106839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40347202503821355461903141 7565100469466504149106839)
          ·
            refine ⟨11347650704199756223660259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7565100469466504149106839 11347650704199756223660259)
            ·
              refine ⟨17021476056299634335490389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11347650704199756223660259 17021476056299634335490389)
              ·
                refine ⟨49867605633690334967257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17021476056299634335490389 49867605633690334967257)
                ·
                  rfl

theorem cell23_2622154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 10].length) (baseStart_2622154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622154 prefixEnd_2622154 := by exact prefixLift 2622154
  have htrace : WordTrace (prefixWord ++ tailWord_2622154) baseStart_2622154 baseEnd_2622154 := by
    simpa [prefixWord, tailWord_2622154, baseEnd_2622154] using wordTrace_append hprefix tailTrace_2622154
  have hstable : (prefixWord ++ tailWord_2622154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622154).length < 2 ^ (prefixWord ++ tailWord_2622154).sum := by decide
  have hdescent : baseEnd_2622154 < baseStart_2622154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622158 : List Nat := [4, 1, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_2622158 : Nat := 118140960795 + 2622158 * 2 ^ 59
def prefixEnd_2622158 : Nat := 4983230072969 + 3 ^ 40 * 2622158 * 2
def baseEnd_2622158 : Nat := 448809135344085676155307

theorem tailTrace_2622158 : CollatzResearch.WordTrace tailWord_2622158 prefixEnd_2622158 448809135344085676155307 := by
  unfold tailWord_2622158
  simp only [CollatzResearch.WordTrace]
  refine ⟨11954744904297108722253391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63758639489584579852018085 11954744904297108722253391)
  ·
    refine ⟨17932117356445663083380087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11954744904297108722253391 17932117356445663083380087)
    ·
      refine ⟨26898176034668494625070131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17932117356445663083380087 26898176034668494625070131)
      ·
        refine ⟨40347264052002741937605197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26898176034668494625070131 40347264052002741937605197)
        ·
          refine ⟨15130224019501028226601949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40347264052002741937605197 15130224019501028226601949)
          ·
            refine ⟨5673834007312885584975731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15130224019501028226601949 5673834007312885584975731)
            ·
              refine ⟨8510751010969328377463597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5673834007312885584975731 8510751010969328377463597)
              ·
                refine ⟨3191531629113498141548849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8510751010969328377463597 3191531629113498141548849)
                ·
                  refine ⟨2393648721835123606161637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3191531629113498141548849 2393648721835123606161637)
                  ·
                    refine ⟨448809135344085676155307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2393648721835123606161637 448809135344085676155307)
                    ·
                      rfl

theorem cell23_2622158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_2622158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622158 prefixEnd_2622158 := by exact prefixLift 2622158
  have htrace : WordTrace (prefixWord ++ tailWord_2622158) baseStart_2622158 baseEnd_2622158 := by
    simpa [prefixWord, tailWord_2622158, baseEnd_2622158] using wordTrace_append hprefix tailTrace_2622158
  have hstable : (prefixWord ++ tailWord_2622158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622158).length < 2 ^ (prefixWord ++ tailWord_2622158).sum := by decide
  have hdescent : baseEnd_2622158 < baseStart_2622158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622168 : List Nat := [2, 1, 2, 2, 3, 2, 3, 2, 1, 2, 3]
def baseStart_2622168 : Nat := 118140960795 + 2622168 * 2 ^ 59
def prefixEnd_2622168 : Nat := 4983230072969 + 3 ^ 40 * 2622168 * 2
def baseEnd_2622168 : Nat := 1346432540838801989340875

theorem tailTrace_2622168 : CollatzResearch.WordTrace tailWord_2622168 prefixEnd_2622168 1346432540838801989340875 := by
  unfold tailWord_2622168
  simp only [CollatzResearch.WordTrace]
  refine ⟨47819161982170320742945579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63758882642893760990594105 47819161982170320742945579)
  ·
    refine ⟨71728742973255481114418369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47819161982170320742945579 71728742973255481114418369)
    ·
      refine ⟨53796557229941610835813777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71728742973255481114418369 53796557229941610835813777)
      ·
        refine ⟨40347417922456208126860333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53796557229941610835813777 40347417922456208126860333)
        ·
          refine ⟨15130281720921078047572625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40347417922456208126860333 15130281720921078047572625)
          ·
            refine ⟨11347711290690808535679469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15130281720921078047572625 11347711290690808535679469)
            ·
              refine ⟨4255391734009053200879801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11347711290690808535679469 4255391734009053200879801)
              ·
                refine ⟨3191543800506789900659851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4255391734009053200879801 3191543800506789900659851)
                ·
                  refine ⟨4787315700760184850989777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3191543800506789900659851 4787315700760184850989777)
                  ·
                    refine ⟨3590486775570138638242333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4787315700760184850989777 3590486775570138638242333)
                    ·
                      refine ⟨1346432540838801989340875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3590486775570138638242333 1346432540838801989340875)
                      ·
                        rfl

theorem cell23_2622168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_2622168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622168 prefixEnd_2622168 := by exact prefixLift 2622168
  have htrace : WordTrace (prefixWord ++ tailWord_2622168) baseStart_2622168 baseEnd_2622168 := by
    simpa [prefixWord, tailWord_2622168, baseEnd_2622168] using wordTrace_append hprefix tailTrace_2622168
  have hstable : (prefixWord ++ tailWord_2622168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622168).length < 2 ^ (prefixWord ++ tailWord_2622168).sum := by decide
  have hdescent : baseEnd_2622168 < baseStart_2622168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622181 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 3, 3, 3]
def baseStart_2622181 : Nat := 118140960795 + 2622181 * 2 ^ 59
def prefixEnd_2622181 : Nat := 4983230072969 + 3 ^ 40 * 2622181 * 2
def baseEnd_2622181 : Nat := 1346439216087310438478315

theorem tailTrace_2622181 : CollatzResearch.WordTrace tailWord_2622181 prefixEnd_2622181 1346439216087310438478315 := by
  unfold tailWord_2622181
  simp only [CollatzResearch.WordTrace]
  refine ⟨95638798113293544706114397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63759198742195696470742931 95638798113293544706114397)
  ·
    refine ⟨35864549292485079264792899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95638798113293544706114397 35864549292485079264792899)
    ·
      refine ⟨53796823938727618897189349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35864549292485079264792899 53796823938727618897189349)
      ·
        refine ⟨10086904488511428543223003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53796823938727618897189349 10086904488511428543223003)
        ·
          refine ⟨15130356732767142814834505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10086904488511428543223003 15130356732767142814834505)
          ·
            refine ⟨11347767549575357111125879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15130356732767142814834505 11347767549575357111125879)
            ·
              refine ⟨17021651324363035666688819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11347767549575357111125879 17021651324363035666688819)
              ·
                refine ⟨25532476986544553500033229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17021651324363035666688819 25532476986544553500033229)
                ·
                  refine ⟨9574678869954207562512461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25532476986544553500033229 9574678869954207562512461)
                  ·
                    refine ⟨3590504576232827835942173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9574678869954207562512461 3590504576232827835942173)
                    ·
                      refine ⟨1346439216087310438478315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3590504576232827835942173 1346439216087310438478315)
                      ·
                        rfl

theorem cell23_2622181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_2622181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622181 prefixEnd_2622181 := by exact prefixLift 2622181
  have htrace : WordTrace (prefixWord ++ tailWord_2622181) baseStart_2622181 baseEnd_2622181 := by
    simpa [prefixWord, tailWord_2622181, baseEnd_2622181] using wordTrace_append hprefix tailTrace_2622181
  have hstable : (prefixWord ++ tailWord_2622181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622181).length < 2 ^ (prefixWord ++ tailWord_2622181).sum := by decide
  have hdescent : baseEnd_2622181 < baseStart_2622181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622215 : List Nat := [1, 1, 4, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2622215 : Nat := 118140960795 + 2622215 * 2 ^ 59
def prefixEnd_2622215 : Nat := 4983230072969 + 3 ^ 40 * 2622215 * 2
def baseEnd_2622215 : Nat := 1346456674429563305453159

theorem tailTrace_2622215 : CollatzResearch.WordTrace tailWord_2622215 prefixEnd_2622215 1346456674429563305453159 := by
  unfold tailWord_2622215
  simp only [CollatzResearch.WordTrace]
  refine ⟨95640038195170368512852099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63760025463446912341901399 95640038195170368512852099)
  ·
    refine ⟨143460057292755552769278149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95640038195170368512852099 143460057292755552769278149)
    ·
      refine ⟨26898760742391666144239653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143460057292755552769278149 26898760742391666144239653)
      ·
        refine ⟨5043517639198437402044935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26898760742391666144239653 5043517639198437402044935)
        ·
          refine ⟨7565276458797656103067403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5043517639198437402044935 7565276458797656103067403)
          ·
            refine ⟨11347914688196484154601105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7565276458797656103067403 11347914688196484154601105)
            ·
              refine ⟨8510936016147363115950829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11347914688196484154601105 8510936016147363115950829)
              ·
                refine ⟨3191601006055261168481561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8510936016147363115950829 3191601006055261168481561)
                ·
                  refine ⟨2393700754541445876361171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3191601006055261168481561 2393700754541445876361171)
                  ·
                    refine ⟨3590551131812168814541757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2393700754541445876361171 3590551131812168814541757)
                    ·
                      refine ⟨1346456674429563305453159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3590551131812168814541757 1346456674429563305453159)
                      ·
                        rfl

theorem cell23_2622215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2622215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622215 prefixEnd_2622215 := by exact prefixLift 2622215
  have htrace : WordTrace (prefixWord ++ tailWord_2622215) baseStart_2622215 baseEnd_2622215 := by
    simpa [prefixWord, tailWord_2622215, baseEnd_2622215] using wordTrace_append hprefix tailTrace_2622215
  have hstable : (prefixWord ++ tailWord_2622215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622215).length < 2 ^ (prefixWord ++ tailWord_2622215).sum := by decide
  have hdescent : baseEnd_2622215 < baseStart_2622215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622242 : List Nat := [3, 3, 1, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_2622242 : Nat := 118140960795 + 2622242 * 2 ^ 59
def prefixEnd_2622242 : Nat := 4983230072969 + 3 ^ 40 * 2622242 * 2
def baseEnd_2622242 : Nat := 1346470538407234699815535

theorem tailTrace_2622242 : CollatzResearch.WordTrace tailWord_2622242 prefixEnd_2622242 1346470538407234699815535 := by
  unfold tailWord_2622242
  simp only [CollatzResearch.WordTrace]
  refine ⟨23910255741518138031021245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63760681977381701416056653 23910255741518138031021245)
  ·
    refine ⟨8966345903069301761632967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23910255741518138031021245 8966345903069301761632967)
    ·
      refine ⟨13449518854603952642449451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8966345903069301761632967 13449518854603952642449451)
      ·
        refine ⟨20174278281905928963674177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13449518854603952642449451 20174278281905928963674177)
        ·
          refine ⟨15130708711429446722755633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20174278281905928963674177 15130708711429446722755633)
          ·
            refine ⟨11348031533572085042066725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15130708711429446722755633 11348031533572085042066725)
            ·
              refine ⟨2127755912544765945387511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11348031533572085042066725 2127755912544765945387511)
              ·
                refine ⟨3191633868817148918081267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127755912544765945387511 3191633868817148918081267)
                ·
                  refine ⟨4787450803225723377121901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3191633868817148918081267 4787450803225723377121901)
                  ·
                    refine ⟨1795294051209646266420713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4787450803225723377121901 1795294051209646266420713)
                    ·
                      refine ⟨1346470538407234699815535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1795294051209646266420713 1346470538407234699815535)
                      ·
                        rfl

theorem cell23_2622242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_2622242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622242 prefixEnd_2622242 := by exact prefixLift 2622242
  have htrace : WordTrace (prefixWord ++ tailWord_2622242) baseStart_2622242 baseEnd_2622242 := by
    simpa [prefixWord, tailWord_2622242, baseEnd_2622242] using wordTrace_append hprefix tailTrace_2622242
  have hstable : (prefixWord ++ tailWord_2622242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622242).length < 2 ^ (prefixWord ++ tailWord_2622242).sum := by decide
  have hdescent : baseEnd_2622242 < baseStart_2622242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622261 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 7]
def baseStart_2622261 : Nat := 118140960795 + 2622261 * 2 ^ 59
def prefixEnd_2622261 : Nat := 4983230072969 + 3 ^ 40 * 2622261 * 2
def baseEnd_2622261 : Nat := 149608921615518902830883

theorem tailTrace_2622261 : CollatzResearch.WordTrace tailWord_2622261 prefixEnd_2622261 149608921615518902830883 := by
  unfold tailWord_2622261
  simp only [CollatzResearch.WordTrace]
  refine ⟨95641715953003718369026637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63761143968669145579351091 95641715953003718369026637)
  ·
    refine ⟨35865643482376394388384989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95641715953003718369026637 35865643482376394388384989)
    ·
      refine ⟨13449616305891147895644371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35865643482376394388384989 13449616305891147895644371)
      ·
        refine ⟨20174424458836721843466557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13449616305891147895644371 20174424458836721843466557)
        ·
          refine ⟨7565409172063770691299959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20174424458836721843466557 7565409172063770691299959)
          ·
            refine ⟨11348113758095656036949939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7565409172063770691299959 11348113758095656036949939)
            ·
              refine ⟨17022170637143484055424909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11348113758095656036949939 17022170637143484055424909)
              ·
                refine ⟨6383313988928806520784341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17022170637143484055424909 6383313988928806520784341)
                ·
                  refine ⟨149608921615518902830883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6383313988928806520784341 149608921615518902830883)
                  ·
                    rfl

theorem cell23_2622261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_2622261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622261 prefixEnd_2622261 := by exact prefixLift 2622261
  have htrace : WordTrace (prefixWord ++ tailWord_2622261) baseStart_2622261 baseEnd_2622261 := by
    simpa [prefixWord, tailWord_2622261, baseEnd_2622261] using wordTrace_append hprefix tailTrace_2622261
  have hstable : (prefixWord ++ tailWord_2622261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622261).length < 2 ^ (prefixWord ++ tailWord_2622261).sum := by decide
  have hdescent : baseEnd_2622261 < baseStart_2622261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622295 : List Nat := [1, 1, 3, 2, 4, 3, 1, 3, 5]
def baseStart_2622295 : Nat := 118140960795 + 2622295 * 2 ^ 59
def prefixEnd_2622295 : Nat := 4983230072969 + 3 ^ 40 * 2622295 * 2
def baseEnd_2622295 : Nat := 149610861431324776939199

theorem tailTrace_2622295 : CollatzResearch.WordTrace tailWord_2622295 prefixEnd_2622295 149610861431324776939199 := by
  unfold tailWord_2622295
  simp only [CollatzResearch.WordTrace]
  refine ⟨95642956034880542175764339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63761970689920361450509559 95642956034880542175764339)
  ·
    refine ⟨143464434052320813263646509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95642956034880542175764339 143464434052320813263646509)
    ·
      refine ⟨53799162769620304973867441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143464434052320813263646509 53799162769620304973867441)
      ·
        refine ⟨40349372077215228730400581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53799162769620304973867441 40349372077215228730400581)
        ·
          refine ⟨7565507264477855386950109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40349372077215228730400581 7565507264477855386950109)
          ·
            refine ⟨2837065224179195770106291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7565507264477855386950109 2837065224179195770106291)
            ·
              refine ⟨4255597836268793655159437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2837065224179195770106291 4255597836268793655159437)
              ·
                refine ⟨1595849188600797620684789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4255597836268793655159437 1595849188600797620684789)
                ·
                  refine ⟨149610861431324776939199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1595849188600797620684789 149610861431324776939199)
                  ·
                    rfl

theorem cell23_2622295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 5].length) (baseStart_2622295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622295 prefixEnd_2622295 := by exact prefixLift 2622295
  have htrace : WordTrace (prefixWord ++ tailWord_2622295) baseStart_2622295 baseEnd_2622295 := by
    simpa [prefixWord, tailWord_2622295, baseEnd_2622295] using wordTrace_append hprefix tailTrace_2622295
  have hstable : (prefixWord ++ tailWord_2622295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622295).length < 2 ^ (prefixWord ++ tailWord_2622295).sum := by decide
  have hdescent : baseEnd_2622295 < baseStart_2622295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622308 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_2622308 : Nat := 118140960795 + 2622308 * 2 ^ 59
def prefixEnd_2622308 : Nat := 4983230072969 + 3 ^ 40 * 2622308 * 2
def baseEnd_2622308 : Nat := 448834809376810480530077

theorem tailTrace_2622308 : CollatzResearch.WordTrace tailWord_2622308 prefixEnd_2622308 448834809376810480530077 := by
  unfold tailWord_2622308
  simp only [CollatzResearch.WordTrace]
  refine ⟨47821715091916722697993789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63762286789222296930658385 47821715091916722697993789)
  ·
    refine ⟨17933143159468771011747671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47821715091916722697993789 17933143159468771011747671)
    ·
      refine ⟨26899714739203156517621507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17933143159468771011747671 26899714739203156517621507)
      ·
        refine ⟨40349572108804734776432261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26899714739203156517621507 40349572108804734776432261)
        ·
          refine ⟨7565544770400887770581049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40349572108804734776432261 7565544770400887770581049)
          ·
            refine ⟨5674158577800665827935787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7565544770400887770581049 5674158577800665827935787)
            ·
              refine ⟨8511237866700998741903681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5674158577800665827935787 8511237866700998741903681)
              ·
                refine ⟨6383428400025749056427761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8511237866700998741903681 6383428400025749056427761)
                ·
                  refine ⟨4787571300019311792320821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6383428400025749056427761 4787571300019311792320821)
                  ·
                    refine ⟨448834809376810480530077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4787571300019311792320821 448834809376810480530077)
                    ·
                      rfl

theorem cell23_2622308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_2622308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622308 prefixEnd_2622308 := by exact prefixLift 2622308
  have htrace : WordTrace (prefixWord ++ tailWord_2622308) baseStart_2622308 baseEnd_2622308 := by
    simpa [prefixWord, tailWord_2622308, baseEnd_2622308] using wordTrace_append hprefix tailTrace_2622308
  have hstable : (prefixWord ++ tailWord_2622308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622308).length < 2 ^ (prefixWord ++ tailWord_2622308).sum := by decide
  have hdescent : baseEnd_2622308 < baseStart_2622308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622331 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 3]
def baseStart_2622331 : Nat := 118140960795 + 2622331 * 2 ^ 59
def prefixEnd_2622331 : Nat := 4983230072969 + 3 ^ 40 * 2622331 * 2
def baseEnd_2622331 : Nat := 1346516238185484851602625

theorem tailTrace_2622331 : CollatzResearch.WordTrace tailWord_2622331 prefixEnd_2622331 1346516238185484851602625 := by
  unfold tailWord_2622331
  simp only [CollatzResearch.WordTrace]
  refine ⟨95644269062750120324074847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63762846041833413549383231 95644269062750120324074847)
  ·
    refine ⟨143466403594125180486112271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95644269062750120324074847 143466403594125180486112271)
    ·
      refine ⟨215199605391187770729168407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143466403594125180486112271 215199605391187770729168407)
      ·
        refine ⟨322799408086781656093752611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215199605391187770729168407 322799408086781656093752611)
        ·
          refine ⟨484199112130172484140628917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322799408086781656093752611 484199112130172484140628917)
          ·
            refine ⟨45393666762203670388183961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 484199112130172484140628917 45393666762203670388183961)
            ·
              refine ⟨34045250071652752791137971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45393666762203670388183961 34045250071652752791137971)
              ·
                refine ⟨51067875107479129186706957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34045250071652752791137971 51067875107479129186706957)
                ·
                  refine ⟨19150453165304673445015109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51067875107479129186706957 19150453165304673445015109)
                  ·
                    refine ⟨3590709968494626270940333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19150453165304673445015109 3590709968494626270940333)
                    ·
                      refine ⟨1346516238185484851602625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3590709968494626270940333 1346516238185484851602625)
                      ·
                        rfl

theorem cell23_2622331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 3].length) (baseStart_2622331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622331 prefixEnd_2622331 := by exact prefixLift 2622331
  have htrace : WordTrace (prefixWord ++ tailWord_2622331) baseStart_2622331 baseEnd_2622331 := by
    simpa [prefixWord, tailWord_2622331, baseEnd_2622331] using wordTrace_append hprefix tailTrace_2622331
  have hstable : (prefixWord ++ tailWord_2622331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622331).length < 2 ^ (prefixWord ++ tailWord_2622331).sum := by decide
  have hdescent : baseEnd_2622331 < baseStart_2622331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622348 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 2, 2, 3]
def baseStart_2622348 : Nat := 118140960795 + 2622348 * 2 ^ 59
def prefixEnd_2622348 : Nat := 4983230072969 + 3 ^ 40 * 2622348 * 2
def baseEnd_2622348 : Nat := 1346524967356611285090047

theorem tailTrace_2622348 : CollatzResearch.WordTrace tailWord_2622348 prefixEnd_2622348 1346524967356611285090047 := by
  unfold tailWord_2622348
  simp only [CollatzResearch.WordTrace]
  refine ⟨47822444551844266113721849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63763259402459021484962465 47822444551844266113721849)
  ·
    refine ⟨35866833413883199585291387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47822444551844266113721849 35866833413883199585291387)
    ·
      refine ⟨53800250120824799377937081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35866833413883199585291387 53800250120824799377937081)
      ·
        refine ⟨40350187590618599533452811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53800250120824799377937081 40350187590618599533452811)
        ·
          refine ⟨60525281385927899300179217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40350187590618599533452811 60525281385927899300179217)
          ·
            refine ⟨45393961039445924475134413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60525281385927899300179217 45393961039445924475134413)
            ·
              refine ⟨17022735389792221678175405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45393961039445924475134413 17022735389792221678175405)
              ·
                refine ⟨6383525771172083129315777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17022735389792221678175405 6383525771172083129315777)
                ·
                  refine ⟨4787644328379062346986833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6383525771172083129315777 4787644328379062346986833)
                  ·
                    refine ⟨3590733246284296760240125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4787644328379062346986833 3590733246284296760240125)
                    ·
                      refine ⟨1346524967356611285090047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3590733246284296760240125 1346524967356611285090047)
                      ·
                        rfl

theorem cell23_2622348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_2622348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622348 prefixEnd_2622348 := by exact prefixLift 2622348
  have htrace : WordTrace (prefixWord ++ tailWord_2622348) baseStart_2622348 baseEnd_2622348 := by
    simpa [prefixWord, tailWord_2622348, baseEnd_2622348] using wordTrace_append hprefix tailTrace_2622348
  have hstable : (prefixWord ++ tailWord_2622348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622348).length < 2 ^ (prefixWord ++ tailWord_2622348).sum := by decide
  have hdescent : baseEnd_2622348 < baseStart_2622348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622398 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_2622398 : Nat := 118140960795 + 2622398 * 2 ^ 59
def prefixEnd_2622398 : Nat := 4983230072969 + 3 ^ 40 * 2622398 * 2
def baseEnd_2622398 : Nat := 448850213796445363154939

theorem tailTrace_2622398 : CollatzResearch.WordTrace tailWord_2622398 prefixEnd_2622398 448850213796445363154939 := by
  unfold tailWord_2622398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11955839094188423845845481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63764475169004927177842565 11955839094188423845845481)
  ·
    refine ⟨8966879320641317884384111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11955839094188423845845481 8966879320641317884384111)
    ·
      refine ⟨13450318980961976826576167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8966879320641317884384111 13450318980961976826576167)
      ·
        refine ⟨20175478471442965239864251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13450318980961976826576167 20175478471442965239864251)
        ·
          refine ⟨30263217707164447859796377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20175478471442965239864251 30263217707164447859796377)
          ·
            refine ⟨22697413280373335894847283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30263217707164447859796377 22697413280373335894847283)
            ·
              refine ⟨34046119920560003842270925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22697413280373335894847283 34046119920560003842270925)
              ·
                refine ⟨12767294970210001440851597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34046119920560003842270925 12767294970210001440851597)
                ·
                  refine ⟨4787735613828750540319349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12767294970210001440851597 4787735613828750540319349)
                  ·
                    refine ⟨448850213796445363154939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4787735613828750540319349 448850213796445363154939)
                    ·
                      rfl

theorem cell23_2622398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_2622398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622398 prefixEnd_2622398 := by exact prefixLift 2622398
  have htrace : WordTrace (prefixWord ++ tailWord_2622398) baseStart_2622398 baseEnd_2622398 := by
    simpa [prefixWord, tailWord_2622398, baseEnd_2622398] using wordTrace_append hprefix tailTrace_2622398
  have hstable : (prefixWord ++ tailWord_2622398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622398).length < 2 ^ (prefixWord ++ tailWord_2622398).sum := by decide
  have hdescent : baseEnd_2622398 < baseStart_2622398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622415 : List Nat := [1, 1, 2, 1, 1, 6, 4, 1, 1, 5]
def baseStart_2622415 : Nat := 118140960795 + 2622415 * 2 ^ 59
def prefixEnd_2622415 : Nat := 4983230072969 + 3 ^ 40 * 2622415 * 2
def baseEnd_2622415 : Nat := 448853123520154174317413

theorem tailTrace_2622415 : CollatzResearch.WordTrace tailWord_2622415 prefixEnd_2622415 448853123520154174317413 := by
  unfold tailWord_2622415
  simp only [CollatzResearch.WordTrace]
  refine ⟨95647332794445802670132699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63764888529630535113421799 95647332794445802670132699)
  ·
    refine ⟨143470999191668704005199049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95647332794445802670132699 143470999191668704005199049)
    ·
      refine ⟨107603249393751528003899287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143470999191668704005199049 107603249393751528003899287)
      ·
        refine ⟨161404874090627292005848931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107603249393751528003899287 161404874090627292005848931)
        ·
          refine ⟨242107311135940938008773397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161404874090627292005848931 242107311135940938008773397)
          ·
            refine ⟨11348780209497231469161253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 242107311135940938008773397 11348780209497231469161253)
            ·
              refine ⟨2127896289280730900467735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11348780209497231469161253 2127896289280730900467735)
              ·
                refine ⟨3191844433921096350701603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127896289280730900467735 3191844433921096350701603)
                ·
                  refine ⟨4787766650881644526052405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3191844433921096350701603 4787766650881644526052405)
                  ·
                    refine ⟨448853123520154174317413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4787766650881644526052405 448853123520154174317413)
                    ·
                      rfl

theorem cell23_2622415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 1, 5].length) (baseStart_2622415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622415 prefixEnd_2622415 := by exact prefixLift 2622415
  have htrace : WordTrace (prefixWord ++ tailWord_2622415) baseStart_2622415 baseEnd_2622415 := by
    simpa [prefixWord, tailWord_2622415, baseEnd_2622415] using wordTrace_append hprefix tailTrace_2622415
  have hstable : (prefixWord ++ tailWord_2622415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622415).length < 2 ^ (prefixWord ++ tailWord_2622415).sum := by decide
  have hdescent : baseEnd_2622415 < baseStart_2622415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622429 : List Nat := [1, 4, 3, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_2622429 : Nat := 118140960795 + 2622429 * 2 ^ 59
def prefixEnd_2622429 : Nat := 4983230072969 + 3 ^ 40 * 2622429 * 2
def baseEnd_2622429 : Nat := 1346566559289625468177175

theorem tailTrace_2622429 : CollatzResearch.WordTrace tailWord_2622429 prefixEnd_2622429 1346566559289625468177175 := by
  unfold tailWord_2622429
  simp only [CollatzResearch.WordTrace]
  refine ⟨95647843416395083061142341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63765228944263388707428227 95647843416395083061142341)
  ·
    refine ⟨17933970640574078073964189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95647843416395083061142341 17933970640574078073964189)
    ·
      refine ⟨6725238990215279277736571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17933970640574078073964189 6725238990215279277736571)
      ·
        refine ⟨10087858485322918916604857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6725238990215279277736571 10087858485322918916604857)
        ·
          refine ⟨7565893863992189187453643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10087858485322918916604857 7565893863992189187453643)
          ·
            refine ⟨11348840795988283781180465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7565893863992189187453643 11348840795988283781180465)
            ·
              refine ⟨8511630596991212835885349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11348840795988283781180465 8511630596991212835885349)
              ·
                refine ⟨1595930736935852406728503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8511630596991212835885349 1595930736935852406728503)
                ·
                  refine ⟨2393896105403778610092755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595930736935852406728503 2393896105403778610092755)
                  ·
                    refine ⟨3590844158105667915139133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2393896105403778610092755 3590844158105667915139133)
                    ·
                      refine ⟨1346566559289625468177175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3590844158105667915139133 1346566559289625468177175)
                      ·
                        rfl

theorem cell23_2622429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_2622429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622429 prefixEnd_2622429 := by exact prefixLift 2622429
  have htrace : WordTrace (prefixWord ++ tailWord_2622429) baseStart_2622429 baseEnd_2622429 := by
    simpa [prefixWord, tailWord_2622429, baseEnd_2622429] using wordTrace_append hprefix tailTrace_2622429
  have hstable : (prefixWord ++ tailWord_2622429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622429).length < 2 ^ (prefixWord ++ tailWord_2622429).sum := by decide
  have hdescent : baseEnd_2622429 < baseStart_2622429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622491 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 10]
def baseStart_2622491 : Nat := 118140960795 + 2622491 * 2 ^ 59
def prefixEnd_2622491 : Nat := 4983230072969 + 3 ^ 40 * 2622491 * 2
def baseEnd_2622491 : Nat := 1346598395090204225601889

theorem tailTrace_2622491 : CollatzResearch.WordTrace tailWord_2622491 prefixEnd_2622491 1346598395090204225601889 := by
  unfold tailWord_2622491
  simp only [CollatzResearch.WordTrace]
  refine ⟨95650104742170467649899327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63766736494780311766599551 95650104742170467649899327)
  ·
    refine ⟨143475157113255701474848991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95650104742170467649899327 143475157113255701474848991)
    ·
      refine ⟨215212735669883552212273487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143475157113255701474848991 215212735669883552212273487)
      ·
        refine ⟨322819103504825328318410231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215212735669883552212273487 322819103504825328318410231)
        ·
          refine ⟨484228655257237992477615347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322819103504825328318410231 484228655257237992477615347)
          ·
            refine ⟨726342982885856988716423021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484228655257237992477615347 726342982885856988716423021)
            ·
              refine ⟨272378618582196370768658633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 726342982885856988716423021 272378618582196370768658633)
              ·
                refine ⟨204283963936647278076493975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272378618582196370768658633 204283963936647278076493975)
                ·
                  refine ⟨306425945904970917114740963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204283963936647278076493975 306425945904970917114740963)
                  ·
                    refine ⟨459638918857456375672111445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 306425945904970917114740963 459638918857456375672111445)
                    ·
                      refine ⟨1346598395090204225601889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 459638918857456375672111445 1346598395090204225601889)
                      ·
                        rfl

theorem cell23_2622491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_2622491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622491 prefixEnd_2622491 := by exact prefixLift 2622491
  have htrace : WordTrace (prefixWord ++ tailWord_2622491) baseStart_2622491 baseEnd_2622491 := by
    simpa [prefixWord, tailWord_2622491, baseEnd_2622491] using wordTrace_append hprefix tailTrace_2622491
  have hstable : (prefixWord ++ tailWord_2622491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622491).length < 2 ^ (prefixWord ++ tailWord_2622491).sum := by decide
  have hdescent : baseEnd_2622491 < baseStart_2622491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622496 : List Nat := [2, 1, 1, 7, 1, 2, 2, 1, 2, 4]
def baseStart_2622496 : Nat := 118140960795 + 2622496 * 2 ^ 59
def prefixEnd_2622496 : Nat := 4983230072969 + 3 ^ 40 * 2622496 * 2
def baseEnd_2622496 : Nat := 448866987497825568679789

theorem tailTrace_2622496 : CollatzResearch.WordTrace tailWord_2622496 prefixEnd_2622496 448866987497825568679789 := by
  unfold tailWord_2622496
  simp only [CollatzResearch.WordTrace]
  refine ⟨47825143553576176751915671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63766858071434902335887561 47825143553576176751915671)
  ·
    refine ⟨71737715330364265127873507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47825143553576176751915671 71737715330364265127873507)
    ·
      refine ⟨107606572995546397691810261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71737715330364265127873507 107606572995546397691810261)
      ·
        refine ⟨2522029054583118695901803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 107606572995546397691810261 2522029054583118695901803)
        ·
          refine ⟨3783043581874678043852705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2522029054583118695901803 3783043581874678043852705)
          ·
            refine ⟨2837282686406008532889529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3783043581874678043852705 2837282686406008532889529)
            ·
              refine ⟨2127962014804506399667147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2837282686406008532889529 2127962014804506399667147)
              ·
                refine ⟨3191943022206759599500721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127962014804506399667147 3191943022206759599500721)
                ·
                  refine ⟨2393957266655069699625541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3191943022206759599500721 2393957266655069699625541)
                  ·
                    refine ⟨448866987497825568679789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2393957266655069699625541 448866987497825568679789)
                    ·
                      rfl

theorem cell23_2622496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 2, 4].length) (baseStart_2622496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622496 prefixEnd_2622496 := by exact prefixLift 2622496
  have htrace : WordTrace (prefixWord ++ tailWord_2622496) baseStart_2622496 baseEnd_2622496 := by
    simpa [prefixWord, tailWord_2622496, baseEnd_2622496] using wordTrace_append hprefix tailTrace_2622496
  have hstable : (prefixWord ++ tailWord_2622496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622496).length < 2 ^ (prefixWord ++ tailWord_2622496).sum := by decide
  have hdescent : baseEnd_2622496 < baseStart_2622496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622506 : List Nat := [3, 1, 4, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_2622506 : Nat := 118140960795 + 2622506 * 2 ^ 59
def prefixEnd_2622506 : Nat := 4983230072969 + 3 ^ 40 * 2622506 * 2
def baseEnd_2622506 : Nat := 1346606097300021666914321

theorem tailTrace_2622506 : CollatzResearch.WordTrace tailWord_2622506 prefixEnd_2622506 1346606097300021666914321 := by
  unfold tailWord_2622506
  simp only [CollatzResearch.WordTrace]
  refine ⟨23912662959279031302923843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63767101224744083474463581 23912662959279031302923843)
  ·
    refine ⟨35868994438918546954385765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23912662959279031302923843 35868994438918546954385765)
    ·
      refine ⟨6725436457297227553947331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35868994438918546954385765 6725436457297227553947331)
      ·
        refine ⟨10088154685945841330920997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6725436457297227553947331 10088154685945841330920997)
        ·
          refine ⟨1891529003614845249547687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10088154685945841330920997 1891529003614845249547687)
          ·
            refine ⟨2837293505422267874321531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891529003614845249547687 2837293505422267874321531)
            ·
              refine ⟨4255940258133401811482297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2837293505422267874321531 4255940258133401811482297)
              ·
                refine ⟨3191955193600051358611723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4255940258133401811482297 3191955193600051358611723)
                ·
                  refine ⟨4787932790400077037917585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3191955193600051358611723 4787932790400077037917585)
                  ·
                    refine ⟨3590949592800057778438189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4787932790400077037917585 3590949592800057778438189)
                    ·
                      refine ⟨1346606097300021666914321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3590949592800057778438189 1346606097300021666914321)
                      ·
                        rfl

theorem cell23_2622506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_2622506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622506 prefixEnd_2622506 := by exact prefixLift 2622506
  have htrace : WordTrace (prefixWord ++ tailWord_2622506) baseStart_2622506 baseEnd_2622506 := by
    simpa [prefixWord, tailWord_2622506, baseEnd_2622506] using wordTrace_append hprefix tailTrace_2622506
  have hstable : (prefixWord ++ tailWord_2622506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622506).length < 2 ^ (prefixWord ++ tailWord_2622506).sum := by decide
  have hdescent : baseEnd_2622506 < baseStart_2622506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622528 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 5]
def baseStart_2622528 : Nat := 118140960795 + 2622528 * 2 ^ 59
def prefixEnd_2622528 : Nat := 4983230072969 + 3 ^ 40 * 2622528 * 2
def baseEnd_2622528 : Nat := 1346617393874420580839219

theorem tailTrace_2622528 : CollatzResearch.WordTrace tailWord_2622528 prefixEnd_2622528 1346617393874420580839219 := by
  unfold tailWord_2622528
  simp only [CollatzResearch.WordTrace]
  refine ⟨47825727121518211484498119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63767636162024281979330825 47825727121518211484498119)
  ·
    refine ⟨71738590682277317226747179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47825727121518211484498119 71738590682277317226747179)
    ·
      refine ⟨107607886023415975840120769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71738590682277317226747179 107607886023415975840120769)
      ·
        refine ⟨80705914517561981880090577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107607886023415975840120769 80705914517561981880090577)
        ·
          refine ⟨60529435888171486410067933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80705914517561981880090577 60529435888171486410067933)
          ·
            refine ⟨22698538458064307403775475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60529435888171486410067933 22698538458064307403775475)
            ·
              refine ⟨34047807687096461105663213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22698538458064307403775475 34047807687096461105663213)
              ·
                refine ⟨12767927882661172914623705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34047807687096461105663213 12767927882661172914623705)
                ·
                  refine ⟨9575945911995879685967779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12767927882661172914623705 9575945911995879685967779)
                  ·
                    refine ⟨14363918867993819528951669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9575945911995879685967779 14363918867993819528951669)
                    ·
                      refine ⟨1346617393874420580839219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14363918867993819528951669 1346617393874420580839219)
                      ·
                        rfl

theorem cell23_2622528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_2622528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622528 prefixEnd_2622528 := by exact prefixLift 2622528
  have htrace : WordTrace (prefixWord ++ tailWord_2622528) baseStart_2622528 baseEnd_2622528 := by
    simpa [prefixWord, tailWord_2622528, baseEnd_2622528] using wordTrace_append hprefix tailTrace_2622528
  have hstable : (prefixWord ++ tailWord_2622528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622528).length < 2 ^ (prefixWord ++ tailWord_2622528).sum := by decide
  have hdescent : baseEnd_2622528 < baseStart_2622528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622615 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_2622615 : Nat := 118140960795 + 2622615 * 2 ^ 59
def prefixEnd_2622615 : Nat := 4983230072969 + 3 ^ 40 * 2622615 * 2
def baseEnd_2622615 : Nat := 1346662066691361740451319

theorem tailTrace_2622615 : CollatzResearch.WordTrace tailWord_2622615 prefixEnd_2622615 1346662066691361740451319 := by
  unfold tailWord_2622615
  simp only [CollatzResearch.WordTrace]
  refine ⟨95654627393721236827413299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63769751595814157884942199 95654627393721236827413299)
  ·
    refine ⟨143481941090581855241119949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95654627393721236827413299 143481941090581855241119949)
    ·
      refine ⟨53805727908968195715419981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143481941090581855241119949 53805727908968195715419981)
      ·
        refine ⟨20177147965863073393282493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53805727908968195715419981 20177147965863073393282493)
        ·
          refine ⟨7566430487198652522480935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20177147965863073393282493 7566430487198652522480935)
          ·
            refine ⟨11349645730797978783721403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7566430487198652522480935 11349645730797978783721403)
            ·
              refine ⟨17024468596196968175582105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11349645730797978783721403 17024468596196968175582105)
              ·
                refine ⟨12768351447147726131686579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17024468596196968175582105 12768351447147726131686579)
                ·
                  refine ⟨19152527170721589197529869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12768351447147726131686579 19152527170721589197529869)
                  ·
                    refine ⟨7182197689020595949073701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19152527170721589197529869 7182197689020595949073701)
                    ·
                      refine ⟨1346662066691361740451319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7182197689020595949073701 1346662066691361740451319)
                      ·
                        rfl

theorem cell23_2622615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_2622615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622615 prefixEnd_2622615 := by exact prefixLift 2622615
  have htrace : WordTrace (prefixWord ++ tailWord_2622615) baseStart_2622615 baseEnd_2622615 := by
    simpa [prefixWord, tailWord_2622615, baseEnd_2622615] using wordTrace_append hprefix tailTrace_2622615
  have hstable : (prefixWord ++ tailWord_2622615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622615).length < 2 ^ (prefixWord ++ tailWord_2622615).sum := by decide
  have hdescent : baseEnd_2622615 < baseStart_2622615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622646 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2622646 : Nat := 118140960795 + 2622646 * 2 ^ 59
def prefixEnd_2622646 : Nat := 4983230072969 + 3 ^ 40 * 2622646 * 2
def baseEnd_2622646 : Nat := 448892661530550373054559

theorem tailTrace_2622646 : CollatzResearch.WordTrace tailWord_2622646 prefixEnd_2622646 448892661530550373054559 := by
  unfold tailWord_2622646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5978484878538058070111987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63770505371072619414527861 5978484878538058070111987)
  ·
    refine ⟨8967727317807087105167981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5978484878538058070111987 8967727317807087105167981)
    ·
      refine ⟨3362897744177657664437993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8967727317807087105167981 3362897744177657664437993)
      ·
        refine ⟨2522173308133243248328495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3362897744177657664437993 2522173308133243248328495)
        ·
          refine ⟨3783259962199864872492743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2522173308133243248328495 3783259962199864872492743)
          ·
            refine ⟨5674889943299797308739115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783259962199864872492743 5674889943299797308739115)
            ·
              refine ⟨8512334914949695963108673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5674889943299797308739115 8512334914949695963108673)
              ·
                refine ⟨6384251186212271972331505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8512334914949695963108673 6384251186212271972331505)
                ·
                  refine ⟨4788188389659203979248629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6384251186212271972331505 4788188389659203979248629)
                  ·
                    refine ⟨448892661530550373054559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4788188389659203979248629 448892661530550373054559)
                    ·
                      rfl

theorem cell23_2622646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2622646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622646 prefixEnd_2622646 := by exact prefixLift 2622646
  have htrace : WordTrace (prefixWord ++ tailWord_2622646) baseStart_2622646 baseEnd_2622646 := by
    simpa [prefixWord, tailWord_2622646, baseEnd_2622646] using wordTrace_append hprefix tailTrace_2622646
  have hstable : (prefixWord ++ tailWord_2622646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622646).length < 2 ^ (prefixWord ++ tailWord_2622646).sum := by decide
  have hdescent : baseEnd_2622646 < baseStart_2622646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622652 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_2622652 : Nat := 118140960795 + 2622652 * 2 ^ 59
def prefixEnd_2622652 : Nat := 4983230072969 + 3 ^ 40 * 2622652 * 2
def baseEnd_2622652 : Nat := 1346681065475578095688649

theorem tailTrace_2622652 : CollatzResearch.WordTrace tailWord_2622652 prefixEnd_2622652 1346681065475578095688649 := by
  unfold tailWord_2622652
  simp only [CollatzResearch.WordTrace]
  refine ⟨47827988447293596073255105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63770651263058128097673473 47827988447293596073255105)
  ·
    refine ⟨35870991335470197054941329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47827988447293596073255105 35870991335470197054941329)
    ·
      refine ⟨26903243501602647791205997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35870991335470197054941329 26903243501602647791205997)
      ·
        refine ⟨10088716313100992921702249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26903243501602647791205997 10088716313100992921702249)
        ·
          refine ⟨7566537234825744691276687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10088716313100992921702249 7566537234825744691276687)
          ·
            refine ⟨11349805852238617036915031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7566537234825744691276687 11349805852238617036915031)
            ·
              refine ⟨17024708778357925555372547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11349805852238617036915031 17024708778357925555372547)
              ·
                refine ⟨25537063167536888333058821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17024708778357925555372547 25537063167536888333058821)
                ·
                  refine ⟨4788199343913166562448529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25537063167536888333058821 4788199343913166562448529)
                  ·
                    refine ⟨3591149507934874921836397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4788199343913166562448529 3591149507934874921836397)
                    ·
                      refine ⟨1346681065475578095688649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3591149507934874921836397 1346681065475578095688649)
                      ·
                        rfl

theorem cell23_2622652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_2622652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622652 prefixEnd_2622652 := by exact prefixLift 2622652
  have htrace : WordTrace (prefixWord ++ tailWord_2622652) baseStart_2622652 baseEnd_2622652 := by
    simpa [prefixWord, tailWord_2622652, baseEnd_2622652] using wordTrace_append hprefix tailTrace_2622652
  have hstable : (prefixWord ++ tailWord_2622652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622652).length < 2 ^ (prefixWord ++ tailWord_2622652).sum := by decide
  have hdescent : baseEnd_2622652 < baseStart_2622652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622682 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3]
def baseStart_2622682 : Nat := 118140960795 + 2622682 * 2 ^ 59
def prefixEnd_2622682 : Nat := 4983230072969 + 3 ^ 40 * 2622682 * 2
def baseEnd_2622682 : Nat := 1346696469895212978313511

theorem tailTrace_2622682 : CollatzResearch.WordTrace tailWord_2622682 prefixEnd_2622682 1346696469895212978313511 := by
  unfold tailWord_2622682
  simp only [CollatzResearch.WordTrace]
  refine ⟨23914267771119626817525575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63771380722985671513401533 23914267771119626817525575)
  ·
    refine ⟨35871401656679440226288363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23914267771119626817525575 35871401656679440226288363)
    ·
      refine ⟨53807102485019160339432545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35871401656679440226288363 53807102485019160339432545)
      ·
        refine ⟨40355326863764370254574409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53807102485019160339432545 40355326863764370254574409)
        ·
          refine ⟨30266495147823277690930807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40355326863764370254574409 30266495147823277690930807)
          ·
            refine ⟨45399742721734916536396211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30266495147823277690930807 45399742721734916536396211)
            ·
              refine ⟨68099614082602374804594317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45399742721734916536396211 68099614082602374804594317)
              ·
                refine ⟨25537355280975890551722869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68099614082602374804594317 25537355280975890551722869)
                ·
                  refine ⟨2394127057591489739224019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25537355280975890551722869 2394127057591489739224019)
                  ·
                    refine ⟨3591190586387234608836029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2394127057591489739224019 3591190586387234608836029)
                    ·
                      refine ⟨1346696469895212978313511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3591190586387234608836029 1346696469895212978313511)
                      ·
                        rfl

theorem cell23_2622682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_2622682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622682 prefixEnd_2622682 := by exact prefixLift 2622682
  have htrace : WordTrace (prefixWord ++ tailWord_2622682) baseStart_2622682 baseEnd_2622682 := by
    simpa [prefixWord, tailWord_2622682, baseEnd_2622682] using wordTrace_append hprefix tailTrace_2622682
  have hstable : (prefixWord ++ tailWord_2622682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622682).length < 2 ^ (prefixWord ++ tailWord_2622682).sum := by decide
  have hdescent : baseEnd_2622682 < baseStart_2622682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622692 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 1, 5, 2]
def baseStart_2622692 : Nat := 118140960795 + 2622692 * 2 ^ 59
def prefixEnd_2622692 : Nat := 4983230072969 + 3 ^ 40 * 2622692 * 2
def baseEnd_2622692 : Nat := 1346701604701757939188465

theorem tailTrace_2622692 : CollatzResearch.WordTrace tailWord_2622692 prefixEnd_2622692 1346701604701757939188465 := by
  unfold tailWord_2622692
  simp only [CollatzResearch.WordTrace]
  refine ⟨47828717907221139488983165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63771623876294852651977553 47828717907221139488983165)
  ·
    refine ⟨17935769215207927308368687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47828717907221139488983165 17935769215207927308368687)
    ·
      refine ⟨26903653822811890962553031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17935769215207927308368687 26903653822811890962553031)
      ·
        refine ⟨40355480734217836443829547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26903653822811890962553031 40355480734217836443829547)
        ·
          refine ⟨60533221101326754665744321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40355480734217836443829547 60533221101326754665744321)
          ·
            refine ⟨45399915825995065999308241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60533221101326754665744321 45399915825995065999308241)
            ·
              refine ⟨34049936869496299499481181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45399915825995065999308241 34049936869496299499481181)
              ·
                refine ⟨12768726326061112312305443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34049936869496299499481181 12768726326061112312305443)
                ·
                  refine ⟨19153089489091668468458165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12768726326061112312305443 19153089489091668468458165)
                  ·
                    refine ⟨1795602139602343918917953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19153089489091668468458165 1795602139602343918917953)
                    ·
                      refine ⟨1346701604701757939188465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1795602139602343918917953 1346701604701757939188465)
                      ·
                        rfl

theorem cell23_2622692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_2622692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622692 prefixEnd_2622692 := by exact prefixLift 2622692
  have htrace : WordTrace (prefixWord ++ tailWord_2622692) baseStart_2622692 baseEnd_2622692 := by
    simpa [prefixWord, tailWord_2622692, baseEnd_2622692] using wordTrace_append hprefix tailTrace_2622692
  have hstable : (prefixWord ++ tailWord_2622692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622692).length < 2 ^ (prefixWord ++ tailWord_2622692).sum := by decide
  have hdescent : baseEnd_2622692 < baseStart_2622692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622702 : List Nat := [4, 1, 2, 1, 1, 1, 2, 5, 1, 5]
def baseStart_2622702 : Nat := 118140960795 + 2622702 * 2 ^ 59
def prefixEnd_2622702 : Nat := 4983230072969 + 3 ^ 40 * 2622702 * 2
def baseEnd_2622702 : Nat := 448902246502767633354473

theorem tailTrace_2622702 : CollatzResearch.WordTrace tailWord_2622702 prefixEnd_2622702 448902246502767633354473 := by
  unfold tailWord_2622702
  simp only [CollatzResearch.WordTrace]
  refine ⟨11957225068050756335728795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63771867029604033790553573 11957225068050756335728795)
  ·
    refine ⟨17935837602076134503593193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11957225068050756335728795 17935837602076134503593193)
    ·
      refine ⟨13451878201557100877694895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17935837602076134503593193 13451878201557100877694895)
      ·
        refine ⟨20177817302335651316542343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13451878201557100877694895 20177817302335651316542343)
        ·
          refine ⟨30266725953503476974813515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20177817302335651316542343 30266725953503476974813515)
          ·
            refine ⟨45400088930255215462220273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30266725953503476974813515 45400088930255215462220273)
            ·
              refine ⟨34050066697691411596665205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45400088930255215462220273 34050066697691411596665205)
              ·
                refine ⟨3192193752908569837187363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34050066697691411596665205 3192193752908569837187363)
                ·
                  refine ⟨4788290629362854755781045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192193752908569837187363 4788290629362854755781045)
                  ·
                    refine ⟨448902246502767633354473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4788290629362854755781045 448902246502767633354473)
                    ·
                      rfl

theorem cell23_2622702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_2622702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622702 prefixEnd_2622702 := by exact prefixLift 2622702
  have htrace : WordTrace (prefixWord ++ tailWord_2622702) baseStart_2622702 baseEnd_2622702 := by
    simpa [prefixWord, tailWord_2622702, baseEnd_2622702] using wordTrace_append hprefix tailTrace_2622702
  have hstable : (prefixWord ++ tailWord_2622702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622702).length < 2 ^ (prefixWord ++ tailWord_2622702).sum := by decide
  have hdescent : baseEnd_2622702 < baseStart_2622702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622725 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_2622725 : Nat := 118140960795 + 2622725 * 2 ^ 59
def prefixEnd_2622725 : Nat := 4983230072969 + 3 ^ 40 * 2622725 * 2
def baseEnd_2622725 : Nat := 1346718549563356310075813

theorem tailTrace_2622725 : CollatzResearch.WordTrace tailWord_2622725 prefixEnd_2622725 1346718549563356310075813 := by
  unfold tailWord_2622725
  simp only [CollatzResearch.WordTrace]
  refine ⟨95658639423322725613917629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63772426282215150409278419 95658639423322725613917629)
  ·
    refine ⟨35871989783746022105219111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95658639423322725613917629 35871989783746022105219111)
    ·
      refine ⟨53807984675619033157828667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35871989783746022105219111 53807984675619033157828667)
      ·
        refine ⟨80711977013428549736743001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53807984675619033157828667 80711977013428549736743001)
        ·
          refine ⟨60533982760071412302557251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80711977013428549736743001 60533982760071412302557251)
          ·
            refine ⟨90800974140107118453835877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60533982760071412302557251 90800974140107118453835877)
            ·
              refine ⟨17025182651270084710094227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90800974140107118453835877 17025182651270084710094227)
              ·
                refine ⟨25537773976905127065141341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17025182651270084710094227 25537773976905127065141341)
                ·
                  refine ⟨9576665241339422649428003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25537773976905127065141341 9576665241339422649428003)
                  ·
                    refine ⟨14364997862009133974142005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9576665241339422649428003 14364997862009133974142005)
                    ·
                      refine ⟨1346718549563356310075813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14364997862009133974142005 1346718549563356310075813)
                      ·
                        rfl

theorem cell23_2622725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_2622725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622725 prefixEnd_2622725 := by exact prefixLift 2622725
  have htrace : WordTrace (prefixWord ++ tailWord_2622725) baseStart_2622725 baseEnd_2622725 := by
    simpa [prefixWord, tailWord_2622725, baseEnd_2622725] using wordTrace_append hprefix tailTrace_2622725
  have hstable : (prefixWord ++ tailWord_2622725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622725).length < 2 ^ (prefixWord ++ tailWord_2622725).sum := by decide
  have hdescent : baseEnd_2622725 < baseStart_2622725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622732 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 1, 6]
def baseStart_2622732 : Nat := 118140960795 + 2622732 * 2 ^ 59
def prefixEnd_2622732 : Nat := 4983230072969 + 3 ^ 40 * 2622732 * 2
def baseEnd_2622732 : Nat := 448907381309312594229427

theorem tailTrace_2622732 : CollatzResearch.WordTrace tailWord_2622732 prefixEnd_2622732 448907381309312594229427 := by
  unfold tailWord_2622732
  simp only [CollatzResearch.WordTrace]
  refine ⟨47829447367148682904711225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63772596489531577206281633 47829447367148682904711225)
  ·
    refine ⟨35872085525361512178533419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47829447367148682904711225 35872085525361512178533419)
    ·
      refine ⟨53808128288042268267800129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35872085525361512178533419 53808128288042268267800129)
      ·
        refine ⟨40356096216031701200850097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53808128288042268267800129 40356096216031701200850097)
        ·
          refine ⟨30267072162023775900637573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40356096216031701200850097 30267072162023775900637573)
          ·
            refine ⟨5675076030379457981369545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30267072162023775900637573 5675076030379457981369545)
            ·
              refine ⟨4256307022784593486027159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5675076030379457981369545 4256307022784593486027159)
              ·
                refine ⟨6384460534176890229040739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4256307022784593486027159 6384460534176890229040739)
                ·
                  refine ⟨9576690801265335343561109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6384460534176890229040739 9576690801265335343561109)
                  ·
                    refine ⟨448907381309312594229427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9576690801265335343561109 448907381309312594229427)
                    ·
                      rfl

theorem cell23_2622732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_2622732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622732 prefixEnd_2622732 := by exact prefixLift 2622732
  have htrace : WordTrace (prefixWord ++ tailWord_2622732) baseStart_2622732 baseEnd_2622732 := by
    simpa [prefixWord, tailWord_2622732, baseEnd_2622732] using wordTrace_append hprefix tailTrace_2622732
  have hstable : (prefixWord ++ tailWord_2622732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622732).length < 2 ^ (prefixWord ++ tailWord_2622732).sum := by decide
  have hdescent : baseEnd_2622732 < baseStart_2622732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622762 : List Nat := [3, 1, 4, 2, 1, 2, 10]
def baseStart_2622762 : Nat := 118140960795 + 2622762 * 2 ^ 59
def prefixEnd_2622762 : Nat := 4983230072969 + 3 ^ 40 * 2622762 * 2
def baseEnd_2622762 : Nat := 16626389485772502040903

theorem tailTrace_2622762 : CollatzResearch.WordTrace tailWord_2622762 prefixEnd_2622762 16626389485772502040903 := by
  unfold tailWord_2622762
  simp only [CollatzResearch.WordTrace]
  refine ⟨23914997231047170233253635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63773325949459120622009693 23914997231047170233253635)
  ·
    refine ⟨35872495846570755349880453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23914997231047170233253635 35872495846570755349880453)
    ·
      refine ⟨6726092971232016628102585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35872495846570755349880453 6726092971232016628102585)
      ·
        refine ⟨5044569728424012471076939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6726092971232016628102585 5044569728424012471076939)
        ·
          refine ⟨7566854592636018706615409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5044569728424012471076939 7566854592636018706615409)
          ·
            refine ⟨5675140944477014029961557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7566854592636018706615409 5675140944477014029961557)
            ·
              refine ⟨16626389485772502040903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5675140944477014029961557 16626389485772502040903)
              ·
                rfl

theorem cell23_2622762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 10].length) (baseStart_2622762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622762 prefixEnd_2622762 := by exact prefixLift 2622762
  have htrace : WordTrace (prefixWord ++ tailWord_2622762) baseStart_2622762 baseEnd_2622762 := by
    simpa [prefixWord, tailWord_2622762, baseEnd_2622762] using wordTrace_append hprefix tailTrace_2622762
  have hstable : (prefixWord ++ tailWord_2622762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622762).length < 2 ^ (prefixWord ++ tailWord_2622762).sum := by decide
  have hdescent : baseEnd_2622762 < baseStart_2622762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622773 : List Nat := [1, 3, 3, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_2622773 : Nat := 118140960795 + 2622773 * 2 ^ 59
def prefixEnd_2622773 : Nat := 4983230072969 + 3 ^ 40 * 2622773 * 2
def baseEnd_2622773 : Nat := 1346743196634772122275593

theorem tailTrace_2622773 : CollatzResearch.WordTrace tailWord_2622773 prefixEnd_2622773 1346743196634772122275593 := by
  unfold tailWord_2622773
  simp only [CollatzResearch.WordTrace]
  refine ⟨95660390127148829811664973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63773593418099219874443315 95660390127148829811664973)
  ·
    refine ⟨35872646297680811179374365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95660390127148829811664973 35872646297680811179374365)
    ·
      refine ⟨13452242361630304192265387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35872646297680811179374365 13452242361630304192265387)
      ·
        refine ⟨20178363542445456288398081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13452242361630304192265387 20178363542445456288398081)
        ·
          refine ⟨15133772656834092216298561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20178363542445456288398081 15133772656834092216298561)
          ·
            refine ⟨11350329492625569162223921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15133772656834092216298561 11350329492625569162223921)
            ·
              refine ⟨8512747119469176871667941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11350329492625569162223921 8512747119469176871667941)
              ·
                refine ⟨1596140084900470663437739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8512747119469176871667941 1596140084900470663437739)
                ·
                  refine ⟨2394210127350705995156609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596140084900470663437739 2394210127350705995156609)
                  ·
                    refine ⟨1795657595513029496367457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2394210127350705995156609 1795657595513029496367457)
                    ·
                      refine ⟨1346743196634772122275593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1795657595513029496367457 1346743196634772122275593)
                      ·
                        rfl

theorem cell23_2622773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_2622773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622773 prefixEnd_2622773 := by exact prefixLift 2622773
  have htrace : WordTrace (prefixWord ++ tailWord_2622773) baseStart_2622773 baseEnd_2622773 := by
    simpa [prefixWord, tailWord_2622773, baseEnd_2622773] using wordTrace_append hprefix tailTrace_2622773
  have hstable : (prefixWord ++ tailWord_2622773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622773).length < 2 ^ (prefixWord ++ tailWord_2622773).sum := by decide
  have hdescent : baseEnd_2622773 < baseStart_2622773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622789 : List Nat := [1, 3, 1, 1, 1, 2, 1, 7, 2, 1, 3]
def baseStart_2622789 : Nat := 118140960795 + 2622789 * 2 ^ 59
def prefixEnd_2622789 : Nat := 4983230072969 + 3 ^ 40 * 2622789 * 2
def baseEnd_2622789 : Nat := 1346751412325244059675519

theorem tailTrace_2622789 : CollatzResearch.WordTrace tailWord_2622789 prefixEnd_2622789 1346751412325244059675519 := by
  unfold tailWord_2622789
  simp only [CollatzResearch.WordTrace]
  refine ⟨95660973695090864544247421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63773982463393909696164947 95660973695090864544247421)
  ·
    refine ⟨35872865135659074204092783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95660973695090864544247421 35872865135659074204092783)
    ·
      refine ⟨53809297703488611306139175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35872865135659074204092783 53809297703488611306139175)
      ·
        refine ⟨80713946555232916959208763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53809297703488611306139175 80713946555232916959208763)
        ·
          refine ⟨121070919832849375438813145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80713946555232916959208763 121070919832849375438813145)
          ·
            refine ⟨90803189874637031579109859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121070919832849375438813145 90803189874637031579109859)
            ·
              refine ⟨136204784811955547368664789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90803189874637031579109859 136204784811955547368664789)
              ·
                refine ⟨3192299644030208141453081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 136204784811955547368664789 3192299644030208141453081)
                ·
                  refine ⟨2394224733022656106089811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3192299644030208141453081 2394224733022656106089811)
                  ·
                    refine ⟨3591337099533984159134717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2394224733022656106089811 3591337099533984159134717)
                    ·
                      refine ⟨1346751412325244059675519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3591337099533984159134717 1346751412325244059675519)
                      ·
                        rfl

theorem cell23_2622789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_2622789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622789 prefixEnd_2622789 := by exact prefixLift 2622789
  have htrace : WordTrace (prefixWord ++ tailWord_2622789) baseStart_2622789 baseEnd_2622789 := by
    simpa [prefixWord, tailWord_2622789, baseEnd_2622789] using wordTrace_append hprefix tailTrace_2622789
  have hstable : (prefixWord ++ tailWord_2622789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622789).length < 2 ^ (prefixWord ++ tailWord_2622789).sum := by decide
  have hdescent : baseEnd_2622789 < baseStart_2622789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622790 : List Nat := [6, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2622790 : Nat := 118140960795 + 2622790 * 2 ^ 59
def prefixEnd_2622790 : Nat := 4983230072969 + 3 ^ 40 * 2622790 * 2
def baseEnd_2622790 : Nat := 1346751925805898555763015

theorem tailTrace_2622790 : CollatzResearch.WordTrace tailWord_2622790 prefixEnd_2622790 1346751925805898555763015 := by
  unfold tailWord_2622790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2989406567752726303594807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63774006778724827810022549 2989406567752726303594807)
  ·
    refine ⟨4484109851629089455392211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2989406567752726303594807 4484109851629089455392211)
    ·
      refine ⟨6726164777443634183088317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4484109851629089455392211 6726164777443634183088317)
      ·
        refine ⟨2522311791541362818658119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6726164777443634183088317 2522311791541362818658119)
        ·
          refine ⟨3783467687312044227987179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2522311791541362818658119 3783467687312044227987179)
          ·
            refine ⟨5675201530968066341980769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783467687312044227987179 5675201530968066341980769)
            ·
              refine ⟨4256401148226049756485577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5675201530968066341980769 4256401148226049756485577)
              ·
                refine ⟨3192300861169537317364183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4256401148226049756485577 3192300861169537317364183)
                ·
                  refine ⟨4788451291754305976046275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192300861169537317364183 4788451291754305976046275)
                  ·
                    refine ⟨7182676937631458964069413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4788451291754305976046275 7182676937631458964069413)
                    ·
                      refine ⟨1346751925805898555763015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7182676937631458964069413 1346751925805898555763015)
                      ·
                        rfl

theorem cell23_2622790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2622790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622790 prefixEnd_2622790 := by exact prefixLift 2622790
  have htrace : WordTrace (prefixWord ++ tailWord_2622790) baseStart_2622790 baseEnd_2622790 := by
    simpa [prefixWord, tailWord_2622790, baseEnd_2622790] using wordTrace_append hprefix tailTrace_2622790
  have hstable : (prefixWord ++ tailWord_2622790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622790).length < 2 ^ (prefixWord ++ tailWord_2622790).sum := by decide
  have hdescent : baseEnd_2622790 < baseStart_2622790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622795 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 4]
def baseStart_2622795 : Nat := 118140960795 + 2622795 * 2 ^ 59
def prefixEnd_2622795 : Nat := 4983230072969 + 3 ^ 40 * 2622795 * 2
def baseEnd_2622795 : Nat := 1346754493209171036200491

theorem tailTrace_2622795 : CollatzResearch.WordTrace tailWord_2622795 prefixEnd_2622795 1346754493209171036200491 := by
  unfold tailWord_2622795
  simp only [CollatzResearch.WordTrace]
  refine ⟨95661192533069127568965839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63774128355379418379310559 95661192533069127568965839)
  ·
    refine ⟨143491788799603691353448759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95661192533069127568965839 143491788799603691353448759)
    ·
      refine ⟨215237683199405537030173139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143491788799603691353448759 215237683199405537030173139)
      ·
        refine ⟨322856524799108305545259709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215237683199405537030173139 322856524799108305545259709)
        ·
          refine ⟨121071196799665614579472391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322856524799108305545259709 121071196799665614579472391)
          ·
            refine ⟨181606795199498421869208587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121071196799665614579472391 181606795199498421869208587)
            ·
              refine ⟨272410192799247632803812881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181606795199498421869208587 272410192799247632803812881)
              ·
                refine ⟨204307644599435724602859661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272410192799247632803812881 204307644599435724602859661)
                ·
                  refine ⟨76615366724788396726072373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204307644599435724602859661 76615366724788396726072373)
                  ·
                    refine ⟨7182690630448912193069285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76615366724788396726072373 7182690630448912193069285)
                    ·
                      refine ⟨1346754493209171036200491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7182690630448912193069285 1346754493209171036200491)
                      ·
                        rfl

theorem cell23_2622795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 4].length) (baseStart_2622795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622795 prefixEnd_2622795 := by exact prefixLift 2622795
  have htrace : WordTrace (prefixWord ++ tailWord_2622795) baseStart_2622795 baseEnd_2622795 := by
    simpa [prefixWord, tailWord_2622795, baseEnd_2622795] using wordTrace_append hprefix tailTrace_2622795
  have hstable : (prefixWord ++ tailWord_2622795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622795).length < 2 ^ (prefixWord ++ tailWord_2622795).sum := by decide
  have hdescent : baseEnd_2622795 < baseStart_2622795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622813 : List Nat := [1, 4, 5, 1, 2, 1, 9]
def baseStart_2622813 : Nat := 118140960795 + 2622813 * 2 ^ 59
def prefixEnd_2622813 : Nat := 4983230072969 + 3 ^ 40 * 2622813 * 2
def baseEnd_2622813 : Nat := 16626712788406814392289

theorem tailTrace_2622813 : CollatzResearch.WordTrace tailWord_2622813 prefixEnd_2622813 16626712788406814392289 := by
  unfold tailWord_2622813
  simp only [CollatzResearch.WordTrace]
  refine ⟨95661849047003916643121093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63774566031335944428747395 95661849047003916643121093)
  ·
    refine ⟨17936596696313234370585205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95661849047003916643121093 17936596696313234370585205)
    ·
      refine ⟨1681555940279365722242363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17936596696313234370585205 1681555940279365722242363)
      ·
        refine ⟨2522333910419048583363545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1681555940279365722242363 2522333910419048583363545)
        ·
          refine ⟨1891750432814286437522659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2522333910419048583363545 1891750432814286437522659)
          ·
            refine ⟨2837625649221429656283989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891750432814286437522659 2837625649221429656283989)
            ·
              refine ⟨16626712788406814392289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2837625649221429656283989 16626712788406814392289)
              ·
                rfl

theorem cell23_2622813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 9].length) (baseStart_2622813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622813 prefixEnd_2622813 := by exact prefixLift 2622813
  have htrace : WordTrace (prefixWord ++ tailWord_2622813) baseStart_2622813 baseEnd_2622813 := by
    simpa [prefixWord, tailWord_2622813, baseEnd_2622813] using wordTrace_append hprefix tailTrace_2622813
  have hstable : (prefixWord ++ tailWord_2622813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622813).length < 2 ^ (prefixWord ++ tailWord_2622813).sum := by decide
  have hdescent : baseEnd_2622813 < baseStart_2622813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622816 : List Nat := [2, 1, 1, 3, 4, 1, 2, 3, 1, 3, 2]
def baseStart_2622816 : Nat := 118140960795 + 2622816 * 2 ^ 59
def prefixEnd_2622816 : Nat := 4983230072969 + 3 ^ 40 * 2622816 * 2
def baseEnd_2622816 : Nat := 1346765276302915454037895

theorem tailTrace_2622816 : CollatzResearch.WordTrace tailWord_2622816 prefixEnd_2622816 1346765276302915454037895 := by
  unfold tailWord_2622816
  simp only [CollatzResearch.WordTrace]
  refine ⟨47830979232996524077740151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63774638977328698770320201 47830979232996524077740151)
  ·
    refine ⟨71746468849494786116610227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47830979232996524077740151 71746468849494786116610227)
    ·
      refine ⟨107619703274242179174915341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71746468849494786116610227 107619703274242179174915341)
      ·
        refine ⟨40357388727840817190593253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107619703274242179174915341 40357388727840817190593253)
        ·
          refine ⟨7567010386470153223236235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40357388727840817190593253 7567010386470153223236235)
          ·
            refine ⟨11350515579705229834854353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7567010386470153223236235 11350515579705229834854353)
            ·
              refine ⟨8512886684778922376140765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11350515579705229834854353 8512886684778922376140765)
              ·
                refine ⟨3192332506792095891052787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8512886684778922376140765 3192332506792095891052787)
                ·
                  refine ⟨4788498760188143836579181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192332506792095891052787 4788498760188143836579181)
                  ·
                    refine ⟨1795687035070553938717193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4788498760188143836579181 1795687035070553938717193)
                    ·
                      refine ⟨1346765276302915454037895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1795687035070553938717193 1346765276302915454037895)
                      ·
                        rfl

theorem cell23_2622816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_2622816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622816 prefixEnd_2622816 := by exact prefixLift 2622816
  have htrace : WordTrace (prefixWord ++ tailWord_2622816) baseStart_2622816 baseEnd_2622816 := by
    simpa [prefixWord, tailWord_2622816, baseEnd_2622816] using wordTrace_append hprefix tailTrace_2622816
  have hstable : (prefixWord ++ tailWord_2622816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622816).length < 2 ^ (prefixWord ++ tailWord_2622816).sum := by decide
  have hdescent : baseEnd_2622816 < baseStart_2622816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622825 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 6]
def baseStart_2622825 : Nat := 118140960795 + 2622825 * 2 ^ 59
def prefixEnd_2622825 : Nat := 4983230072969 + 3 ^ 40 * 2622825 * 2
def baseEnd_2622825 : Nat := 1346769897628805918825353

theorem tailTrace_2622825 : CollatzResearch.WordTrace tailWord_2622825 prefixEnd_2622825 1346769897628805918825353 := by
  unfold tailWord_2622825
  simp only [CollatzResearch.WordTrace]
  refine ⟨95662286722960442692557929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63774857815306961795038619 95662286722960442692557929)
  ·
    refine ⟨71746715042220332019418447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95662286722960442692557929 71746715042220332019418447)
    ·
      refine ⟨107620072563330498029127671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71746715042220332019418447 107620072563330498029127671)
      ·
        refine ⟨161430108844995747043691507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107620072563330498029127671 161430108844995747043691507)
        ·
          refine ⟨242145163267493620565537261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161430108844995747043691507 242145163267493620565537261)
          ·
            refine ⟨90804436225310107712076473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242145163267493620565537261 90804436225310107712076473)
            ·
              refine ⟨68103327168982580784057355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90804436225310107712076473 68103327168982580784057355)
              ·
                refine ⟨102154990753473871176086033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68103327168982580784057355 102154990753473871176086033)
                ·
                  refine ⟨76616243065105403382064525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102154990753473871176086033 76616243065105403382064525)
                  ·
                    refine ⟨28731091149414526268274197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76616243065105403382064525 28731091149414526268274197)
                    ·
                      refine ⟨1346769897628805918825353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28731091149414526268274197 1346769897628805918825353)
                      ·
                        rfl

theorem cell23_2622825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_2622825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622825 prefixEnd_2622825 := by exact prefixLift 2622825
  have htrace : WordTrace (prefixWord ++ tailWord_2622825) baseStart_2622825 baseEnd_2622825 := by
    simpa [prefixWord, tailWord_2622825, baseEnd_2622825] using wordTrace_append hprefix tailTrace_2622825
  have hstable : (prefixWord ++ tailWord_2622825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622825).length < 2 ^ (prefixWord ++ tailWord_2622825).sum := by decide
  have hdescent : baseEnd_2622825 < baseStart_2622825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622832 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 3]
def baseStart_2622832 : Nat := 118140960795 + 2622832 * 2 ^ 59
def prefixEnd_2622832 : Nat := 4983230072969 + 3 ^ 40 * 2622832 * 2
def baseEnd_2622832 : Nat := 1346773491993387391437821

theorem tailTrace_2622832 : CollatzResearch.WordTrace tailWord_2622832 prefixEnd_2622832 1346773491993387391437821 := by
  unfold tailWord_2622832
  simp only [CollatzResearch.WordTrace]
  refine ⟨47831271016967541444031375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63775028022623388592041833 47831271016967541444031375)
  ·
    refine ⟨71746906525451312166047063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47831271016967541444031375 71746906525451312166047063)
    ·
      refine ⟨107620359788176968249070595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71746906525451312166047063 107620359788176968249070595)
      ·
        refine ⟨161430539682265452373605893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107620359788176968249070595 161430539682265452373605893)
        ·
          refine ⟨30268226190424772320051105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161430539682265452373605893 30268226190424772320051105)
          ·
            refine ⟨22701169642818579240038329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30268226190424772320051105 22701169642818579240038329)
            ·
              refine ⟨17025877232113934430028747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22701169642818579240038329 17025877232113934430028747)
              ·
                refine ⟨25538815848170901645043121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17025877232113934430028747 25538815848170901645043121)
                ·
                  refine ⟨19154111886128176233782341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25538815848170901645043121 19154111886128176233782341)
                  ·
                    refine ⟨3591395978649033043834189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19154111886128176233782341 3591395978649033043834189)
                    ·
                      refine ⟨1346773491993387391437821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3591395978649033043834189 1346773491993387391437821)
                      ·
                        rfl

theorem cell23_2622832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 3].length) (baseStart_2622832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622832 prefixEnd_2622832 := by exact prefixLift 2622832
  have htrace : WordTrace (prefixWord ++ tailWord_2622832) baseStart_2622832 baseEnd_2622832 := by
    simpa [prefixWord, tailWord_2622832, baseEnd_2622832] using wordTrace_append hprefix tailTrace_2622832
  have hstable : (prefixWord ++ tailWord_2622832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622832).length < 2 ^ (prefixWord ++ tailWord_2622832).sum := by decide
  have hdescent : baseEnd_2622832 < baseStart_2622832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622850 : List Nat := [3, 4, 2, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_2622850 : Nat := 118140960795 + 2622850 * 2 ^ 59
def prefixEnd_2622850 : Nat := 4983230072969 + 3 ^ 40 * 2622850 * 2
def baseEnd_2622850 : Nat := 1346782734645168321012739

theorem tailTrace_2622850 : CollatzResearch.WordTrace tailWord_2622850 prefixEnd_2622850 1346782734645168321012739 := by
  unfold tailWord_2622850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23915799636967467990554501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63775465698579914641478669 23915799636967467990554501)
  ·
    refine ⟨4484212431931400248228969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23915799636967467990554501 4484212431931400248228969)
    ·
      refine ⟨3363159323948550186171727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4484212431931400248228969 3363159323948550186171727)
      ·
        refine ⟨5044738985922825279257591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3363159323948550186171727 5044738985922825279257591)
        ·
          refine ⟨7567108478884237918886387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5044738985922825279257591 7567108478884237918886387)
          ·
            refine ⟨11350662718326356878329581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7567108478884237918886387 11350662718326356878329581)
            ·
              refine ⟨4256498519372383829373593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11350662718326356878329581 4256498519372383829373593)
              ·
                refine ⟨3192373889529287872030195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4256498519372383829373593 3192373889529287872030195)
                ·
                  refine ⟨4788560834293931808045293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192373889529287872030195 4788560834293931808045293)
                  ·
                    refine ⟨1795710312860224428016985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4788560834293931808045293 1795710312860224428016985)
                    ·
                      refine ⟨1346782734645168321012739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1795710312860224428016985 1346782734645168321012739)
                      ·
                        rfl

theorem cell23_2622850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_2622850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622850 prefixEnd_2622850 := by exact prefixLift 2622850
  have htrace : WordTrace (prefixWord ++ tailWord_2622850) baseStart_2622850 baseEnd_2622850 := by
    simpa [prefixWord, tailWord_2622850, baseEnd_2622850] using wordTrace_append hprefix tailTrace_2622850
  have hstable : (prefixWord ++ tailWord_2622850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622850).length < 2 ^ (prefixWord ++ tailWord_2622850).sum := by decide
  have hdescent : baseEnd_2622850 < baseStart_2622850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622892 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_2622892 : Nat := 118140960795 + 2622892 * 2 ^ 59
def prefixEnd_2622892 : Nat := 4983230072969 + 3 ^ 40 * 2622892 * 2
def baseEnd_2622892 : Nat := 1346804300832657156687545

theorem tailTrace_2622892 : CollatzResearch.WordTrace tailWord_2622892 prefixEnd_2622892 1346804300832657156687545 := by
  unfold tailWord_2622892
  simp only [CollatzResearch.WordTrace]
  refine ⟨47832365206858856567623465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63776486942478475423497953 47832365206858856567623465)
  ·
    refine ⟨35874273905144142425717599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47832365206858856567623465 35874273905144142425717599)
    ·
      refine ⟨53811410857716213638576399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35874273905144142425717599 53811410857716213638576399)
      ·
        refine ⟨80717116286574320457864599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53811410857716213638576399 80717116286574320457864599)
        ·
          refine ⟨121075674429861480686796899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80717116286574320457864599 121075674429861480686796899)
          ·
            refine ⟨181613511644792221030195349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121075674429861480686796899 181613511644792221030195349)
            ·
              refine ⟨8513133358349635360790407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 181613511644792221030195349 8513133358349635360790407)
              ·
                refine ⟨12769700037524453041185611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8513133358349635360790407 12769700037524453041185611)
                ·
                  refine ⟨19154550056286679561778417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12769700037524453041185611 19154550056286679561778417)
                  ·
                    refine ⟨14365912542215009671333813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19154550056286679561778417 14365912542215009671333813)
                    ·
                      refine ⟨1346804300832657156687545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14365912542215009671333813 1346804300832657156687545)
                      ·
                        rfl

theorem cell23_2622892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_2622892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622892 prefixEnd_2622892 := by exact prefixLift 2622892
  have htrace : WordTrace (prefixWord ++ tailWord_2622892) baseStart_2622892 baseEnd_2622892 := by
    simpa [prefixWord, tailWord_2622892, baseEnd_2622892] using wordTrace_append hprefix tailTrace_2622892
  have hstable : (prefixWord ++ tailWord_2622892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622892).length < 2 ^ (prefixWord ++ tailWord_2622892).sum := by decide
  have hdescent : baseEnd_2622892 < baseStart_2622892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622916 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_2622916 : Nat := 118140960795 + 2622916 * 2 ^ 59
def prefixEnd_2622916 : Nat := 4983230072969 + 3 ^ 40 * 2622916 * 2
def baseEnd_2622916 : Nat := 448938874789455020929145

theorem tailTrace_2622916 : CollatzResearch.WordTrace tailWord_2622916 prefixEnd_2622916 448938874789455020929145 := by
  unfold tailWord_2622916
  simp only [CollatzResearch.WordTrace]
  refine ⟨47832802882815382617060301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63777070510420510156080401 47832802882815382617060301)
  ·
    refine ⟨17937301081055768481397613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47832802882815382617060301 17937301081055768481397613)
    ·
      refine ⟨6726487905395913180524105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17937301081055768481397613 6726487905395913180524105)
      ·
        refine ⟨5044865929046934885393079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6726487905395913180524105 5044865929046934885393079)
        ·
          refine ⟨7567298893570402328089619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5044865929046934885393079 7567298893570402328089619)
          ·
            refine ⟨11350948340355603492134429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7567298893570402328089619 11350948340355603492134429)
            ·
              refine ⟨4256605627633351309550411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11350948340355603492134429 4256605627633351309550411)
              ·
                refine ⟨6384908441450026964325617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4256605627633351309550411 6384908441450026964325617)
                ·
                  refine ⟨4788681331087520223244213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6384908441450026964325617 4788681331087520223244213)
                  ·
                    refine ⟨448938874789455020929145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4788681331087520223244213 448938874789455020929145)
                    ·
                      rfl

theorem cell23_2622916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_2622916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622916 prefixEnd_2622916 := by exact prefixLift 2622916
  have htrace : WordTrace (prefixWord ++ tailWord_2622916) baseStart_2622916 baseEnd_2622916 := by
    simpa [prefixWord, tailWord_2622916, baseEnd_2622916] using wordTrace_append hprefix tailTrace_2622916
  have hstable : (prefixWord ++ tailWord_2622916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622916).length < 2 ^ (prefixWord ++ tailWord_2622916).sum := by decide
  have hdescent : baseEnd_2622916 < baseStart_2622916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622919 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 1, 6, 2]
def baseStart_2622919 : Nat := 118140960795 + 2622919 * 2 ^ 59
def prefixEnd_2622919 : Nat := 4983230072969 + 3 ^ 40 * 2622919 * 2
def baseEnd_2622919 : Nat := 1346818164810328551049921

theorem tailTrace_2622919 : CollatzResearch.WordTrace tailWord_2622919 prefixEnd_2622919 1346818164810328551049921 := by
  unfold tailWord_2622919
  simp only [CollatzResearch.WordTrace]
  refine ⟨95665715184619896746479811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63777143456413264497653207 95665715184619896746479811)
  ·
    refine ⟨143498572776929845119719717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95665715184619896746479811 143498572776929845119719717)
    ·
      refine ⟨26905982395674345959947447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143498572776929845119719717 26905982395674345959947447)
      ·
        refine ⟨40358973593511518939921171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26905982395674345959947447 40358973593511518939921171)
        ·
          refine ⟨60538460390267278409881757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40358973593511518939921171 60538460390267278409881757)
          ·
            refine ⟨22701922646350229403705659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60538460390267278409881757 22701922646350229403705659)
            ·
              refine ⟨34052883969525344105558489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22701922646350229403705659 34052883969525344105558489)
              ·
                refine ⟨25539662977144008079168867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34052883969525344105558489 25539662977144008079168867)
                ·
                  refine ⟨38309494465716012118753301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25539662977144008079168867 38309494465716012118753301)
                  ·
                    refine ⟨1795757553080438068066561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38309494465716012118753301 1795757553080438068066561)
                    ·
                      refine ⟨1346818164810328551049921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1795757553080438068066561 1346818164810328551049921)
                      ·
                        rfl

theorem cell23_2622919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_2622919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2622919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2622919 prefixEnd_2622919 := by exact prefixLift 2622919
  have htrace : WordTrace (prefixWord ++ tailWord_2622919) baseStart_2622919 baseEnd_2622919 := by
    simpa [prefixWord, tailWord_2622919, baseEnd_2622919] using wordTrace_append hprefix tailTrace_2622919
  have hstable : (prefixWord ++ tailWord_2622919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622919).length < 2 ^ (prefixWord ++ tailWord_2622919).sum := by decide
  have hdescent : baseEnd_2622919 < baseStart_2622919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623036 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 1, 6]
def baseStart_2623036 : Nat := 118140960795 + 2623036 * 2 ^ 59
def prefixEnd_2623036 : Nat := 4983230072969 + 3 ^ 40 * 2623036 * 2
def baseEnd_2623036 : Nat := 448959414015634864428961

theorem tailTrace_2623036 : CollatzResearch.WordTrace tailWord_2623036 prefixEnd_2623036 448959414015634864428961 := by
  unfold tailWord_2623036
  simp only [CollatzResearch.WordTrace]
  refine ⟨47834991262598012864244481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63779988350130683818992641 47834991262598012864244481)
  ·
    refine ⟨35876243446948509648183361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47834991262598012864244481 35876243446948509648183361)
    ·
      refine ⟨26907182585211382236137521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35876243446948509648183361 26907182585211382236137521)
      ·
        refine ⟨20180386938908536677103141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26907182585211382236137521 20180386938908536677103141)
        ·
          refine ⟨3783822551045350626956839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20180386938908536677103141 3783822551045350626956839)
          ·
            refine ⟨5675733826568025940435259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783822551045350626956839 5675733826568025940435259)
            ·
              refine ⟨8513600739852038910652889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5675733826568025940435259 8513600739852038910652889)
              ·
                refine ⟨6385200554889029182989667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8513600739852038910652889 6385200554889029182989667)
                ·
                  refine ⟨9577800832333543774484501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6385200554889029182989667 9577800832333543774484501)
                  ·
                    refine ⟨448959414015634864428961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9577800832333543774484501 448959414015634864428961)
                    ·
                      rfl

theorem cell23_2623036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_2623036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623036 prefixEnd_2623036 := by exact prefixLift 2623036
  have htrace : WordTrace (prefixWord ++ tailWord_2623036) baseStart_2623036 baseEnd_2623036 := by
    simpa [prefixWord, tailWord_2623036, baseEnd_2623036] using wordTrace_append hprefix tailTrace_2623036
  have hstable : (prefixWord ++ tailWord_2623036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623036).length < 2 ^ (prefixWord ++ tailWord_2623036).sum := by decide
  have hdescent : baseEnd_2623036 < baseStart_2623036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623039 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 4]
def baseStart_2623039 : Nat := 118140960795 + 2623039 * 2 ^ 59
def prefixEnd_2623039 : Nat := 4983230072969 + 3 ^ 40 * 2623039 * 2
def baseEnd_2623039 : Nat := 1346879782488868081549369

theorem tailTrace_2623039 : CollatzResearch.WordTrace tailWord_2623039 prefixEnd_2623039 1346879782488868081549369 := by
  unfold tailWord_2623039
  simp only [CollatzResearch.WordTrace]
  refine ⟨95670091944185157240848171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63780061296123438160565447 95670091944185157240848171)
  ·
    refine ⟨143505137916277735861272257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95670091944185157240848171 143505137916277735861272257)
    ·
      refine ⟨107628853437208301895954193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143505137916277735861272257 107628853437208301895954193)
      ·
        refine ⟨80721640077906226421965645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107628853437208301895954193 80721640077906226421965645)
        ·
          refine ⟨30270615029214834908237117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80721640077906226421965645 30270615029214834908237117)
          ·
            refine ⟨11351480635955563090588919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30270615029214834908237117 11351480635955563090588919)
            ·
              refine ⟨17027220953933344635883379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11351480635955563090588919 17027220953933344635883379)
              ·
                refine ⟨25540831430900016953825069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17027220953933344635883379 25540831430900016953825069)
                ·
                  refine ⟨9577811786587506357684401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25540831430900016953825069 9577811786587506357684401)
                  ·
                    refine ⟨7183358839940629768263301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9577811786587506357684401 7183358839940629768263301)
                    ·
                      refine ⟨1346879782488868081549369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7183358839940629768263301 1346879782488868081549369)
                      ·
                        rfl

theorem cell23_2623039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_2623039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623039 prefixEnd_2623039 := by exact prefixLift 2623039
  have htrace : WordTrace (prefixWord ++ tailWord_2623039) baseStart_2623039 baseEnd_2623039 := by
    simpa [prefixWord, tailWord_2623039, baseEnd_2623039] using wordTrace_append hprefix tailTrace_2623039
  have hstable : (prefixWord ++ tailWord_2623039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623039).length < 2 ^ (prefixWord ++ tailWord_2623039).sum := by decide
  have hdescent : baseEnd_2623039 < baseStart_2623039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623076 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_2623076 : Nat := 118140960795 + 2623076 * 2 ^ 59
def prefixEnd_2623076 : Nat := 4983230072969 + 3 ^ 40 * 2623076 * 2
def baseEnd_2623076 : Nat := 1346898781273084436786699

theorem tailTrace_2623076 : CollatzResearch.WordTrace tailWord_2623076 prefixEnd_2623076 1346898781273084436786699 := by
  unfold tailWord_2623076
  simp only [CollatzResearch.WordTrace]
  refine ⟨47835720722525556279972541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63780960963367408373296721 47835720722525556279972541)
  ·
    refine ⟨17938395270947083604989703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47835720722525556279972541 17938395270947083604989703)
    ·
      refine ⟨26907592906420625407484555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17938395270947083604989703 26907592906420625407484555)
      ·
        refine ⟨40361389359630938111226833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26907592906420625407484555 40361389359630938111226833)
        ·
          refine ⟨30271042019723203583420125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40361389359630938111226833 30271042019723203583420125)
          ·
            refine ⟨11351640757396201343782547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30271042019723203583420125 11351640757396201343782547)
            ·
              refine ⟨17027461136094302015673821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11351640757396201343782547 17027461136094302015673821)
              ·
                refine ⟨6385297926035363255877683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17027461136094302015673821 6385297926035363255877683)
                ·
                  refine ⟨9577946889053044883816525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6385297926035363255877683 9577946889053044883816525)
                  ·
                    refine ⟨3591730083394891831431197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9577946889053044883816525 3591730083394891831431197)
                    ·
                      refine ⟨1346898781273084436786699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3591730083394891831431197 1346898781273084436786699)
                      ·
                        rfl

theorem cell23_2623076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_2623076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623076 prefixEnd_2623076 := by exact prefixLift 2623076
  have htrace : WordTrace (prefixWord ++ tailWord_2623076) baseStart_2623076 baseEnd_2623076 := by
    simpa [prefixWord, tailWord_2623076, baseEnd_2623076] using wordTrace_append hprefix tailTrace_2623076
  have hstable : (prefixWord ++ tailWord_2623076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623076).length < 2 ^ (prefixWord ++ tailWord_2623076).sum := by decide
  have hdescent : baseEnd_2623076 < baseStart_2623076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623093 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2623093 : Nat := 118140960795 + 2623093 * 2 ^ 59
def prefixEnd_2623093 : Nat := 4983230072969 + 3 ^ 40 * 2623093 * 2
def baseEnd_2623093 : Nat := 1346907510444210870274121

theorem tailTrace_2623093 : CollatzResearch.WordTrace tailWord_2623093 prefixEnd_2623093 1346907510444210870274121 := by
  unfold tailWord_2623093
  simp only [CollatzResearch.WordTrace]
  refine ⟨95672061485989524463313933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63781374323993016308875955 95672061485989524463313933)
  ·
    refine ⟨35877023057246071673742725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95672061485989524463313933 35877023057246071673742725)
    ·
      refine ⟨6726941823233638438826761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35877023057246071673742725 6726941823233638438826761)
      ·
        refine ⟨5045206367425228829120071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6726941823233638438826761 5045206367425228829120071)
        ·
          refine ⟨7567809551137843243680107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5045206367425228829120071 7567809551137843243680107)
          ·
            refine ⟨11351714326706764865520161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7567809551137843243680107 11351714326706764865520161)
            ·
              refine ⟨8513785745030073649140121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11351714326706764865520161 8513785745030073649140121)
              ·
                refine ⟨6385339308772555236855091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8513785745030073649140121 6385339308772555236855091)
                ·
                  refine ⟨9578008963158832855282637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6385339308772555236855091 9578008963158832855282637)
                  ·
                    refine ⟨3591753361184562320730989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9578008963158832855282637 3591753361184562320730989)
                    ·
                      refine ⟨1346907510444210870274121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3591753361184562320730989 1346907510444210870274121)
                      ·
                        rfl

theorem cell23_2623093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2623093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623093 prefixEnd_2623093 := by exact prefixLift 2623093
  have htrace : WordTrace (prefixWord ++ tailWord_2623093) baseStart_2623093 baseEnd_2623093 := by
    simpa [prefixWord, tailWord_2623093, baseEnd_2623093] using wordTrace_append hprefix tailTrace_2623093
  have hstable : (prefixWord ++ tailWord_2623093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623093).length < 2 ^ (prefixWord ++ tailWord_2623093).sum := by decide
  have hdescent : baseEnd_2623093 < baseStart_2623093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623094 : List Nat := [5, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_2623094 : Nat := 118140960795 + 2623094 * 2 ^ 59
def prefixEnd_2623094 : Nat := 4983230072969 + 3 ^ 40 * 2623094 * 2
def baseEnd_2623094 : Nat := 1346908023924865366361617

theorem tailTrace_2623094 : CollatzResearch.WordTrace tailWord_2623094 prefixEnd_2623094 1346908023924865366361617 := by
  unfold tailWord_2623094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5979506122436618852131271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63781398639323934422733557 5979506122436618852131271)
  ·
    refine ⟨8969259183654928278196907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5979506122436618852131271 8969259183654928278196907)
    ·
      refine ⟨13453888775482392417295361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8969259183654928278196907 13453888775482392417295361)
      ·
        refine ⟨10090416581611794312971521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13453888775482392417295361 10090416581611794312971521)
        ·
          refine ⟨7567812436208845734728641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10090416581611794312971521 7567812436208845734728641)
          ·
            refine ⟨5675859327156634301046481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7567812436208845734728641 5675859327156634301046481)
            ·
              refine ⟨4256894495367475725784861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5675859327156634301046481 4256894495367475725784861)
              ·
                refine ⟨1596335435762803397169323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4256894495367475725784861 1596335435762803397169323)
                ·
                  refine ⟨2394503153644205095753985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596335435762803397169323 2394503153644205095753985)
                  ·
                    refine ⟨1795877365233153821815489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2394503153644205095753985 1795877365233153821815489)
                    ·
                      refine ⟨1346908023924865366361617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1795877365233153821815489 1346908023924865366361617)
                      ·
                        rfl

theorem cell23_2623094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_2623094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623094 prefixEnd_2623094 := by exact prefixLift 2623094
  have htrace : WordTrace (prefixWord ++ tailWord_2623094) baseStart_2623094 baseEnd_2623094 := by
    simpa [prefixWord, tailWord_2623094, baseEnd_2623094] using wordTrace_append hprefix tailTrace_2623094
  have hstable : (prefixWord ++ tailWord_2623094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623094).length < 2 ^ (prefixWord ++ tailWord_2623094).sum := by decide
  have hdescent : baseEnd_2623094 < baseStart_2623094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623109 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 4, 6]
def baseStart_2623109 : Nat := 118140960795 + 2623109 * 2 ^ 59
def prefixEnd_2623109 : Nat := 4983230072969 + 3 ^ 40 * 2623109 * 2
def baseEnd_2623109 : Nat := 448971908711560935891349

theorem tailTrace_2623109 : CollatzResearch.WordTrace tailWord_2623109 prefixEnd_2623109 448971908711560935891349 := by
  unfold tailWord_2623109
  simp only [CollatzResearch.WordTrace]
  refine ⟨95672645053931559195896381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63781763369287706130597587 95672645053931559195896381)
  ·
    refine ⟨35877241895224334698461143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95672645053931559195896381 35877241895224334698461143)
    ·
      refine ⟨53815862842836502047691715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35877241895224334698461143 53815862842836502047691715)
      ·
        refine ⟨80723794264254753071537573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53815862842836502047691715 80723794264254753071537573)
        ·
          refine ⟨15135711424547766200913295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80723794264254753071537573 15135711424547766200913295)
          ·
            refine ⟨22703567136821649301369943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15135711424547766200913295 22703567136821649301369943)
            ·
              refine ⟨34055350705232473952054915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22703567136821649301369943 34055350705232473952054915)
              ·
                refine ⟨51083026057848710928082373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34055350705232473952054915 51083026057848710928082373)
                ·
                  refine ⟨9578067385846633299015445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51083026057848710928082373 9578067385846633299015445)
                  ·
                    refine ⟨448971908711560935891349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9578067385846633299015445 448971908711560935891349)
                    ·
                      rfl

theorem cell23_2623109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_2623109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623109 prefixEnd_2623109 := by exact prefixLift 2623109
  have htrace : WordTrace (prefixWord ++ tailWord_2623109) baseStart_2623109 baseEnd_2623109 := by
    simpa [prefixWord, tailWord_2623109, baseEnd_2623109] using wordTrace_append hprefix tailTrace_2623109
  have hstable : (prefixWord ++ tailWord_2623109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623109).length < 2 ^ (prefixWord ++ tailWord_2623109).sum := by decide
  have hdescent : baseEnd_2623109 < baseStart_2623109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623129 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 1, 4, 4]
def baseStart_2623129 : Nat := 118140960795 + 2623129 * 2 ^ 59
def prefixEnd_2623129 : Nat := 4983230072969 + 3 ^ 40 * 2623129 * 2
def baseEnd_2623129 : Nat := 1346925995747772729423955

theorem tailTrace_2623129 : CollatzResearch.WordTrace tailWord_2623129 prefixEnd_2623129 1346925995747772729423955 := by
  unfold tailWord_2623129
  simp only [CollatzResearch.WordTrace]
  refine ⟨95673374513859102611624441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63782249675906068407749627 95673374513859102611624441)
  ·
    refine ⟨71755030885394326958718331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95673374513859102611624441 71755030885394326958718331)
    ·
      refine ⟨107632546328091490438077497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71755030885394326958718331 107632546328091490438077497)
      ·
        refine ⟨80724409746068617828558123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107632546328091490438077497 80724409746068617828558123)
        ·
          refine ⟨121086614619102926742837185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80724409746068617828558123 121086614619102926742837185)
          ·
            refine ⟨90814960964327195057127889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121086614619102926742837185 90814960964327195057127889)
            ·
              refine ⟨68111220723245396292845917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90814960964327195057127889 68111220723245396292845917)
              ·
                refine ⟨25541707771217023609817219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68111220723245396292845917 25541707771217023609817219)
                ·
                  refine ⟨38312561656825535414725829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25541707771217023609817219 38312561656825535414725829)
                  ·
                    refine ⟨7183605310654787890261093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38312561656825535414725829 7183605310654787890261093)
                    ·
                      refine ⟨1346925995747772729423955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7183605310654787890261093 1346925995747772729423955)
                      ·
                        rfl

theorem cell23_2623129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_2623129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623129 prefixEnd_2623129 := by exact prefixLift 2623129
  have htrace : WordTrace (prefixWord ++ tailWord_2623129) baseStart_2623129 baseEnd_2623129 := by
    simpa [prefixWord, tailWord_2623129, baseEnd_2623129] using wordTrace_append hprefix tailTrace_2623129
  have hstable : (prefixWord ++ tailWord_2623129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623129).length < 2 ^ (prefixWord ++ tailWord_2623129).sum := by decide
  have hdescent : baseEnd_2623129 < baseStart_2623129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623139 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 7]
def baseStart_2623139 : Nat := 118140960795 + 2623139 * 2 ^ 59
def prefixEnd_2623139 : Nat := 4983230072969 + 3 ^ 40 * 2623139 * 2
def baseEnd_2623139 : Nat := 149659014506035298922101

theorem tailTrace_2623139 : CollatzResearch.WordTrace tailWord_2623139 prefixEnd_2623139 149659014506035298922101 := by
  unfold tailWord_2623139
  simp only [CollatzResearch.WordTrace]
  refine ⟨95673739243822874319488471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63782492829215249546325647 95673739243822874319488471)
  ·
    refine ⟨143510608865734311479232707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95673739243822874319488471 143510608865734311479232707)
    ·
      refine ⟨215265913298601467218849061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143510608865734311479232707 215265913298601467218849061)
      ·
        refine ⟨40362358743487775103534199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215265913298601467218849061 40362358743487775103534199)
        ·
          refine ⟨60543538115231662655301299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40362358743487775103534199 60543538115231662655301299)
          ·
            refine ⟨90815307172847493982951949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60543538115231662655301299 90815307172847493982951949)
            ·
              refine ⟨34055740189817810243606981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90815307172847493982951949 34055740189817810243606981)
              ·
                refine ⟨6385451285590839420676309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34055740189817810243606981 6385451285590839420676309)
                ·
                  refine ⟨149659014506035298922101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6385451285590839420676309 149659014506035298922101)
                  ·
                    rfl

theorem cell23_2623139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 7].length) (baseStart_2623139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623139 prefixEnd_2623139 := by exact prefixLift 2623139
  have htrace : WordTrace (prefixWord ++ tailWord_2623139) baseStart_2623139 baseEnd_2623139 := by
    simpa [prefixWord, tailWord_2623139, baseEnd_2623139] using wordTrace_append hprefix tailTrace_2623139
  have hstable : (prefixWord ++ tailWord_2623139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623139).length < 2 ^ (prefixWord ++ tailWord_2623139).sum := by decide
  have hdescent : baseEnd_2623139 < baseStart_2623139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623216 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 7, 4]
def baseStart_2623216 : Nat := 118140960795 + 2623216 * 2 ^ 59
def prefixEnd_2623216 : Nat := 4983230072969 + 3 ^ 40 * 2623216 * 2
def baseEnd_2623216 : Nat := 448990222854904629678685

theorem tailTrace_2623216 : CollatzResearch.WordTrace tailWord_2623216 prefixEnd_2623216 448990222854904629678685 := by
  unfold tailWord_2623216
  simp only [CollatzResearch.WordTrace]
  refine ⟨47838273832271958235020751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63784365109695944313361001 47838273832271958235020751)
  ·
    refine ⟨71757410748407937352531127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47838273832271958235020751 71757410748407937352531127)
    ·
      refine ⟨107636116122611906028796691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71757410748407937352531127 107636116122611906028796691)
      ·
        refine ⟨161454174183917859043195037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107636116122611906028796691 161454174183917859043195037)
        ·
          refine ⟨60545315318969197141198139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161454174183917859043195037 60545315318969197141198139)
          ·
            refine ⟨90817972978453795711797209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60545315318969197141198139 90817972978453795711797209)
            ·
              refine ⟨68113479733840346783847907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90817972978453795711797209 68113479733840346783847907)
              ·
                refine ⟨102170219600760520175771861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68113479733840346783847907 102170219600760520175771861)
                ·
                  refine ⟨2394614521892824691619653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 102170219600760520175771861 2394614521892824691619653)
                  ·
                    refine ⟨448990222854904629678685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2394614521892824691619653 448990222854904629678685)
                    ·
                      rfl

theorem cell23_2623216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 7, 4].length) (baseStart_2623216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623216 prefixEnd_2623216 := by exact prefixLift 2623216
  have htrace : WordTrace (prefixWord ++ tailWord_2623216) baseStart_2623216 baseEnd_2623216 := by
    simpa [prefixWord, tailWord_2623216, baseEnd_2623216] using wordTrace_append hprefix tailTrace_2623216
  have hstable : (prefixWord ++ tailWord_2623216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623216).length < 2 ^ (prefixWord ++ tailWord_2623216).sum := by decide
  have hdescent : baseEnd_2623216 < baseStart_2623216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623226 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3]
def baseStart_2623226 : Nat := 118140960795 + 2623226 * 2 ^ 59
def prefixEnd_2623226 : Nat := 4983230072969 + 3 ^ 40 * 2623226 * 2
def baseEnd_2623226 : Nat := 1346975803371258849911009

theorem tailTrace_2623226 : CollatzResearch.WordTrace tailWord_2623226 prefixEnd_2623226 1346975803371258849911009 := by
  unfold tailWord_2623226
  simp only [CollatzResearch.WordTrace]
  refine ⟨23919228098626922044476383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63784608263005125451937021 23919228098626922044476383)
  ·
    refine ⟨35878842147940383066714575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23919228098626922044476383 35878842147940383066714575)
    ·
      refine ⟨53818263221910574600071863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35878842147940383066714575 53818263221910574600071863)
      ·
        refine ⟨80727394832865861900107795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53818263221910574600071863 80727394832865861900107795)
        ·
          refine ⟨121091092249298792850161693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80727394832865861900107795 121091092249298792850161693)
          ·
            refine ⟨45409159593487047318810635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121091092249298792850161693 45409159593487047318810635)
            ·
              refine ⟨68113739390230570978215953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45409159593487047318810635 68113739390230570978215953)
              ·
                refine ⟨51085304542672928233661965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68113739390230570978215953 51085304542672928233661965)
                ·
                  refine ⟨19156989203502348087623237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51085304542672928233661965 19156989203502348087623237)
                  ·
                    refine ⟨3591935475656690266429357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19156989203502348087623237 3591935475656690266429357)
                    ·
                      refine ⟨1346975803371258849911009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3591935475656690266429357 1346975803371258849911009)
                      ·
                        rfl

theorem cell23_2623226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_2623226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623226 prefixEnd_2623226 := by exact prefixLift 2623226
  have htrace : WordTrace (prefixWord ++ tailWord_2623226) baseStart_2623226 baseEnd_2623226 := by
    simpa [prefixWord, tailWord_2623226, baseEnd_2623226] using wordTrace_append hprefix tailTrace_2623226
  have hstable : (prefixWord ++ tailWord_2623226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623226).length < 2 ^ (prefixWord ++ tailWord_2623226).sum := by decide
  have hdescent : baseEnd_2623226 < baseStart_2623226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623250 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2623250 : Nat := 118140960795 + 2623250 * 2 ^ 59
def prefixEnd_2623250 : Nat := 4983230072969 + 3 ^ 40 * 2623250 * 2
def baseEnd_2623250 : Nat := 448996042302322252003633

theorem tailTrace_2623250 : CollatzResearch.WordTrace tailWord_2623250 prefixEnd_2623250 448996042302322252003633 := by
  unfold tailWord_2623250
  simp only [CollatzResearch.WordTrace]
  refine ⟨23919446936605185069194801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63785191830947160184519469 23919446936605185069194801)
  ·
    refine ⟨17939585202453888801896101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23919446936605185069194801 17939585202453888801896101)
    ·
      refine ⟨3363672225460104150355519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17939585202453888801896101 3363672225460104150355519)
      ·
        refine ⟨5045508338190156225533279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3363672225460104150355519 5045508338190156225533279)
        ·
          refine ⟨7568262507285234338299919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5045508338190156225533279 7568262507285234338299919)
          ·
            refine ⟨11352393760927851507449879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7568262507285234338299919 11352393760927851507449879)
            ·
              refine ⟨17028590641391777261174819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11352393760927851507449879 17028590641391777261174819)
              ·
                refine ⟨25542885962087665891762229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17028590641391777261174819 25542885962087665891762229)
                ·
                  refine ⟨2394645558945718677352709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25542885962087665891762229 2394645558945718677352709)
                  ·
                    refine ⟨448996042302322252003633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2394645558945718677352709 448996042302322252003633)
                    ·
                      rfl

theorem cell23_2623250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2623250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623250 prefixEnd_2623250 := by exact prefixLift 2623250
  have htrace : WordTrace (prefixWord ++ tailWord_2623250) baseStart_2623250 baseEnd_2623250 := by
    simpa [prefixWord, tailWord_2623250, baseEnd_2623250] using wordTrace_append hprefix tailTrace_2623250
  have hstable : (prefixWord ++ tailWord_2623250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623250).length < 2 ^ (prefixWord ++ tailWord_2623250).sum := by decide
  have hdescent : baseEnd_2623250 < baseStart_2623250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623290 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3]
def baseStart_2623290 : Nat := 118140960795 + 2623290 * 2 ^ 59
def prefixEnd_2623290 : Nat := 4983230072969 + 3 ^ 40 * 2623290 * 2
def baseEnd_2623290 : Nat := 1347008666133146599510715

theorem tailTrace_2623290 : CollatzResearch.WordTrace tailWord_2623290 prefixEnd_2623290 1347008666133146599510715 := by
  unfold tailWord_2623290
  simp only [CollatzResearch.WordTrace]
  refine ⟨23919811666568956777058831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63786164444183884738823549 23919811666568956777058831)
  ·
    refine ⟨35879717499853435165588247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23919811666568956777058831 35879717499853435165588247)
    ·
      refine ⟨53819576249780152748382371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35879717499853435165588247 53819576249780152748382371)
      ·
        refine ⟨80729364374670229122573557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53819576249780152748382371 80729364374670229122573557)
        ·
          refine ⟨7568377910125333980241271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80729364374670229122573557 7568377910125333980241271)
          ·
            refine ⟨11352566865188000970361907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7568377910125333980241271 11352566865188000970361907)
            ·
              refine ⟨17028850297782001455542861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11352566865188000970361907 17028850297782001455542861)
              ·
                refine ⟨6385818861668250545828573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17028850297782001455542861 6385818861668250545828573)
                ·
                  refine ⟨2394682073125593954685715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6385818861668250545828573 2394682073125593954685715)
                  ·
                    refine ⟨3592023109688390932028573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2394682073125593954685715 3592023109688390932028573)
                    ·
                      refine ⟨1347008666133146599510715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3592023109688390932028573 1347008666133146599510715)
                      ·
                        rfl

theorem cell23_2623290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_2623290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623290 prefixEnd_2623290 := by exact prefixLift 2623290
  have htrace : WordTrace (prefixWord ++ tailWord_2623290) baseStart_2623290 baseEnd_2623290 := by
    simpa [prefixWord, tailWord_2623290, baseEnd_2623290] using wordTrace_append hprefix tailTrace_2623290
  have hstable : (prefixWord ++ tailWord_2623290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623290).length < 2 ^ (prefixWord ++ tailWord_2623290).sum := by decide
  have hdescent : baseEnd_2623290 < baseStart_2623290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623333 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 5, 2, 3]
def baseStart_2623333 : Nat := 118140960795 + 2623333 * 2 ^ 59
def prefixEnd_2623333 : Nat := 4983230072969 + 3 ^ 40 * 2623333 * 2
def baseEnd_2623333 : Nat := 1347030745801289931273017

theorem tailTrace_2623333 : CollatzResearch.WordTrace tailWord_2623333 prefixEnd_2623333 1347030745801289931273017 := by
  unfold tailWord_2623333
  simp only [CollatzResearch.WordTrace]
  refine ⟨95680815005120045452050653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63787210003413363634700435 95680815005120045452050653)
  ·
    refine ⟨35880305626920017044518995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95680815005120045452050653 35880305626920017044518995)
    ·
      refine ⟨53820458440380025566778493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35880305626920017044518995 53820458440380025566778493)
      ·
        refine ⟨20182671915142509587541935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53820458440380025566778493 20182671915142509587541935)
        ·
          refine ⟨30274007872713764381312903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20182671915142509587541935 30274007872713764381312903)
          ·
            refine ⟨45411011809070646571969355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30274007872713764381312903 45411011809070646571969355)
            ·
              refine ⟨68116517713605969857954033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45411011809070646571969355 68116517713605969857954033)
              ·
                refine ⟨51087388285204477393465525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68116517713605969857954033 51087388285204477393465525)
                ·
                  refine ⟨4789442651737919755637393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51087388285204477393465525 4789442651737919755637393)
                  ·
                    refine ⟨3592081988803439816728045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4789442651737919755637393 3592081988803439816728045)
                    ·
                      refine ⟨1347030745801289931273017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3592081988803439816728045 1347030745801289931273017)
                      ·
                        rfl

theorem cell23_2623333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_2623333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623333 prefixEnd_2623333 := by exact prefixLift 2623333
  have htrace : WordTrace (prefixWord ++ tailWord_2623333) baseStart_2623333 baseEnd_2623333 := by
    simpa [prefixWord, tailWord_2623333, baseEnd_2623333] using wordTrace_append hprefix tailTrace_2623333
  have hstable : (prefixWord ++ tailWord_2623333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623333).length < 2 ^ (prefixWord ++ tailWord_2623333).sum := by decide
  have hdescent : baseEnd_2623333 < baseStart_2623333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623380 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_2623380 : Nat := 118140960795 + 2623380 * 2 ^ 59
def prefixEnd_2623380 : Nat := 4983230072969 + 3 ^ 40 * 2623380 * 2
def baseEnd_2623380 : Nat := 1347054879392051247385301

theorem tailTrace_2623380 : CollatzResearch.WordTrace tailWord_2623380 prefixEnd_2623380 1347054879392051247385301 := by
  unfold tailWord_2623380
  simp only [CollatzResearch.WordTrace]
  refine ⟨47841264617974886239505797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63788352823966514986007729 47841264617974886239505797)
  ·
    refine ⟨8970237115870291169907337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47841264617974886239505797 8970237115870291169907337)
    ·
      refine ⟨6727677836902718377430503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8970237115870291169907337 6727677836902718377430503)
      ·
        refine ⟨10091516755354077566145755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6727677836902718377430503 10091516755354077566145755)
        ·
          refine ⟨15137275133031116349218633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10091516755354077566145755 15137275133031116349218633)
          ·
            refine ⟨11352956349773337261913975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15137275133031116349218633 11352956349773337261913975)
            ·
              refine ⟨17029434524660005892870963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11352956349773337261913975 17029434524660005892870963)
              ·
                refine ⟨25544151786990008839306445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17029434524660005892870963 25544151786990008839306445)
                ·
                  refine ⟨9579056920121253314739917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25544151786990008839306445 9579056920121253314739917)
                  ·
                    refine ⟨3592146345045469993027469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9579056920121253314739917 3592146345045469993027469)
                    ·
                      refine ⟨1347054879392051247385301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3592146345045469993027469 1347054879392051247385301)
                      ·
                        rfl

theorem cell23_2623380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_2623380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623380 prefixEnd_2623380 := by exact prefixLift 2623380
  have htrace : WordTrace (prefixWord ++ tailWord_2623380) baseStart_2623380 baseEnd_2623380 := by
    simpa [prefixWord, tailWord_2623380, baseEnd_2623380] using wordTrace_append hprefix tailTrace_2623380
  have hstable : (prefixWord ++ tailWord_2623380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623380).length < 2 ^ (prefixWord ++ tailWord_2623380).sum := by decide
  have hdescent : baseEnd_2623380 < baseStart_2623380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623384 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 1, 1, 5]
def baseStart_2623384 : Nat := 118140960795 + 2623384 * 2 ^ 59
def prefixEnd_2623384 : Nat := 4983230072969 + 3 ^ 40 * 2623384 * 2
def baseEnd_2623384 : Nat := 1347056933314669231735283

theorem tailTrace_2623384 : CollatzResearch.WordTrace tailWord_2623384 prefixEnd_2623384 1347056933314669231735283 := by
  unfold tailWord_2623384
  simp only [CollatzResearch.WordTrace]
  refine ⟨47841337563967640581078603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63788450085290187441438137 47841337563967640581078603)
  ·
    refine ⟨71762006345951460871617905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47841337563967640581078603 71762006345951460871617905)
    ·
      refine ⟨53821504759463595653713429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71762006345951460871617905 53821504759463595653713429)
      ·
        refine ⟨2522883035599856046267817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53821504759463595653713429 2522883035599856046267817)
        ·
          refine ⟨1892162276699892034700863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2522883035599856046267817 1892162276699892034700863)
          ·
            refine ⟨2838243415049838052051295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892162276699892034700863 2838243415049838052051295)
            ·
              refine ⟨4257365122574757078076943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2838243415049838052051295 4257365122574757078076943)
              ·
                refine ⟨6386047683862135617115415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4257365122574757078076943 6386047683862135617115415)
                ·
                  refine ⟨9579071525793203425673123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6386047683862135617115415 9579071525793203425673123)
                  ·
                    refine ⟨14368607288689805138509685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9579071525793203425673123 14368607288689805138509685)
                    ·
                      refine ⟨1347056933314669231735283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14368607288689805138509685 1347056933314669231735283)
                      ·
                        rfl

theorem cell23_2623384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_2623384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623384 prefixEnd_2623384 := by exact prefixLift 2623384
  have htrace : WordTrace (prefixWord ++ tailWord_2623384) baseStart_2623384 baseEnd_2623384 := by
    simpa [prefixWord, tailWord_2623384, baseEnd_2623384] using wordTrace_append hprefix tailTrace_2623384
  have hstable : (prefixWord ++ tailWord_2623384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623384).length < 2 ^ (prefixWord ++ tailWord_2623384).sum := by decide
  have hdescent : baseEnd_2623384 < baseStart_2623384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623413 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2623413 : Nat := 118140960795 + 2623413 * 2 ^ 59
def prefixEnd_2623413 : Nat := 4983230072969 + 3 ^ 40 * 2623413 * 2
def baseEnd_2623413 : Nat := 449023941417883206090883

theorem tailTrace_2623413 : CollatzResearch.WordTrace tailWord_2623413 prefixEnd_2623413 449023941417883206090883 := by
  unfold tailWord_2623413
  simp only [CollatzResearch.WordTrace]
  refine ⟨95683732844830219114962893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63789155229886812743308595 95683732844830219114962893)
  ·
    refine ⟨35881399816811332168111085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95683732844830219114962893 35881399816811332168111085)
    ·
      refine ⟨13455524931304249563041657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35881399816811332168111085 13455524931304249563041657)
      ·
        refine ⟨10091643698478187172281243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13455524931304249563041657 10091643698478187172281243)
        ·
          refine ⟨15137465547717280758421865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10091643698478187172281243 15137465547717280758421865)
          ·
            refine ⟨11353099160787960568816399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15137465547717280758421865 11353099160787960568816399)
            ·
              refine ⟨17029648741181940853224599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11353099160787960568816399 17029648741181940853224599)
              ·
                refine ⟨25544473111772911279836899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17029648741181940853224599 25544473111772911279836899)
                ·
                  refine ⟨38316709667659366919755349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25544473111772911279836899 38316709667659366919755349)
                  ·
                    refine ⟨449023941417883206090883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38316709667659366919755349 449023941417883206090883)
                    ·
                      rfl

theorem cell23_2623413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2623413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623413 prefixEnd_2623413 := by exact prefixLift 2623413
  have htrace : WordTrace (prefixWord ++ tailWord_2623413) baseStart_2623413 baseEnd_2623413 := by
    simpa [prefixWord, tailWord_2623413, baseEnd_2623413] using wordTrace_append hprefix tailTrace_2623413
  have hstable : (prefixWord ++ tailWord_2623413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623413).length < 2 ^ (prefixWord ++ tailWord_2623413).sum := by decide
  have hdescent : baseEnd_2623413 < baseStart_2623413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623423 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 3]
def baseStart_2623423 : Nat := 118140960795 + 2623423 * 2 ^ 59
def prefixEnd_2623423 : Nat := 4983230072969 + 3 ^ 40 * 2623423 * 2
def baseEnd_2623423 : Nat := 1347076959060194579147603

theorem tailTrace_2623423 : CollatzResearch.WordTrace tailWord_2623423 prefixEnd_2623423 1347076959060194579147603 := by
  unfold tailWord_2623423
  simp only [CollatzResearch.WordTrace]
  refine ⟨95684097574793990822826923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63789398383195993881884615 95684097574793990822826923)
  ·
    refine ⟨143526146362190986234240385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95684097574793990822826923 143526146362190986234240385)
    ·
      refine ⟨107644609771643239675680289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143526146362190986234240385 107644609771643239675680289)
      ·
        refine ⟨80733457328732429756760217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107644609771643239675680289 80733457328732429756760217)
        ·
          refine ⟨60550092996549322317570163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80733457328732429756760217 60550092996549322317570163)
          ·
            refine ⟨90825139494823983476355245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60550092996549322317570163 90825139494823983476355245)
            ·
              refine ⟨34059427310558993803633217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90825139494823983476355245 34059427310558993803633217)
              ·
                refine ⟨25544570482919245352724913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34059427310558993803633217 25544570482919245352724913)
                ·
                  refine ⟨19158427862189434014543685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25544570482919245352724913 19158427862189434014543685)
                  ·
                    refine ⟨3592205224160518877726941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19158427862189434014543685 3592205224160518877726941)
                    ·
                      refine ⟨1347076959060194579147603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3592205224160518877726941 1347076959060194579147603)
                      ·
                        rfl

theorem cell23_2623423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_2623423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623423 prefixEnd_2623423 := by exact prefixLift 2623423
  have htrace : WordTrace (prefixWord ++ tailWord_2623423) baseStart_2623423 baseEnd_2623423 := by
    simpa [prefixWord, tailWord_2623423, baseEnd_2623423] using wordTrace_append hprefix tailTrace_2623423
  have hstable : (prefixWord ++ tailWord_2623423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623423).length < 2 ^ (prefixWord ++ tailWord_2623423).sum := by decide
  have hdescent : baseEnd_2623423 < baseStart_2623423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623460 : List Nat := [2, 3, 1, 1, 1, 1, 3, 6, 5]
def baseStart_2623460 : Nat := 118140960795 + 2623460 * 2 ^ 59
def prefixEnd_2623460 : Nat := 4983230072969 + 3 ^ 40 * 2623460 * 2
def baseEnd_2623460 : Nat := 149677328649378992709437

theorem tailTrace_2623460 : CollatzResearch.WordTrace tailWord_2623460 prefixEnd_2623460 149677328649378992709437 := by
  unfold tailWord_2623460
  simp only [CollatzResearch.WordTrace]
  refine ⟨47842723537829973070961917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63790298050439964094615889 47842723537829973070961917)
  ·
    refine ⟨17941021326686239901610719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47842723537829973070961917 17941021326686239901610719)
    ·
      refine ⟨26911531990029359852416079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17941021326686239901610719 26911531990029359852416079)
      ·
        refine ⟨40367297985044039778624119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26911531990029359852416079 40367297985044039778624119)
        ·
          refine ⟨60550946977566059667936179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40367297985044039778624119 60550946977566059667936179)
          ·
            refine ⟨90826420466349089501904269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60550946977566059667936179 90826420466349089501904269)
            ·
              refine ⟨34059907674880908563214101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90826420466349089501904269 34059907674880908563214101)
              ·
                refine ⟨1596558172260042588900661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34059907674880908563214101 1596558172260042588900661)
                ·
                  refine ⟨149677328649378992709437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1596558172260042588900661 149677328649378992709437)
                  ·
                    rfl

theorem cell23_2623460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_2623460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623460 prefixEnd_2623460 := by exact prefixLift 2623460
  have htrace : WordTrace (prefixWord ++ tailWord_2623460) baseStart_2623460 baseEnd_2623460 := by
    simpa [prefixWord, tailWord_2623460, baseEnd_2623460] using wordTrace_append hprefix tailTrace_2623460
  have hstable : (prefixWord ++ tailWord_2623460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623460).length < 2 ^ (prefixWord ++ tailWord_2623460).sum := by decide
  have hdescent : baseEnd_2623460 < baseStart_2623460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623480 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 2, 5, 2]
def baseStart_2623480 : Nat := 118140960795 + 2623480 * 2 ^ 59
def prefixEnd_2623480 : Nat := 4983230072969 + 3 ^ 40 * 2623480 * 2
def baseEnd_2623480 : Nat := 1347106227457500856134841

theorem tailTrace_2623480 : CollatzResearch.WordTrace tailWord_2623480 prefixEnd_2623480 1347106227457500856134841 := by
  unfold tailWord_2623480
  simp only [CollatzResearch.WordTrace]
  refine ⟨47843088267793744778825947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63790784357058326371767929 47843088267793744778825947)
  ·
    refine ⟨71764632401690617168238921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47843088267793744778825947 71764632401690617168238921)
    ·
      refine ⟨53823474301267962876179191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71764632401690617168238921 53823474301267962876179191)
      ·
        refine ⟨80735211451901944314268787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53823474301267962876179191 80735211451901944314268787)
        ·
          refine ⟨121102817177852916471403181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80735211451901944314268787 121102817177852916471403181)
          ·
            refine ⟨45413556441694843676776193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121102817177852916471403181 45413556441694843676776193)
            ·
              refine ⟨34060167331271132757582145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45413556441694843676776193 34060167331271132757582145)
              ·
                refine ⟨25545125498453349568186609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34060167331271132757582145 25545125498453349568186609)
                ·
                  refine ⟨19158844123840012176139957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25545125498453349568186609 19158844123840012176139957)
                  ·
                    refine ⟨1796141636610001141513121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19158844123840012176139957 1796141636610001141513121)
                    ·
                      refine ⟨1347106227457500856134841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1796141636610001141513121 1347106227457500856134841)
                      ·
                        rfl

theorem cell23_2623480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 5, 2].length) (baseStart_2623480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623480 prefixEnd_2623480 := by exact prefixLift 2623480
  have htrace : WordTrace (prefixWord ++ tailWord_2623480) baseStart_2623480 baseEnd_2623480 := by
    simpa [prefixWord, tailWord_2623480, baseEnd_2623480] using wordTrace_append hprefix tailTrace_2623480
  have hstable : (prefixWord ++ tailWord_2623480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623480).length < 2 ^ (prefixWord ++ tailWord_2623480).sum := by decide
  have hdescent : baseEnd_2623480 < baseStart_2623480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623577 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 3, 1, 3]
def baseStart_2623577 : Nat := 118140960795 + 2623577 * 2 ^ 59
def prefixEnd_2623577 : Nat := 4983230072969 + 3 ^ 40 * 2623577 * 2
def baseEnd_2623577 : Nat := 1347156035080986976621895

theorem tailTrace_2623577 : CollatzResearch.WordTrace tailWord_2623577 prefixEnd_2623577 1347156035080986976621895 := by
  unfold tailWord_2623577
  simp only [CollatzResearch.WordTrace]
  refine ⟨95689714416236075123932985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63793142944157383415955323 95689714416236075123932985)
  ·
    refine ⟨71767285812177056342949739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95689714416236075123932985 71767285812177056342949739)
    ·
      refine ⟨107650928718265584514424609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71767285812177056342949739 107650928718265584514424609)
      ·
        refine ⟨80738196538699188385818457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107650928718265584514424609 80738196538699188385818457)
        ·
          refine ⟨60553647404024391289363843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80738196538699188385818457 60553647404024391289363843)
          ·
            refine ⟨90830471106036586934045765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60553647404024391289363843 90830471106036586934045765)
            ·
              refine ⟨17030713332381860050133581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90830471106036586934045765 17030713332381860050133581)
              ·
                refine ⟨6386517499643197518800093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17030713332381860050133581 6386517499643197518800093)
                ·
                  refine ⟨2394944062366199069550035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6386517499643197518800093 2394944062366199069550035)
                  ·
                    refine ⟨3592416093549298604325053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2394944062366199069550035 3592416093549298604325053)
                    ·
                      refine ⟨1347156035080986976621895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3592416093549298604325053 1347156035080986976621895)
                      ·
                        rfl

theorem cell23_2623577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_2623577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623577 prefixEnd_2623577 := by exact prefixLift 2623577
  have htrace : WordTrace (prefixWord ++ tailWord_2623577) baseStart_2623577 baseEnd_2623577 := by
    simpa [prefixWord, tailWord_2623577, baseEnd_2623577] using wordTrace_append hprefix tailTrace_2623577
  have hstable : (prefixWord ++ tailWord_2623577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623577).length < 2 ^ (prefixWord ++ tailWord_2623577).sum := by decide
  have hdescent : baseEnd_2623577 < baseStart_2623577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623587 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 4, 3, 2]
def baseStart_2623587 : Nat := 118140960795 + 2623587 * 2 ^ 59
def prefixEnd_2623587 : Nat := 4983230072969 + 3 ^ 40 * 2623587 * 2
def baseEnd_2623587 : Nat := 1347161169887531937496849

theorem tailTrace_2623587 : CollatzResearch.WordTrace tailWord_2623587 prefixEnd_2623587 1347161169887531937496849 := by
  unfold tailWord_2623587
  simp only [CollatzResearch.WordTrace]
  refine ⟨95690079146199846831797015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63793386097466564554531343 95690079146199846831797015)
  ·
    refine ⟨143535118719299770247695523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95690079146199846831797015 143535118719299770247695523)
    ·
      refine ⟨215302678078949655371543285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143535118719299770247695523 215302678078949655371543285)
      ·
        refine ⟨20184626069901530191082183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 215302678078949655371543285 20184626069901530191082183)
        ·
          refine ⟨30276939104852295286623275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20184626069901530191082183 30276939104852295286623275)
          ·
            refine ⟨45415408657278442929934913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30276939104852295286623275 45415408657278442929934913)
            ·
              refine ⟨34061556492958832197451185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45415408657278442929934913 34061556492958832197451185)
              ·
                refine ⟨25546167369719124148088389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34061556492958832197451185 25546167369719124148088389)
                ·
                  refine ⟨4789906381822335777766573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25546167369719124148088389 4789906381822335777766573)
                  ·
                    refine ⟨1796214893183375916662465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4789906381822335777766573 1796214893183375916662465)
                    ·
                      refine ⟨1347161169887531937496849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1796214893183375916662465 1347161169887531937496849)
                      ·
                        rfl

theorem cell23_2623587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_2623587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623587 prefixEnd_2623587 := by exact prefixLift 2623587
  have htrace : WordTrace (prefixWord ++ tailWord_2623587) baseStart_2623587 baseEnd_2623587 := by
    simpa [prefixWord, tailWord_2623587, baseEnd_2623587] using wordTrace_append hprefix tailTrace_2623587
  have hstable : (prefixWord ++ tailWord_2623587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623587).length < 2 ^ (prefixWord ++ tailWord_2623587).sum := by decide
  have hdescent : baseEnd_2623587 < baseStart_2623587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623597 : List Nat := [1, 5, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_2623597 : Nat := 118140960795 + 2623597 * 2 ^ 59
def prefixEnd_2623597 : Nat := 4983230072969 + 3 ^ 40 * 2623597 * 2
def baseEnd_2623597 : Nat := 449055434898025632790601

theorem tailTrace_2623597 : CollatzResearch.WordTrace tailWord_2623597 prefixEnd_2623597 449055434898025632790601 := by
  unfold tailWord_2623597
  simp only [CollatzResearch.WordTrace]
  refine ⟨95690443876163618539661045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63793629250775745693107363 95690443876163618539661045)
  ·
    refine ⟨8970979113390339238093223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95690443876163618539661045 8970979113390339238093223)
    ·
      refine ⟨13456468670085508857139835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8970979113390339238093223 13456468670085508857139835)
      ·
        refine ⟨20184703005128263285709753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13456468670085508857139835 20184703005128263285709753)
        ·
          refine ⟨15138527253846197464282315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20184703005128263285709753 15138527253846197464282315)
          ·
            refine ⟨22707790880769296196423473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15138527253846197464282315 22707790880769296196423473)
            ·
              refine ⟨17030843160576972147317605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22707790880769296196423473 17030843160576972147317605)
              ·
                refine ⟨3193283092608182277622051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17030843160576972147317605 3193283092608182277622051)
                ·
                  refine ⟨4789924638912273416433077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3193283092608182277622051 4789924638912273416433077)
                  ·
                    refine ⟨449055434898025632790601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4789924638912273416433077 449055434898025632790601)
                    ·
                      rfl

theorem cell23_2623597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_2623597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623597 prefixEnd_2623597 := by exact prefixLift 2623597
  have htrace : WordTrace (prefixWord ++ tailWord_2623597) baseStart_2623597 baseEnd_2623597 := by
    simpa [prefixWord, tailWord_2623597, baseEnd_2623597] using wordTrace_append hprefix tailTrace_2623597
  have hstable : (prefixWord ++ tailWord_2623597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623597).length < 2 ^ (prefixWord ++ tailWord_2623597).sum := by decide
  have hdescent : baseEnd_2623597 < baseStart_2623597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623647 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2623647 : Nat := 118140960795 + 2623647 * 2 ^ 59
def prefixEnd_2623647 : Nat := 4983230072969 + 3 ^ 40 * 2623647 * 2
def baseEnd_2623647 : Nat := 1347191978726801702746573

theorem tailTrace_2623647 : CollatzResearch.WordTrace tailWord_2623647 prefixEnd_2623647 1347191978726801702746573 := by
  unfold tailWord_2623647
  simp only [CollatzResearch.WordTrace]
  refine ⟨95692267525982477078981195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63794845017321651385987463 95692267525982477078981195)
  ·
    refine ⟨143538401288973715618471793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95692267525982477078981195 143538401288973715618471793)
    ·
      refine ⟨107653800966730286713853845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143538401288973715618471793 107653800966730286713853845)
      ·
        refine ⟨5046271920315482189711899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107653800966730286713853845 5046271920315482189711899)
        ·
          refine ⟨7569407880473223284567849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5046271920315482189711899 7569407880473223284567849)
          ·
            refine ⟨5677055910354917463425887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7569407880473223284567849 5677055910354917463425887)
            ·
              refine ⟨8515583865532376195138831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5677055910354917463425887 8515583865532376195138831)
              ·
                refine ⟨12773375798298564292708247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8515583865532376195138831 12773375798298564292708247)
                ·
                  refine ⟨19160063697447846439062371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12773375798298564292708247 19160063697447846439062371)
                  ·
                    refine ⟨28740095546171769658593557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19160063697447846439062371 28740095546171769658593557)
                    ·
                      refine ⟨1347191978726801702746573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28740095546171769658593557 1347191978726801702746573)
                      ·
                        rfl

theorem cell23_2623647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2623647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623647 prefixEnd_2623647 := by exact prefixLift 2623647
  have htrace : WordTrace (prefixWord ++ tailWord_2623647) baseStart_2623647 baseEnd_2623647 := by
    simpa [prefixWord, tailWord_2623647, baseEnd_2623647] using wordTrace_append hprefix tailTrace_2623647
  have hstable : (prefixWord ++ tailWord_2623647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623647).length < 2 ^ (prefixWord ++ tailWord_2623647).sum := by decide
  have hdescent : baseEnd_2623647 < baseStart_2623647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623662 : List Nat := [4, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_2623662 : Nat := 118140960795 + 2623662 * 2 ^ 59
def prefixEnd_2623662 : Nat := 4983230072969 + 3 ^ 40 * 2623662 * 2
def baseEnd_2623662 : Nat := 1347199680936619144059005

theorem tailTrace_2623662 : CollatzResearch.WordTrace tailWord_2623662 prefixEnd_2623662 1347199680936619144059005 := by
  unfold tailWord_2623662
  simp only [CollatzResearch.WordTrace]
  refine ⟨11961601827616016830097155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63795209747285423093851493 11961601827616016830097155)
  ·
    refine ⟨17942402741424025245145733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11961601827616016830097155 17942402741424025245145733)
    ·
      refine ⟨3364200514017004733464825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17942402741424025245145733 3364200514017004733464825)
      ·
        refine ⟨2523150385512753550098619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3364200514017004733464825 2523150385512753550098619)
        ·
          refine ⟨3784725578269130325147929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2523150385512753550098619 3784725578269130325147929)
          ·
            refine ⟨2838544183701847743860947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3784725578269130325147929 2838544183701847743860947)
            ·
              refine ⟨4257816275552771615791421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2838544183701847743860947 4257816275552771615791421)
              ·
                refine ⟨1596681103332289355921783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4257816275552771615791421 1596681103332289355921783)
                ·
                  refine ⟨2395021654998434033882675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596681103332289355921783 2395021654998434033882675)
                  ·
                    refine ⟨3592532482497651050824013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2395021654998434033882675 3592532482497651050824013)
                    ·
                      refine ⟨1347199680936619144059005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3592532482497651050824013 1347199680936619144059005)
                      ·
                        rfl

theorem cell23_2623662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_2623662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623662 prefixEnd_2623662 := by exact prefixLift 2623662
  have htrace : WordTrace (prefixWord ++ tailWord_2623662) baseStart_2623662 baseEnd_2623662 := by
    simpa [prefixWord, tailWord_2623662, baseEnd_2623662] using wordTrace_append hprefix tailTrace_2623662
  have hstable : (prefixWord ++ tailWord_2623662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623662).length < 2 ^ (prefixWord ++ tailWord_2623662).sum := by decide
  have hdescent : baseEnd_2623662 < baseStart_2623662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623724 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 1, 4, 2]
def baseStart_2623724 : Nat := 118140960795 + 2623724 * 2 ^ 59
def prefixEnd_2623724 : Nat := 4983230072969 + 3 ^ 40 * 2623724 * 2
def baseEnd_2623724 : Nat := 1347231516737197901483719

theorem tailTrace_2623724 : CollatzResearch.WordTrace tailWord_2623724 prefixEnd_2623724 1347231516737197901483719 := by
  unfold tailWord_2623724
  simp only [CollatzResearch.WordTrace]
  refine ⟨47847537973351759614767113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63796717297802346153022817 47847537973351759614767113)
  ·
    refine ⟨35885653480013819711075335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47847537973351759614767113 35885653480013819711075335)
    ·
      refine ⟨53828480220020729566613003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35885653480013819711075335 53828480220020729566613003)
      ·
        refine ⟨80742720330031094349919505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53828480220020729566613003 80742720330031094349919505)
        ·
          refine ⟨60557040247523320762439629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80742720330031094349919505 60557040247523320762439629)
          ·
            refine ⟨22708890092821245285914861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60557040247523320762439629 22708890092821245285914861)
            ·
              refine ⟨8515833784807966982218073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22708890092821245285914861 8515833784807966982218073)
              ·
                refine ⟨6386875338605975236663555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8515833784807966982218073 6386875338605975236663555)
                ·
                  refine ⟨9580313007908962854995333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6386875338605975236663555 9580313007908962854995333)
                  ·
                    refine ⟨1796308688982930535311625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9580313007908962854995333 1796308688982930535311625)
                    ·
                      refine ⟨1347231516737197901483719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1796308688982930535311625 1347231516737197901483719)
                      ·
                        rfl

theorem cell23_2623724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 4, 2].length) (baseStart_2623724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623724 prefixEnd_2623724 := by exact prefixLift 2623724
  have htrace : WordTrace (prefixWord ++ tailWord_2623724) baseStart_2623724 baseEnd_2623724 := by
    simpa [prefixWord, tailWord_2623724, baseEnd_2623724] using wordTrace_append hprefix tailTrace_2623724
  have hstable : (prefixWord ++ tailWord_2623724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623724).length < 2 ^ (prefixWord ++ tailWord_2623724).sum := by decide
  have hdescent : baseEnd_2623724 < baseStart_2623724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623727 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 5]
def baseStart_2623727 : Nat := 118140960795 + 2623727 * 2 ^ 59
def prefixEnd_2623727 : Nat := 4983230072969 + 3 ^ 40 * 2623727 * 2
def baseEnd_2623727 : Nat := 1347233057179161389746205

theorem tailTrace_2623727 : CollatzResearch.WordTrace tailWord_2623727 prefixEnd_2623727 1347233057179161389746205 := by
  unfold tailWord_2623727
  simp only [CollatzResearch.WordTrace]
  refine ⟨95695185365692650741893435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63796790243795100494595623 95695185365692650741893435)
  ·
    refine ⟨143542778048538976112840153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95695185365692650741893435 143542778048538976112840153)
    ·
      refine ⟨107657083536404232084630115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143542778048538976112840153 107657083536404232084630115)
      ·
        refine ⟨161485625304606348126945173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107657083536404232084630115 161485625304606348126945173)
        ·
          refine ⟨7569638686153422568450555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 161485625304606348126945173 7569638686153422568450555)
          ·
            refine ⟨11354458029230133852675833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7569638686153422568450555 11354458029230133852675833)
            ·
              refine ⟨8515843521922600389506875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11354458029230133852675833 8515843521922600389506875)
              ·
                refine ⟨12773765282883900584260313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8515843521922600389506875 12773765282883900584260313)
                ·
                  refine ⟨9580323962162925438195235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12773765282883900584260313 9580323962162925438195235)
                  ·
                    refine ⟨14370485943244388157292853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9580323962162925438195235 14370485943244388157292853)
                    ·
                      refine ⟨1347233057179161389746205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14370485943244388157292853 1347233057179161389746205)
                      ·
                        rfl

theorem cell23_2623727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_2623727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623727 prefixEnd_2623727 := by exact prefixLift 2623727
  have htrace : WordTrace (prefixWord ++ tailWord_2623727) baseStart_2623727 baseEnd_2623727 := by
    simpa [prefixWord, tailWord_2623727, baseEnd_2623727] using wordTrace_append hprefix tailTrace_2623727
  have hstable : (prefixWord ++ tailWord_2623727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623727).length < 2 ^ (prefixWord ++ tailWord_2623727).sum := by decide
  have hdescent : baseEnd_2623727 < baseStart_2623727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623781 : List Nat := [1, 3, 1, 2, 5, 1, 2, 3, 5]
def baseStart_2623781 : Nat := 118140960795 + 2623781 * 2 ^ 59
def prefixEnd_2623781 : Nat := 4983230072969 + 3 ^ 40 * 2623781 * 2
def baseEnd_2623781 : Nat := 149695642792722686496773

theorem tailTrace_2623781 : CollatzResearch.WordTrace tailWord_2623781 prefixEnd_2623781 149695642792722686496773 := by
  unfold tailWord_2623781
  simp only [CollatzResearch.WordTrace]
  refine ⟨95697154907497017964359197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63798103271664678642906131 95697154907497017964359197)
  ·
    refine ⟨35886433090311381736634699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95697154907497017964359197 35886433090311381736634699)
    ·
      refine ⟨53829649635467072604952049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35886433090311381736634699 53829649635467072604952049)
      ·
        refine ⟨40372237226600304453714037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53829649635467072604952049 40372237226600304453714037)
        ·
          refine ⟨3784897239993778542535691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40372237226600304453714037 3784897239993778542535691)
          ·
            refine ⟨5677345859990667813803537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784897239993778542535691 5677345859990667813803537)
            ·
              refine ⟨4258009394993000860352653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5677345859990667813803537 4258009394993000860352653)
              ·
                refine ⟨1596753523122375322632245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4258009394993000860352653 1596753523122375322632245)
                ·
                  refine ⟨149695642792722686496773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1596753523122375322632245 149695642792722686496773)
                  ·
                    rfl

theorem cell23_2623781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 5].length) (baseStart_2623781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623781 prefixEnd_2623781 := by exact prefixLift 2623781
  have htrace : WordTrace (prefixWord ++ tailWord_2623781) baseStart_2623781 baseEnd_2623781 := by
    simpa [prefixWord, tailWord_2623781, baseEnd_2623781] using wordTrace_append hprefix tailTrace_2623781
  have hstable : (prefixWord ++ tailWord_2623781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623781).length < 2 ^ (prefixWord ++ tailWord_2623781).sum := by decide
  have hdescent : baseEnd_2623781 < baseStart_2623781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623824 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 3, 4]
def baseStart_2623824 : Nat := 118140960795 + 2623824 * 2 ^ 59
def prefixEnd_2623824 : Nat := 4983230072969 + 3 ^ 40 * 2623824 * 2
def baseEnd_2623824 : Nat := 449094288267549170077753

theorem tailTrace_2623824 : CollatzResearch.WordTrace tailWord_2623824 prefixEnd_2623824 449094288267549170077753 := by
  unfold tailWord_2623824
  simp only [CollatzResearch.WordTrace]
  refine ⟨47849361623170618154087263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63799148830894157538783017 47849361623170618154087263)
  ·
    refine ⟨71774042434755927231130895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47849361623170618154087263 71774042434755927231130895)
    ·
      refine ⟨107661063652133890846696343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71774042434755927231130895 107661063652133890846696343)
      ·
        refine ⟨161491595478200836270044515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107661063652133890846696343 161491595478200836270044515)
        ·
          refine ⟨242237393217301254405066773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161491595478200836270044515 242237393217301254405066773)
          ·
            refine ⟨11354877807060996300237505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 242237393217301254405066773 11354877807060996300237505)
            ·
              refine ⟨8516158355295747225178129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11354877807060996300237505 8516158355295747225178129)
              ·
                refine ⟨6387118766471810418883597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8516158355295747225178129 6387118766471810418883597)
                ·
                  refine ⟨2395169537426928907081349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6387118766471810418883597 2395169537426928907081349)
                  ·
                    refine ⟨449094288267549170077753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2395169537426928907081349 449094288267549170077753)
                    ·
                      rfl

theorem cell23_2623824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 3, 4].length) (baseStart_2623824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623824 prefixEnd_2623824 := by exact prefixLift 2623824
  have htrace : WordTrace (prefixWord ++ tailWord_2623824) baseStart_2623824 baseEnd_2623824 := by
    simpa [prefixWord, tailWord_2623824, baseEnd_2623824] using wordTrace_append hprefix tailTrace_2623824
  have hstable : (prefixWord ++ tailWord_2623824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623824).length < 2 ^ (prefixWord ++ tailWord_2623824).sum := by decide
  have hdescent : baseEnd_2623824 < baseStart_2623824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623834 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3]
def baseStart_2623834 : Nat := 118140960795 + 2623834 * 2 ^ 59
def prefixEnd_2623834 : Nat := 4983230072969 + 3 ^ 40 * 2623834 * 2
def baseEnd_2623834 : Nat := 1347287999609192471108213

theorem tailTrace_2623834 : CollatzResearch.WordTrace tailWord_2623834 prefixEnd_2623834 1347287999609192471108213 := by
  unfold tailWord_2623834
  simp only [CollatzResearch.WordTrace]
  refine ⟨23924771994076252004009639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63799391984203338677359037 23924771994076252004009639)
  ·
    refine ⟨35887157991114378006014459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23924771994076252004009639 35887157991114378006014459)
    ·
      refine ⟨53830736986671567009021689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35887157991114378006014459 53830736986671567009021689)
      ·
        refine ⟨40373052740003675256766267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53830736986671567009021689 40373052740003675256766267)
        ·
          refine ⟨60559579110005512885149401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40373052740003675256766267 60559579110005512885149401)
          ·
            refine ⟨45419684332504134663862051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60559579110005512885149401 45419684332504134663862051)
            ·
              refine ⟨68129526498756201995793077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45419684332504134663862051 68129526498756201995793077)
              ·
                refine ⟨6387143109258393937105601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68129526498756201995793077 6387143109258393937105601)
                ·
                  refine ⟨4790357331943795452829201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6387143109258393937105601 4790357331943795452829201)
                  ·
                    refine ⟨3592767998957846589621901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4790357331943795452829201 3592767998957846589621901)
                    ·
                      refine ⟨1347287999609192471108213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3592767998957846589621901 1347287999609192471108213)
                      ·
                        rfl

theorem cell23_2623834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_2623834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623834 prefixEnd_2623834 := by exact prefixLift 2623834
  have htrace : WordTrace (prefixWord ++ tailWord_2623834) baseStart_2623834 baseEnd_2623834 := by
    simpa [prefixWord, tailWord_2623834, baseEnd_2623834] using wordTrace_append hprefix tailTrace_2623834
  have hstable : (prefixWord ++ tailWord_2623834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623834).length < 2 ^ (prefixWord ++ tailWord_2623834).sum := by decide
  have hdescent : baseEnd_2623834 < baseStart_2623834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623884 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 3, 5]
def baseStart_2623884 : Nat := 118140960795 + 2623884 * 2 ^ 59
def prefixEnd_2623884 : Nat := 4983230072969 + 3 ^ 40 * 2623884 * 2
def baseEnd_2623884 : Nat := 449104557880639091827661

theorem tailTrace_2623884 : CollatzResearch.WordTrace tailWord_2623884 prefixEnd_2623884 449104557880639091827661 := by
  unfold tailWord_2623884
  simp only [CollatzResearch.WordTrace]
  refine ⟨47850455813061933277679353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63800607750749244370239137 47850455813061933277679353)
  ·
    refine ⟨35887841859796449958259515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47850455813061933277679353 35887841859796449958259515)
    ·
      refine ⟨53831762789694674937389273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35887841859796449958259515 53831762789694674937389273)
      ·
        refine ⟨40373822092271006203041955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53831762789694674937389273 40373822092271006203041955)
        ·
          refine ⟨60560733138406509304562933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40373822092271006203041955 60560733138406509304562933)
          ·
            refine ⟨5677568731725610247302775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60560733138406509304562933 5677568731725610247302775)
            ·
              refine ⟨8516353097588415370954163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5677568731725610247302775 8516353097588415370954163)
              ·
                refine ⟨12774529646382623056431245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8516353097588415370954163 12774529646382623056431245)
                ·
                  refine ⟨4790448617393483646161717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12774529646382623056431245 4790448617393483646161717)
                  ·
                    refine ⟨449104557880639091827661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4790448617393483646161717 449104557880639091827661)
                    ·
                      rfl

theorem cell23_2623884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_2623884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623884 prefixEnd_2623884 := by exact prefixLift 2623884
  have htrace : WordTrace (prefixWord ++ tailWord_2623884) baseStart_2623884 baseEnd_2623884 := by
    simpa [prefixWord, tailWord_2623884, baseEnd_2623884] using wordTrace_append hprefix tailTrace_2623884
  have hstable : (prefixWord ++ tailWord_2623884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623884).length < 2 ^ (prefixWord ++ tailWord_2623884).sum := by decide
  have hdescent : baseEnd_2623884 < baseStart_2623884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2623934 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_2623934 : Nat := 118140960795 + 2623934 * 2 ^ 59
def prefixEnd_2623934 : Nat := 4983230072969 + 3 ^ 40 * 2623934 * 2
def baseEnd_2623934 : Nat := 1347339347674642079857753

theorem tailTrace_2623934 : CollatzResearch.WordTrace tailWord_2623934 prefixEnd_2623934 1347339347674642079857753 := by
  unfold tailWord_2623934
  simp only [CollatzResearch.WordTrace]
  refine ⟨11962841909492840636834857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63801823517295150063119237 11962841909492840636834857)
  ·
    refine ⟨8972131432119630477626143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11962841909492840636834857 8972131432119630477626143)
    ·
      refine ⟨13458197148179445716439215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8972131432119630477626143 13458197148179445716439215)
      ·
        refine ⟨20187295722269168574658823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13458197148179445716439215 20187295722269168574658823)
        ·
          refine ⟨30280943583403752861988235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20187295722269168574658823 30280943583403752861988235)
          ·
            refine ⟨45421415375105629292982353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30280943583403752861988235 45421415375105629292982353)
            ·
              refine ⟨34066061531329221969736765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45421415375105629292982353 34066061531329221969736765)
              ·
                refine ⟨12774773074248458238651287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34066061531329221969736765 12774773074248458238651287)
                ·
                  refine ⟨19162159611372687357976931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12774773074248458238651287 19162159611372687357976931)
                  ·
                    refine ⟨28743239417059031036965397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19162159611372687357976931 28743239417059031036965397)
                    ·
                      refine ⟨1347339347674642079857753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28743239417059031036965397 1347339347674642079857753)
                      ·
                        rfl

theorem cell23_2623934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_2623934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2623934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2623934 prefixEnd_2623934 := by exact prefixLift 2623934
  have htrace : WordTrace (prefixWord ++ tailWord_2623934) baseStart_2623934 baseEnd_2623934 := by
    simpa [prefixWord, tailWord_2623934, baseEnd_2623934] using wordTrace_append hprefix tailTrace_2623934
  have hstable : (prefixWord ++ tailWord_2623934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2623934).length < 2 ^ (prefixWord ++ tailWord_2623934).sum := by decide
  have hdescent : baseEnd_2623934 < baseStart_2623934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2623934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624062 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_2624062 : Nat := 118140960795 + 2624062 * 2 ^ 59
def prefixEnd_2624062 : Nat := 4983230072969 + 3 ^ 40 * 2624062 * 2
def baseEnd_2624062 : Nat := 1347405073198417579057165

theorem tailTrace_2624062 : CollatzResearch.WordTrace tailWord_2624062 prefixEnd_2624062 1347405073198417579057165 := by
  unfold tailWord_2624062
  simp only [CollatzResearch.WordTrace]
  refine ⟨11963425477434875369417305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63804935879652668636892293 11963425477434875369417305)
  ·
    refine ⟨8972569108076156527062979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11963425477434875369417305 8972569108076156527062979)
    ·
      refine ⟨13458853662114234790594469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8972569108076156527062979 13458853662114234790594469)
      ·
        refine ⟨2523535061646419023236463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13458853662114234790594469 2523535061646419023236463)
        ·
          refine ⟨3785302592469628534854695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2523535061646419023236463 3785302592469628534854695)
          ·
            refine ⟨5677953888704442802282043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3785302592469628534854695 5677953888704442802282043)
            ·
              refine ⟨8516930833056664203423065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5677953888704442802282043 8516930833056664203423065)
              ·
                refine ⟨6387698124792498152567299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8516930833056664203423065 6387698124792498152567299)
                ·
                  refine ⟨9581547187188747228850949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6387698124792498152567299 9581547187188747228850949)
                  ·
                    refine ⟨1796540097597890105409553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9581547187188747228850949 1796540097597890105409553)
                    ·
                      refine ⟨1347405073198417579057165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1796540097597890105409553 1347405073198417579057165)
                      ·
                        rfl

theorem cell23_2624062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_2624062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624062 prefixEnd_2624062 := by exact prefixLift 2624062
  have htrace : WordTrace (prefixWord ++ tailWord_2624062) baseStart_2624062 baseEnd_2624062 := by
    simpa [prefixWord, tailWord_2624062, baseEnd_2624062] using wordTrace_append hprefix tailTrace_2624062
  have hstable : (prefixWord ++ tailWord_2624062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624062).length < 2 ^ (prefixWord ++ tailWord_2624062).sum := by decide
  have hdescent : baseEnd_2624062 < baseStart_2624062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624064 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 1, 7]
def baseStart_2624064 : Nat := 118140960795 + 2624064 * 2 ^ 59
def prefixEnd_2624064 : Nat := 4983230072969 + 3 ^ 40 * 2624064 * 2
def baseEnd_2624064 : Nat := 449135366719908857077385

theorem tailTrace_2624064 : CollatzResearch.WordTrace tailWord_2624064 prefixEnd_2624064 449135366719908857077385 := by
  unfold tailWord_2624064
  simp only [CollatzResearch.WordTrace]
  refine ⟨47853738382735878648455623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63804984510314504864607497 47853738382735878648455623)
  ·
    refine ⟨71780607574103817972683435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47853738382735878648455623 71780607574103817972683435)
    ·
      refine ⟨107670911361155726959025153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71780607574103817972683435 107670911361155726959025153)
      ·
        refine ⟨80753183520866795219268865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107670911361155726959025153 80753183520866795219268865)
        ·
          refine ⟨60564887640650096414451649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80753183520866795219268865 60564887640650096414451649)
          ·
            refine ⟨45423665730487572310838737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60564887640650096414451649 45423665730487572310838737)
            ·
              refine ⟨34067749297865679233129053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45423665730487572310838737 34067749297865679233129053)
              ·
                refine ⟨12775405986699629712423395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34067749297865679233129053 12775405986699629712423395)
                ·
                  refine ⟨19163108980049444568635093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12775405986699629712423395 19163108980049444568635093)
                  ·
                    refine ⟨449135366719908857077385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19163108980049444568635093 449135366719908857077385)
                    ·
                      rfl

theorem cell23_2624064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_2624064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624064 prefixEnd_2624064 := by exact prefixLift 2624064
  have htrace : WordTrace (prefixWord ++ tailWord_2624064) baseStart_2624064 baseEnd_2624064 := by
    simpa [prefixWord, tailWord_2624064, baseEnd_2624064] using wordTrace_append hprefix tailTrace_2624064
  have hstable : (prefixWord ++ tailWord_2624064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624064).length < 2 ^ (prefixWord ++ tailWord_2624064).sum := by decide
  have hdescent : baseEnd_2624064 < baseStart_2624064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624081 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 2, 5]
def baseStart_2624081 : Nat := 118140960795 + 2624081 * 2 ^ 59
def prefixEnd_2624081 : Nat := 4983230072969 + 3 ^ 40 * 2624081 * 2
def baseEnd_2624081 : Nat := 449138276443617668239859

theorem tailTrace_2624081 : CollatzResearch.WordTrace tailWord_2624081 prefixEnd_2624081 449138276443617668239859 := by
  unfold tailWord_2624081
  simp only [CollatzResearch.WordTrace]
  refine ⟨95708096806410169200280097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63805397870940112800186731 95708096806410169200280097)
  ·
    refine ⟨71781072604807626900210073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95708096806410169200280097 71781072604807626900210073)
    ·
      refine ⟨53835804453605720175157555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71781072604807626900210073 53835804453605720175157555)
      ·
        refine ⟨80753706680408580262736333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53835804453605720175157555 80753706680408580262736333)
        ·
          refine ⟨30282640005153217598526125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80753706680408580262736333 30282640005153217598526125)
          ·
            refine ⟨11355990001932456599447297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30282640005153217598526125 11355990001932456599447297)
            ·
              refine ⟨8516992501449342449585473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11355990001932456599447297 8516992501449342449585473)
              ·
                refine ⟨6387744376087006837189105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8516992501449342449585473 6387744376087006837189105)
                ·
                  refine ⟨4790808282065255127891829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6387744376087006837189105 4790808282065255127891829)
                  ·
                    refine ⟨449138276443617668239859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4790808282065255127891829 449138276443617668239859)
                    ·
                      rfl

theorem cell23_2624081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_2624081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624081 prefixEnd_2624081 := by exact prefixLift 2624081
  have htrace : WordTrace (prefixWord ++ tailWord_2624081) baseStart_2624081 baseEnd_2624081 := by
    simpa [prefixWord, tailWord_2624081, baseEnd_2624081] using wordTrace_append hprefix tailTrace_2624081
  have hstable : (prefixWord ++ tailWord_2624081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624081).length < 2 ^ (prefixWord ++ tailWord_2624081).sum := by decide
  have hdescent : baseEnd_2624081 < baseStart_2624081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624111 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 5, 4]
def baseStart_2624111 : Nat := 118140960795 + 2624111 * 2 ^ 59
def prefixEnd_2624111 : Nat := 4983230072969 + 3 ^ 40 * 2624111 * 2
def baseEnd_2624111 : Nat := 449143411250162629114813

theorem tailTrace_2624111 : CollatzResearch.WordTrace tailWord_2624111 prefixEnd_2624111 449143411250162629114813 := by
  unfold tailWord_2624111
  simp only [CollatzResearch.WordTrace]
  refine ⟨95709190996301484323872187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63806127330867656215914791 95709190996301484323872187)
  ·
    refine ⟨143563786494452226485808281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95709190996301484323872187 143563786494452226485808281)
    ·
      refine ⟨107672839870839169864356211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143563786494452226485808281 107672839870839169864356211)
      ·
        refine ⟨161509259806258754796534317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107672839870839169864356211 161509259806258754796534317)
        ·
          refine ⟨60565972427347033048700369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161509259806258754796534317 60565972427347033048700369)
          ·
            refine ⟨45424479320510274786525277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60565972427347033048700369 45424479320510274786525277)
            ·
              refine ⟨17034179745191353044946979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45424479320510274786525277 17034179745191353044946979)
              ·
                refine ⟨25551269617787029567420469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17034179745191353044946979 25551269617787029567420469)
                ·
                  refine ⟨2395431526667534021945669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25551269617787029567420469 2395431526667534021945669)
                  ·
                    refine ⟨449143411250162629114813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2395431526667534021945669 449143411250162629114813)
                    ·
                      rfl

theorem cell23_2624111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 4].length) (baseStart_2624111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624111 prefixEnd_2624111 := by exact prefixLift 2624111
  have htrace : WordTrace (prefixWord ++ tailWord_2624111) baseStart_2624111 baseEnd_2624111 := by
    simpa [prefixWord, tailWord_2624111, baseEnd_2624111] using wordTrace_append hprefix tailTrace_2624111
  have hstable : (prefixWord ++ tailWord_2624111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624111).length < 2 ^ (prefixWord ++ tailWord_2624111).sum := by decide
  have hdescent : baseEnd_2624111 < baseStart_2624111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624130 : List Nat := [3, 4, 3, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2624130 : Nat := 118140960795 + 2624130 * 2 ^ 59
def prefixEnd_2624130 : Nat := 4983230072969 + 3 ^ 40 * 2624130 * 2
def baseEnd_2624130 : Nat := 1347439989882923313006853

theorem tailTrace_2624130 : CollatzResearch.WordTrace tailWord_2624130 prefixEnd_2624130 1347439989882923313006853 := by
  unfold tailWord_2624130
  simp only [CollatzResearch.WordTrace]
  refine ⟨23927470995808162642203461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63806589322155100379209229 23927470995808162642203461)
  ·
    refine ⟨4486400811714030495413149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23927470995808162642203461 4486400811714030495413149)
    ·
      refine ⟨1682400304392761435779931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4486400811714030495413149 1682400304392761435779931)
      ·
        refine ⟨2523600456589142153669897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1682400304392761435779931 2523600456589142153669897)
        ·
          refine ⟨1892700342441856615252423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2523600456589142153669897 1892700342441856615252423)
          ·
            refine ⟨2839050513662784922878635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892700342441856615252423 2839050513662784922878635)
            ·
              refine ⟨4258575770494177384317953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839050513662784922878635 4258575770494177384317953)
              ·
                refine ⟨3193931827870633038238465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4258575770494177384317953 3193931827870633038238465)
                ·
                  refine ⟨2395448870902974778678849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3193931827870633038238465 2395448870902974778678849)
                  ·
                    refine ⟨1796586653177231084009137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2395448870902974778678849 1796586653177231084009137)
                    ·
                      refine ⟨1347439989882923313006853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1796586653177231084009137 1347439989882923313006853)
                      ·
                        rfl

theorem cell23_2624130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2624130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624130 prefixEnd_2624130 := by exact prefixLift 2624130
  have htrace : WordTrace (prefixWord ++ tailWord_2624130) baseStart_2624130 baseEnd_2624130 := by
    simpa [prefixWord, tailWord_2624130, baseEnd_2624130] using wordTrace_append hprefix tailTrace_2624130
  have hstable : (prefixWord ++ tailWord_2624130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624130).length < 2 ^ (prefixWord ++ tailWord_2624130).sum := by decide
  have hdescent : baseEnd_2624130 < baseStart_2624130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624188 : List Nat := [2, 2, 2, 3, 1, 1, 1, 5, 1, 5]
def baseStart_2624188 : Nat := 118140960795 + 2624188 * 2 ^ 59
def prefixEnd_2624188 : Nat := 4983230072969 + 3 ^ 40 * 2624188 * 2
def baseEnd_2624188 : Nat := 449156590586961362027195

theorem tailTrace_2624188 : CollatzResearch.WordTrace tailWord_2624188 prefixEnd_2624188 449156590586961362027195 := by
  unfold tailWord_2624188
  simp only [CollatzResearch.WordTrace]
  refine ⟨47855999708511263237212609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63807999611348350982950145 47855999708511263237212609)
  ·
    refine ⟨35891999781383447427909457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47855999708511263237212609 35891999781383447427909457)
    ·
      refine ⟨26918999836037585570932093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35891999781383447427909457 26918999836037585570932093)
      ·
        refine ⟨10094624938514094589099535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26918999836037585570932093 10094624938514094589099535)
        ·
          refine ⟨15141937407771141883649303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10094624938514094589099535 15141937407771141883649303)
          ·
            refine ⟨22712906111656712825473955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15141937407771141883649303 22712906111656712825473955)
            ·
              refine ⟨34069359167485069238210933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22712906111656712825473955 34069359167485069238210933)
              ·
                refine ⟨3194002421951725241082275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34069359167485069238210933 3194002421951725241082275)
                ·
                  refine ⟨4791003632927587861623413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194002421951725241082275 4791003632927587861623413)
                  ·
                    refine ⟨449156590586961362027195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4791003632927587861623413 449156590586961362027195)
                    ·
                      rfl

theorem cell23_2624188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_2624188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624188 prefixEnd_2624188 := by exact prefixLift 2624188
  have htrace : WordTrace (prefixWord ++ tailWord_2624188) baseStart_2624188 baseEnd_2624188 := by
    simpa [prefixWord, tailWord_2624188, baseEnd_2624188] using wordTrace_append hprefix tailTrace_2624188
  have hstable : (prefixWord ++ tailWord_2624188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624188).length < 2 ^ (prefixWord ++ tailWord_2624188).sum := by decide
  have hdescent : baseEnd_2624188 < baseStart_2624188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624202 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_2624202 : Nat := 118140960795 + 2624202 * 2 ^ 59
def prefixEnd_2624202 : Nat := 4983230072969 + 3 ^ 40 * 2624202 * 2
def baseEnd_2624202 : Nat := 1347476960490047031306521

theorem tailTrace_2624202 : CollatzResearch.WordTrace tailWord_2624202 prefixEnd_2624202 1347476960490047031306521 := by
  unfold tailWord_2624202
  simp only [CollatzResearch.WordTrace]
  refine ⟨23928127509742951716358715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63808340025981204576956573 23928127509742951716358715)
  ·
    refine ⟨35892191264614427574538073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23928127509742951716358715 35892191264614427574538073)
    ·
      refine ⟨26919143448460820680903555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35892191264614427574538073 26919143448460820680903555)
      ·
        refine ⟨40378715172691231021355333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26919143448460820680903555 40378715172691231021355333)
        ·
          refine ⟨7571009094879605816504125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40378715172691231021355333 7571009094879605816504125)
          ·
            refine ⟨2839128410579852181189047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7571009094879605816504125 2839128410579852181189047)
            ·
              refine ⟨4258692615869778271783571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839128410579852181189047 4258692615869778271783571)
              ·
                refine ⟨6388038923804667407675357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258692615869778271783571 6388038923804667407675357)
                ·
                  refine ⟨2395514596426750277878259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6388038923804667407675357 2395514596426750277878259)
                  ·
                    refine ⟨3593271894640125416817389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2395514596426750277878259 3593271894640125416817389)
                    ·
                      refine ⟨1347476960490047031306521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3593271894640125416817389 1347476960490047031306521)
                      ·
                        rfl

theorem cell23_2624202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_2624202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624202 prefixEnd_2624202 := by exact prefixLift 2624202
  have htrace : WordTrace (prefixWord ++ tailWord_2624202) baseStart_2624202 baseEnd_2624202 := by
    simpa [prefixWord, tailWord_2624202, baseEnd_2624202] using wordTrace_append hprefix tailTrace_2624202
  have hstable : (prefixWord ++ tailWord_2624202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624202).length < 2 ^ (prefixWord ++ tailWord_2624202).sum := by decide
  have hdescent : baseEnd_2624202 < baseStart_2624202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624225 : List Nat := [1, 2, 3, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_2624225 : Nat := 118140960795 + 2624225 * 2 ^ 59
def prefixEnd_2624225 : Nat := 4983230072969 + 3 ^ 40 * 2624225 * 2
def baseEnd_2624225 : Nat := 1347488770545100441318915

theorem tailTrace_2624225 : CollatzResearch.WordTrace tailWord_2624225 prefixEnd_2624225 1347488770545100441318915 := by
  unfold tailWord_2624225
  simp only [CollatzResearch.WordTrace]
  refine ⟨95713348917888481793522129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63808899278592321195681419 95713348917888481793522129)
  ·
    refine ⟨71785011688416361345141597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95713348917888481793522129 71785011688416361345141597)
    ·
      refine ⟨26919379383156135504428099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71785011688416361345141597 26919379383156135504428099)
      ·
        refine ⟨40379069074734203256642149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26919379383156135504428099 40379069074734203256642149)
        ·
          refine ⟨7571075451512663110620403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40379069074734203256642149 7571075451512663110620403)
          ·
            refine ⟨11356613177268994665930605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7571075451512663110620403 11356613177268994665930605)
            ·
              refine ⟨4258729941475872999723977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11356613177268994665930605 4258729941475872999723977)
              ·
                refine ⟨3194047456106904749792983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4258729941475872999723977 3194047456106904749792983)
                ·
                  refine ⟨4791071184160357124689475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194047456106904749792983 4791071184160357124689475)
                  ·
                    refine ⟨7186606776240535687034213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4791071184160357124689475 7186606776240535687034213)
                    ·
                      refine ⟨1347488770545100441318915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7186606776240535687034213 1347488770545100441318915)
                      ·
                        rfl

theorem cell23_2624225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_2624225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624225 prefixEnd_2624225 := by exact prefixLift 2624225
  have htrace : WordTrace (prefixWord ++ tailWord_2624225) baseStart_2624225 baseEnd_2624225 := by
    simpa [prefixWord, tailWord_2624225, baseEnd_2624225] using wordTrace_append hprefix tailTrace_2624225
  have hstable : (prefixWord ++ tailWord_2624225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624225).length < 2 ^ (prefixWord ++ tailWord_2624225).sum := by decide
  have hdescent : baseEnd_2624225 < baseStart_2624225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624238 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_2624238 : Nat := 118140960795 + 2624238 * 2 ^ 59
def prefixEnd_2624238 : Nat := 4983230072969 + 3 ^ 40 * 2624238 * 2
def baseEnd_2624238 : Nat := 1347495445793608890456355

theorem tailTrace_2624238 : CollatzResearch.WordTrace tailWord_2624238 prefixEnd_2624238 1347495445793608890456355 := by
  unfold tailWord_2624238
  simp only [CollatzResearch.WordTrace]
  refine ⟨11964227883355173126718171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63809215377894256675830245 11964227883355173126718171)
  ·
    refine ⟨17946341825032759690077257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11964227883355173126718171 17946341825032759690077257)
    ·
      refine ⟨13459756368774569767557943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17946341825032759690077257 13459756368774569767557943)
      ·
        refine ⟨20189634553161854651336915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13459756368774569767557943 20189634553161854651336915)
        ·
          refine ⟨30284451829742781977005373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20189634553161854651336915 30284451829742781977005373)
          ·
            refine ⟨11356669436153543241377015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30284451829742781977005373 11356669436153543241377015)
            ·
              refine ⟨17035004154230314862065523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11356669436153543241377015 17035004154230314862065523)
              ·
                refine ⟨25552506231345472293098285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17035004154230314862065523 25552506231345472293098285)
                ·
                  refine ⟨9582189836754552109911857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25552506231345472293098285 9582189836754552109911857)
                  ·
                    refine ⟨7186642377565914082433893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9582189836754552109911857 7186642377565914082433893)
                    ·
                      refine ⟨1347495445793608890456355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7186642377565914082433893 1347495445793608890456355)
                      ·
                        rfl

theorem cell23_2624238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_2624238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624238 prefixEnd_2624238 := by exact prefixLift 2624238
  have htrace : WordTrace (prefixWord ++ tailWord_2624238) baseStart_2624238 baseEnd_2624238 := by
    simpa [prefixWord, tailWord_2624238, baseEnd_2624238] using wordTrace_append hprefix tailTrace_2624238
  have hstable : (prefixWord ++ tailWord_2624238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624238).length < 2 ^ (prefixWord ++ tailWord_2624238).sum := by decide
  have hdescent : baseEnd_2624238 < baseStart_2624238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624242 : List Nat := [3, 2, 1, 3, 1, 3, 3, 1, 1, 1, 4]
def baseStart_2624242 : Nat := 118140960795 + 2624242 * 2 ^ 59
def prefixEnd_2624242 : Nat := 4983230072969 + 3 ^ 40 * 2624242 * 2
def baseEnd_2624242 : Nat := 1347497499716226874806337

theorem tailTrace_2624242 : CollatzResearch.WordTrace tailWord_2624242 prefixEnd_2624242 1347497499716226874806337 := by
  unfold tailWord_2624242
  simp only [CollatzResearch.WordTrace]
  refine ⟨23928492239706723424222745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63809312639217929131260653 23928492239706723424222745)
  ·
    refine ⟨17946369179780042568167059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23928492239706723424222745 17946369179780042568167059)
    ·
      refine ⟨26919553769670063852250589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17946369179780042568167059 26919553769670063852250589)
      ·
        refine ⟨10094832663626273944593971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26919553769670063852250589 10094832663626273944593971)
        ·
          refine ⟨15142248995439410916890957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10094832663626273944593971 15142248995439410916890957)
          ·
            refine ⟨5678343373289779093834109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15142248995439410916890957 5678343373289779093834109)
            ·
              refine ⟨2129378764983667160187791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5678343373289779093834109 2129378764983667160187791)
              ·
                refine ⟨3194068147475500740281687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2129378764983667160187791 3194068147475500740281687)
                ·
                  refine ⟨4791102221213251110422531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194068147475500740281687 4791102221213251110422531)
                  ·
                    refine ⟨7186653331819876665633797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4791102221213251110422531 7186653331819876665633797)
                    ·
                      refine ⟨1347497499716226874806337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7186653331819876665633797 1347497499716226874806337)
                      ·
                        rfl

theorem cell23_2624242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_2624242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624242 prefixEnd_2624242 := by exact prefixLift 2624242
  have htrace : WordTrace (prefixWord ++ tailWord_2624242) baseStart_2624242 baseEnd_2624242 := by
    simpa [prefixWord, tailWord_2624242, baseEnd_2624242] using wordTrace_append hprefix tailTrace_2624242
  have hstable : (prefixWord ++ tailWord_2624242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624242).length < 2 ^ (prefixWord ++ tailWord_2624242).sum := by decide
  have hdescent : baseEnd_2624242 < baseStart_2624242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624275 : List Nat := [1, 1, 1, 2, 1, 3, 3, 5, 2, 1, 3]
def baseStart_2624275 : Nat := 118140960795 + 2624275 * 2 ^ 59
def prefixEnd_2624275 : Nat := 4983230072969 + 3 ^ 40 * 2624275 * 2
def baseEnd_2624275 : Nat := 1347514444577825245693685

theorem tailTrace_2624275 : CollatzResearch.WordTrace tailWord_2624275 prefixEnd_2624275 1347514444577825245693685 := by
  unfold tailWord_2624275
  simp only [CollatzResearch.WordTrace]
  refine ⟨95715172567707340332842279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63810115045138226888561519 95715172567707340332842279)
  ·
    refine ⟨143572758851561010499263419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95715172567707340332842279 143572758851561010499263419)
    ·
      refine ⟨215359138277341515748895129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143572758851561010499263419 215359138277341515748895129)
      ·
        refine ⟨161519353708006136811671347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215359138277341515748895129 161519353708006136811671347)
        ·
          refine ⟨242279030562009205217507021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161519353708006136811671347 242279030562009205217507021)
          ·
            refine ⟨90854636460753451956565133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242279030562009205217507021 90854636460753451956565133)
            ·
              refine ⟨34070488672782544483711925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90854636460753451956565133 34070488672782544483711925)
              ·
                refine ⟨3194108313073363545347993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34070488672782544483711925 3194108313073363545347993)
                ·
                  refine ⟨2395581234805022659010995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3194108313073363545347993 2395581234805022659010995)
                  ·
                    refine ⟨3593371852207533988516493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2395581234805022659010995 3593371852207533988516493)
                    ·
                      refine ⟨1347514444577825245693685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3593371852207533988516493 1347514444577825245693685)
                      ·
                        rfl

theorem cell23_2624275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 1, 3].length) (baseStart_2624275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624275 prefixEnd_2624275 := by exact prefixLift 2624275
  have htrace : WordTrace (prefixWord ++ tailWord_2624275) baseStart_2624275 baseEnd_2624275 := by
    simpa [prefixWord, tailWord_2624275, baseEnd_2624275] using wordTrace_append hprefix tailTrace_2624275
  have hstable : (prefixWord ++ tailWord_2624275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624275).length < 2 ^ (prefixWord ++ tailWord_2624275).sum := by decide
  have hdescent : baseEnd_2624275 < baseStart_2624275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624291 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 3, 8]
def baseStart_2624291 : Nat := 118140960795 + 2624291 * 2 ^ 59
def prefixEnd_2624291 : Nat := 4983230072969 + 3 ^ 40 * 2624291 * 2
def baseEnd_2624291 : Nat := 449174220089432394364537

theorem tailTrace_2624291 : CollatzResearch.WordTrace tailWord_2624291 prefixEnd_2624291 449174220089432394364537 := by
  unfold tailWord_2624291
  simp only [CollatzResearch.WordTrace]
  refine ⟨95715756135649375065424727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63810504090432916710283151 95715756135649375065424727)
  ·
    refine ⟨143573634203474062598137091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95715756135649375065424727 143573634203474062598137091)
    ·
      refine ⟨215360451305211093897205637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143573634203474062598137091 215360451305211093897205637)
      ·
        refine ⟨40380084619727080105726057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215360451305211093897205637 40380084619727080105726057)
        ·
          refine ⟨30285063464795310079294543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40380084619727080105726057 30285063464795310079294543)
          ·
            refine ⟨45427595197192965118941815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30285063464795310079294543 45427595197192965118941815)
            ·
              refine ⟨68141392795789447678412723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45427595197192965118941815 68141392795789447678412723)
              ·
                refine ⟨102212089193684171517619085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68141392795789447678412723 102212089193684171517619085)
                ·
                  refine ⟨38329533447631564319107157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102212089193684171517619085 38329533447631564319107157)
                  ·
                    refine ⟨449174220089432394364537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38329533447631564319107157 449174220089432394364537)
                    ·
                      rfl

theorem cell23_2624291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 8].length) (baseStart_2624291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624291 prefixEnd_2624291 := by exact prefixLift 2624291
  have htrace : WordTrace (prefixWord ++ tailWord_2624291) baseStart_2624291 baseEnd_2624291 := by
    simpa [prefixWord, tailWord_2624291, baseEnd_2624291] using wordTrace_append hprefix tailTrace_2624291
  have hstable : (prefixWord ++ tailWord_2624291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624291).length < 2 ^ (prefixWord ++ tailWord_2624291).sum := by decide
  have hdescent : baseEnd_2624291 < baseStart_2624291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624309 : List Nat := [1, 3, 3, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_2624309 : Nat := 118140960795 + 2624309 * 2 ^ 59
def prefixEnd_2624309 : Nat := 4983230072969 + 3 ^ 40 * 2624309 * 2
def baseEnd_2624309 : Nat := 1347531902920078112668529

theorem tailTrace_2624309 : CollatzResearch.WordTrace tailWord_2624309 prefixEnd_2624309 1347531902920078112668529 := by
  unfold tailWord_2624309
  simp only [CollatzResearch.WordTrace]
  refine ⟨95716412649584164139579981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63810941766389442759719987 95716412649584164139579981)
  ·
    refine ⟨35893654743594061552342493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95716412649584164139579981 35893654743594061552342493)
    ·
      refine ⟨13460120528847773082128435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35893654743594061552342493 13460120528847773082128435)
      ·
        refine ⟨20190180793271659623192653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13460120528847773082128435 20190180793271659623192653)
        ·
          refine ⟨7571317797476872358697245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20190180793271659623192653 7571317797476872358697245)
          ·
            refine ⟨2839244174053827134511467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7571317797476872358697245 2839244174053827134511467)
            ·
              refine ⟨4258866261080740701767201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839244174053827134511467 4258866261080740701767201)
              ·
                refine ⟨3194149695810555526325401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4258866261080740701767201 3194149695810555526325401)
                ·
                  refine ⟨2395612271857916644744051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3194149695810555526325401 2395612271857916644744051)
                  ·
                    refine ⟨3593418407786874967116077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2395612271857916644744051 3593418407786874967116077)
                    ·
                      refine ⟨1347531902920078112668529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3593418407786874967116077 1347531902920078112668529)
                      ·
                        rfl

theorem cell23_2624309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_2624309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624309 prefixEnd_2624309 := by exact prefixLift 2624309
  have htrace : WordTrace (prefixWord ++ tailWord_2624309) baseStart_2624309 baseEnd_2624309 := by
    simpa [prefixWord, tailWord_2624309, baseEnd_2624309] using wordTrace_append hprefix tailTrace_2624309
  have hstable : (prefixWord ++ tailWord_2624309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624309).length < 2 ^ (prefixWord ++ tailWord_2624309).sum := by decide
  have hdescent : baseEnd_2624309 < baseStart_2624309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624326 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2624326 : Nat := 118140960795 + 2624326 * 2 ^ 59
def prefixEnd_2624326 : Nat := 4983230072969 + 3 ^ 40 * 2624326 * 2
def baseEnd_2624326 : Nat := 1347540632091204546155951

theorem tailTrace_2624326 : CollatzResearch.WordTrace tailWord_2624326 prefixEnd_2624326 1347540632091204546155951 := by
  unfold tailWord_2624326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2991157271578830501342151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63811355127015050695299221 2991157271578830501342151)
  ·
    refine ⟨4486735907368245752013227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2991157271578830501342151 4486735907368245752013227)
    ·
      refine ⟨6730103861052368628019841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4486735907368245752013227 6730103861052368628019841)
      ·
        refine ⟨5047577895789276471014881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6730103861052368628019841 5047577895789276471014881)
        ·
          refine ⟨3785683421841957353261161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5047577895789276471014881 3785683421841957353261161)
          ·
            refine ⟨2839262566381468014945871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3785683421841957353261161 2839262566381468014945871)
            ·
              refine ⟨4258893849572202022418807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839262566381468014945871 4258893849572202022418807)
              ·
                refine ⟨6388340774358303033628211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258893849572202022418807 6388340774358303033628211)
                ·
                  refine ⟨9582511161537454550442317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6388340774358303033628211 9582511161537454550442317)
                  ·
                    refine ⟨3593441685576545456415869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9582511161537454550442317 3593441685576545456415869)
                    ·
                      refine ⟨1347540632091204546155951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3593441685576545456415869 1347540632091204546155951)
                      ·
                        rfl

theorem cell23_2624326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2624326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624326 prefixEnd_2624326 := by exact prefixLift 2624326
  have htrace : WordTrace (prefixWord ++ tailWord_2624326) baseStart_2624326 baseEnd_2624326 := by
    simpa [prefixWord, tailWord_2624326, baseEnd_2624326] using wordTrace_append hprefix tailTrace_2624326
  have hstable : (prefixWord ++ tailWord_2624326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624326).length < 2 ^ (prefixWord ++ tailWord_2624326).sum := by decide
  have hdescent : baseEnd_2624326 < baseStart_2624326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624328 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_2624328 : Nat := 118140960795 + 2624328 * 2 ^ 59
def prefixEnd_2624328 : Nat := 4983230072969 + 3 ^ 40 * 2624328 * 2
def baseEnd_2624328 : Nat := 1347541659052513538330941

theorem tailTrace_2624328 : CollatzResearch.WordTrace tailWord_2624328 prefixEnd_2624328 1347541659052513538330941 := by
  unfold tailWord_2624328
  simp only [CollatzResearch.WordTrace]
  refine ⟨47858552818257665192260819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63811403757676886923014425 47858552818257665192260819)
  ·
    refine ⟨71787829227386497788391229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47858552818257665192260819 71787829227386497788391229)
    ·
      refine ⟨26920435960269936670646711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71787829227386497788391229 26920435960269936670646711)
      ·
        refine ⟨40380653940404905005970067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26920435960269936670646711 40380653940404905005970067)
        ·
          refine ⟨60570980910607357508955101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40380653940404905005970067 60570980910607357508955101)
          ·
            refine ⟨22714117841477759065858163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60570980910607357508955101 22714117841477759065858163)
            ·
              refine ⟨34071176762216638598787245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22714117841477759065858163 34071176762216638598787245)
              ·
                refine ⟨12776691285831239474545217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34071176762216638598787245 12776691285831239474545217)
                ·
                  refine ⟨9582518464373429605908913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12776691285831239474545217 9582518464373429605908913)
                  ·
                    refine ⟨7186888848280072204431685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9582518464373429605908913 7186888848280072204431685)
                    ·
                      refine ⟨1347541659052513538330941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7186888848280072204431685 1347541659052513538330941)
                      ·
                        rfl

theorem cell23_2624328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_2624328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624328 prefixEnd_2624328 := by exact prefixLift 2624328
  have htrace : WordTrace (prefixWord ++ tailWord_2624328) baseStart_2624328 baseEnd_2624328 := by
    simpa [prefixWord, tailWord_2624328, baseEnd_2624328] using wordTrace_append hprefix tailTrace_2624328
  have hstable : (prefixWord ++ tailWord_2624328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624328).length < 2 ^ (prefixWord ++ tailWord_2624328).sum := by decide
  have hdescent : baseEnd_2624328 < baseStart_2624328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624331 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 9]
def baseStart_2624331 : Nat := 118140960795 + 2624331 * 2 ^ 59
def prefixEnd_2624331 : Nat := 4983230072969 + 3 ^ 40 * 2624331 * 2
def baseEnd_2624331 : Nat := 1347543199494477026593427

theorem tailTrace_2624331 : CollatzResearch.WordTrace tailWord_2624331 prefixEnd_2624331 1347543199494477026593427 := by
  unfold tailWord_2624331
  simp only [CollatzResearch.WordTrace]
  refine ⟨95717215055504461896880847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63811476703669641264587231 95717215055504461896880847)
  ·
    refine ⟨143575822583256692845321271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95717215055504461896880847 143575822583256692845321271)
    ·
      refine ⟨215363733874885039267981907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143575822583256692845321271 215363733874885039267981907)
      ·
        refine ⟨323045600812327558901972861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215363733874885039267981907 323045600812327558901972861)
        ·
          refine ⟨121142100304622834588239823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323045600812327558901972861 121142100304622834588239823)
          ·
            refine ⟨181713150456934251882359735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121142100304622834588239823 181713150456934251882359735)
            ·
              refine ⟨272569725685401377823539603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181713150456934251882359735 272569725685401377823539603)
              ·
                refine ⟨408854588528102066735309405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272569725685401377823539603 408854588528102066735309405)
                ·
                  refine ⟨153320470698038275025741027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408854588528102066735309405 153320470698038275025741027)
                  ·
                    refine ⟨229980706047057412538611541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 153320470698038275025741027 229980706047057412538611541)
                    ·
                      refine ⟨1347543199494477026593427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 229980706047057412538611541 1347543199494477026593427)
                      ·
                        rfl

theorem cell23_2624331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_2624331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624331 prefixEnd_2624331 := by exact prefixLift 2624331
  have htrace : WordTrace (prefixWord ++ tailWord_2624331) baseStart_2624331 baseEnd_2624331 := by
    simpa [prefixWord, tailWord_2624331, baseEnd_2624331] using wordTrace_append hprefix tailTrace_2624331
  have hstable : (prefixWord ++ tailWord_2624331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624331).length < 2 ^ (prefixWord ++ tailWord_2624331).sum := by decide
  have hdescent : baseEnd_2624331 < baseStart_2624331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624332 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 1, 4, 2]
def baseStart_2624332 : Nat := 118140960795 + 2624332 * 2 ^ 59
def prefixEnd_2624332 : Nat := 4983230072969 + 3 ^ 40 * 2624332 * 2
def baseEnd_2624332 : Nat := 1347543712975131522680923

theorem tailTrace_2624332 : CollatzResearch.WordTrace tailWord_2624332 prefixEnd_2624332 1347543712975131522680923 := by
  unfold tailWord_2624332
  simp only [CollatzResearch.WordTrace]
  refine ⟨47858625764250419533833625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63811501019000559378444833 47858625764250419533833625)
  ·
    refine ⟨35893969323187814650375219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47858625764250419533833625 35893969323187814650375219)
    ·
      refine ⟨53840953984781721975562829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35893969323187814650375219 53840953984781721975562829)
      ·
        refine ⟨20190357744293145740836061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53840953984781721975562829 20190357744293145740836061)
        ·
          refine ⟨7571384154109929652813523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20190357744293145740836061 7571384154109929652813523)
          ·
            refine ⟨11357076231164894479220285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7571384154109929652813523 11357076231164894479220285)
            ·
              refine ⟨4258903586686835429707607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11357076231164894479220285 4258903586686835429707607)
              ·
                refine ⟨6388355380030253144561411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258903586686835429707607 6388355380030253144561411)
                ·
                  refine ⟨9582533070045379716842117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6388355380030253144561411 9582533070045379716842117)
                  ·
                    refine ⟨1796724950633508696907897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9582533070045379716842117 1796724950633508696907897)
                    ·
                      refine ⟨1347543712975131522680923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1796724950633508696907897 1347543712975131522680923)
                      ·
                        rfl

theorem cell23_2624332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_2624332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624332 prefixEnd_2624332 := by exact prefixLift 2624332
  have htrace : WordTrace (prefixWord ++ tailWord_2624332) baseStart_2624332 baseEnd_2624332 := by
    simpa [prefixWord, tailWord_2624332, baseEnd_2624332] using wordTrace_append hprefix tailTrace_2624332
  have hstable : (prefixWord ++ tailWord_2624332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624332).length < 2 ^ (prefixWord ++ tailWord_2624332).sum := by decide
  have hdescent : baseEnd_2624332 < baseStart_2624332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624338 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 7]
def baseStart_2624338 : Nat := 118140960795 + 2624338 * 2 ^ 59
def prefixEnd_2624338 : Nat := 4983230072969 + 3 ^ 40 * 2624338 * 2
def baseEnd_2624338 : Nat := 149727421539895388800655

theorem tailTrace_2624338 : CollatzResearch.WordTrace tailWord_2624338 prefixEnd_2624338 149727421539895388800655 := by
  unfold tailWord_2624338
  simp only [CollatzResearch.WordTrace]
  refine ⟨23929367591619775523096417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63811646910986068061590445 23929367591619775523096417)
  ·
    refine ⟨17947025693714831642322313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23929367591619775523096417 17947025693714831642322313)
    ·
      refine ⟨13460269270286123731741735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17947025693714831642322313 13460269270286123731741735)
      ·
        refine ⟨20190403905429185597612603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13460269270286123731741735 20190403905429185597612603)
        ·
          refine ⟨30285605858143778396418905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20190403905429185597612603 30285605858143778396418905)
          ·
            refine ⟨22714204393607833797314179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30285605858143778396418905 22714204393607833797314179)
            ·
              refine ⟨34071306590411750695971269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22714204393607833797314179 34071306590411750695971269)
              ·
                refine ⟨6388369985702203255494613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34071306590411750695971269 6388369985702203255494613)
                ·
                  refine ⟨149727421539895388800655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6388369985702203255494613 149727421539895388800655)
                  ·
                    rfl

theorem cell23_2624338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_2624338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624338 prefixEnd_2624338 := by exact prefixLift 2624338
  have htrace : WordTrace (prefixWord ++ tailWord_2624338) baseStart_2624338 baseEnd_2624338 := by
    simpa [prefixWord, tailWord_2624338, baseEnd_2624338] using wordTrace_append hprefix tailTrace_2624338
  have hstable : (prefixWord ++ tailWord_2624338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624338).length < 2 ^ (prefixWord ++ tailWord_2624338).sum := by decide
  have hdescent : baseEnd_2624338 < baseStart_2624338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624368 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 4, 5]
def baseStart_2624368 : Nat := 118140960795 + 2624368 * 2 ^ 59
def prefixEnd_2624368 : Nat := 4983230072969 + 3 ^ 40 * 2624368 * 2
def baseEnd_2624368 : Nat := 449187399426231127276919

theorem tailTrace_2624368 : CollatzResearch.WordTrace tailWord_2624368 prefixEnd_2624368 449187399426231127276919 := by
  unfold tailWord_2624368
  simp only [CollatzResearch.WordTrace]
  refine ⟨47859282278185208607988879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63812376370913611477318505 47859282278185208607988879)
  ·
    refine ⟨71788923417277812911983319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47859282278185208607988879 71788923417277812911983319)
    ·
      refine ⟨107683385125916719367974979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71788923417277812911983319 107683385125916719367974979)
      ·
        refine ⟨161525077688875079051962469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107683385125916719367974979 161525077688875079051962469)
        ·
          refine ⟨30285952066664077322242963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161525077688875079051962469 30285952066664077322242963)
          ·
            refine ⟨45428928099996115983364445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30285952066664077322242963 45428928099996115983364445)
            ·
              refine ⟨17035848037498543493761667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45428928099996115983364445 17035848037498543493761667)
              ·
                refine ⟨25553772056247815240642501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17035848037498543493761667 25553772056247815240642501)
                ·
                  refine ⟨4791332260546465357620469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25553772056247815240642501 4791332260546465357620469)
                  ·
                    refine ⟨449187399426231127276919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4791332260546465357620469 449187399426231127276919)
                    ·
                      rfl

theorem cell23_2624368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4, 5].length) (baseStart_2624368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624368 prefixEnd_2624368 := by exact prefixLift 2624368
  have htrace : WordTrace (prefixWord ++ tailWord_2624368) baseStart_2624368 baseEnd_2624368 := by
    simpa [prefixWord, tailWord_2624368, baseEnd_2624368] using wordTrace_append hprefix tailTrace_2624368
  have hstable : (prefixWord ++ tailWord_2624368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624368).length < 2 ^ (prefixWord ++ tailWord_2624368).sum := by decide
  have hdescent : baseEnd_2624368 < baseStart_2624368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624405 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_2624405 : Nat := 118140960795 + 2624405 * 2 ^ 59
def prefixEnd_2624405 : Nat := 4983230072969 + 3 ^ 40 * 2624405 * 2
def baseEnd_2624405 : Nat := 1347581197062909737068087

theorem tailTrace_2624405 : CollatzResearch.WordTrace tailWord_2624405 prefixEnd_2624405 1347581197062909737068087 := by
  unfold tailWord_2624405
  simp only [CollatzResearch.WordTrace]
  refine ⟨95719914057236372535074669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63813276038157581690049779 95719914057236372535074669)
  ·
    refine ⟨35894967771463639700653001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95719914057236372535074669 35894967771463639700653001)
    ·
      refine ⟨26921225828597729775489751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35894967771463639700653001 26921225828597729775489751)
      ·
        refine ⟨40381838742896594663234627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26921225828597729775489751 40381838742896594663234627)
        ·
          refine ⟨60572758114344891994851941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40381838742896594663234627 60572758114344891994851941)
          ·
            refine ⟨11357392146439667249034739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60572758114344891994851941 11357392146439667249034739)
            ·
              refine ⟨17036088219659500873552109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11357392146439667249034739 17036088219659500873552109)
              ·
                refine ⟨6388533082372312827582041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17036088219659500873552109 6388533082372312827582041)
                ·
                  refine ⟨4791399811779234620686531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6388533082372312827582041 4791399811779234620686531)
                  ·
                    refine ⟨7187099717668851931029797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4791399811779234620686531 7187099717668851931029797)
                    ·
                      refine ⟨1347581197062909737068087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7187099717668851931029797 1347581197062909737068087)
                      ·
                        rfl

theorem cell23_2624405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_2624405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624405 prefixEnd_2624405 := by exact prefixLift 2624405
  have htrace : WordTrace (prefixWord ++ tailWord_2624405) baseStart_2624405 baseEnd_2624405 := by
    simpa [prefixWord, tailWord_2624405, baseEnd_2624405] using wordTrace_append hprefix tailTrace_2624405
  have hstable : (prefixWord ++ tailWord_2624405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624405).length < 2 ^ (prefixWord ++ tailWord_2624405).sum := by decide
  have hdescent : baseEnd_2624405 < baseStart_2624405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624425 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 2, 2, 3]
def baseStart_2624425 : Nat := 118140960795 + 2624425 * 2 ^ 59
def prefixEnd_2624425 : Nat := 4983230072969 + 3 ^ 40 * 2624425 * 2
def baseEnd_2624425 : Nat := 1347591466675999658817995

theorem tailTrace_2624425 : CollatzResearch.WordTrace tailWord_2624425 prefixEnd_2624425 1347591466675999658817995 := by
  unfold tailWord_2624425
  simp only [CollatzResearch.WordTrace]
  refine ⟨95720643517163915950802729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63813762344775943967201819 95720643517163915950802729)
  ·
    refine ⟨71790482637872936963102047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95720643517163915950802729 71790482637872936963102047)
    ·
      refine ⟨107685723956809405444653071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71790482637872936963102047 107685723956809405444653071)
      ·
        refine ⟨161528585935214108166979607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107685723956809405444653071 161528585935214108166979607)
        ·
          refine ⟨242292878902821162250469411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161528585935214108166979607 242292878902821162250469411)
          ·
            refine ⟨363439318354231743375704117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242292878902821162250469411 363439318354231743375704117)
            ·
              refine ⟨34072436095709225941472261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 363439318354231743375704117 34072436095709225941472261)
              ·
                refine ⟨6388581767945479864026049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34072436095709225941472261 6388581767945479864026049)
                ·
                  refine ⟨4791436325959109898019537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6388581767945479864026049 4791436325959109898019537)
                  ·
                    refine ⟨3593577244469332423514653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4791436325959109898019537 3593577244469332423514653)
                    ·
                      refine ⟨1347591466675999658817995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3593577244469332423514653 1347591466675999658817995)
                      ·
                        rfl

theorem cell23_2624425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 2, 3].length) (baseStart_2624425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624425 prefixEnd_2624425 := by exact prefixLift 2624425
  have htrace : WordTrace (prefixWord ++ tailWord_2624425) baseStart_2624425 baseEnd_2624425 := by
    simpa [prefixWord, tailWord_2624425, baseEnd_2624425] using wordTrace_append hprefix tailTrace_2624425
  have hstable : (prefixWord ++ tailWord_2624425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624425).length < 2 ^ (prefixWord ++ tailWord_2624425).sum := by decide
  have hdescent : baseEnd_2624425 < baseStart_2624425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624466 : List Nat := [3, 2, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_2624466 : Nat := 118140960795 + 2624466 * 2 ^ 59
def prefixEnd_2624466 : Nat := 4983230072969 + 3 ^ 40 * 2624466 * 2
def baseEnd_2624466 : Nat := 449204173127611332801769

theorem tailTrace_2624466 : CollatzResearch.WordTrace tailWord_2624466 prefixEnd_2624466 449204173127611332801769 := by
  unfold tailWord_2624466
  simp only [CollatzResearch.WordTrace]
  refine ⟨23930534727503844988261313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63814759273343586635363501 23930534727503844988261313)
  ·
    refine ⟨17947901045627883741195985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23930534727503844988261313 17947901045627883741195985)
    ·
      refine ⟨13460925784220912805896989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17947901045627883741195985 13460925784220912805896989)
      ·
        refine ⟨5047847169082842302211371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13460925784220912805896989 5047847169082842302211371)
        ·
          refine ⟨7571770753624263453317057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5047847169082842302211371 7571770753624263453317057)
          ·
            refine ⟨5678828065218197589987793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7571770753624263453317057 5678828065218197589987793)
            ·
              refine ⟨4259121048913648192490845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5678828065218197589987793 4259121048913648192490845)
              ·
                refine ⟨1597170393342618072184067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4259121048913648192490845 1597170393342618072184067)
                ·
                  refine ⟨2395755590013927108276101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597170393342618072184067 2395755590013927108276101)
                  ·
                    refine ⟨449204173127611332801769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2395755590013927108276101 449204173127611332801769)
                    ·
                      rfl

theorem cell23_2624466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_2624466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624466 prefixEnd_2624466 := by exact prefixLift 2624466
  have htrace : WordTrace (prefixWord ++ tailWord_2624466) baseStart_2624466 baseEnd_2624466 := by
    simpa [prefixWord, tailWord_2624466, baseEnd_2624466] using wordTrace_append hprefix tailTrace_2624466
  have hstable : (prefixWord ++ tailWord_2624466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624466).length < 2 ^ (prefixWord ++ tailWord_2624466).sum := by decide
  have hdescent : baseEnd_2624466 < baseStart_2624466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624479 : List Nat := [1, 1, 2, 3, 6, 1, 1, 2, 6]
def baseStart_2624479 : Nat := 118140960795 + 2624479 * 2 ^ 59
def prefixEnd_2624479 : Nat := 4983230072969 + 3 ^ 40 * 2624479 * 2
def baseEnd_2624479 : Nat := 149735466070149160838083

theorem tailTrace_2624479 : CollatzResearch.WordTrace tailWord_2624479 prefixEnd_2624479 149735466070149160838083 := by
  unfold tailWord_2624479
  simp only [CollatzResearch.WordTrace]
  refine ⟨95722613058968283173268491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63815075372645522115512327 95722613058968283173268491)
  ·
    refine ⟨143583919588452424759902737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95722613058968283173268491 143583919588452424759902737)
    ·
      refine ⟨107687939691339318569927053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143583919588452424759902737 107687939691339318569927053)
      ·
        refine ⟨40382977384252244463722645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107687939691339318569927053 40382977384252244463722645)
        ·
          refine ⟨1892952064886823959236999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40382977384252244463722645 1892952064886823959236999)
          ·
            refine ⟨2839428097330235938855499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892952064886823959236999 2839428097330235938855499)
            ·
              refine ⟨4259142145995353908283249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839428097330235938855499 4259142145995353908283249)
              ·
                refine ⟨3194356609496515431212437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4259142145995353908283249 3194356609496515431212437)
                ·
                  refine ⟨149735466070149160838083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3194356609496515431212437 149735466070149160838083)
                  ·
                    rfl

theorem cell23_2624479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 6].length) (baseStart_2624479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624479 prefixEnd_2624479 := by exact prefixLift 2624479
  have htrace : WordTrace (prefixWord ++ tailWord_2624479) baseStart_2624479 baseEnd_2624479 := by
    simpa [prefixWord, tailWord_2624479, baseEnd_2624479] using wordTrace_append hprefix tailTrace_2624479
  have hstable : (prefixWord ++ tailWord_2624479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624479).length < 2 ^ (prefixWord ++ tailWord_2624479).sum := by decide
  have hdescent : baseEnd_2624479 < baseStart_2624479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624482 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2624482 : Nat := 118140960795 + 2624482 * 2 ^ 59
def prefixEnd_2624482 : Nat := 4983230072969 + 3 ^ 40 * 2624482 * 2
def baseEnd_2624482 : Nat := 1347620735073305935805233

theorem tailTrace_2624482 : CollatzResearch.WordTrace tailWord_2624482 prefixEnd_2624482 1347620735073305935805233 := by
  unfold tailWord_2624482
  simp only [CollatzResearch.WordTrace]
  refine ⟨23930680619489353671406925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63815148318638276457085133 23930680619489353671406925)
  ·
    refine ⟨8974005232308507626777597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23930680619489353671406925 8974005232308507626777597)
    ·
      refine ⟨3365251962115690360041599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8974005232308507626777597 3365251962115690360041599)
      ·
        refine ⟨5047877943173535540062399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3365251962115690360041599 5047877943173535540062399)
        ·
          refine ⟨7571816914760303310093599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5047877943173535540062399 7571816914760303310093599)
          ·
            refine ⟨11357725372140454965140399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7571816914760303310093599 11357725372140454965140399)
            ·
              refine ⟨17036588058210682447710599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11357725372140454965140399 17036588058210682447710599)
              ·
                refine ⟨25554882087316023671565899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17036588058210682447710599 25554882087316023671565899)
                ·
                  refine ⟨38332323130974035507348849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25554882087316023671565899 38332323130974035507348849)
                  ·
                    refine ⟨28749242348230526630511637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38332323130974035507348849 28749242348230526630511637)
                    ·
                      refine ⟨1347620735073305935805233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28749242348230526630511637 1347620735073305935805233)
                      ·
                        rfl

theorem cell23_2624482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2624482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624482 prefixEnd_2624482 := by exact prefixLift 2624482
  have htrace : WordTrace (prefixWord ++ tailWord_2624482) baseStart_2624482 baseEnd_2624482 := by
    simpa [prefixWord, tailWord_2624482, baseEnd_2624482] using wordTrace_append hprefix tailTrace_2624482
  have hstable : (prefixWord ++ tailWord_2624482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624482).length < 2 ^ (prefixWord ++ tailWord_2624482).sum := by decide
  have hdescent : baseEnd_2624482 < baseStart_2624482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624522 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 4, 4]
def baseStart_2624522 : Nat := 118140960795 + 2624522 * 2 ^ 59
def prefixEnd_2624522 : Nat := 4983230072969 + 3 ^ 40 * 2624522 * 2
def baseEnd_2624522 : Nat := 449213758099828593101683

theorem tailTrace_2624522 : CollatzResearch.WordTrace tailWord_2624522 prefixEnd_2624522 449213758099828593101683 := by
  unfold tailWord_2624522
  simp only [CollatzResearch.WordTrace]
  refine ⟨23931045349453125379270955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63816120931875001011389213 23931045349453125379270955)
  ·
    refine ⟨35896568024179688068906433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23931045349453125379270955 35896568024179688068906433)
    ·
      refine ⟨26922426018134766051679825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35896568024179688068906433 26922426018134766051679825)
      ·
        refine ⟨20191819513601074538759869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26922426018134766051679825 20191819513601074538759869)
        ·
          refine ⟨7571932317600402952034951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20191819513601074538759869 7571932317600402952034951)
          ·
            refine ⟨11357898476400604428052427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7571932317600402952034951 11357898476400604428052427)
            ·
              refine ⟨17036847714600906642078641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11357898476400604428052427 17036847714600906642078641)
              ·
                refine ⟨12777635785950679981558981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17036847714600906642078641 12777635785950679981558981)
                ·
                  refine ⟨2395806709865752496542309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12777635785950679981558981 2395806709865752496542309)
                  ·
                    refine ⟨449213758099828593101683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2395806709865752496542309 449213758099828593101683)
                    ·
                      rfl

theorem cell23_2624522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_2624522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624522 prefixEnd_2624522 := by exact prefixLift 2624522
  have htrace : WordTrace (prefixWord ++ tailWord_2624522) baseStart_2624522 baseEnd_2624522 := by
    simpa [prefixWord, tailWord_2624522, baseEnd_2624522] using wordTrace_append hprefix tailTrace_2624522
  have hstable : (prefixWord ++ tailWord_2624522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624522).length < 2 ^ (prefixWord ++ tailWord_2624522).sum := by decide
  have hdescent : baseEnd_2624522 < baseStart_2624522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624535 : List Nat := [1, 1, 3, 5, 1, 1, 11]
def baseStart_2624535 : Nat := 118140960795 + 2624535 * 2 ^ 59
def prefixEnd_2624535 : Nat := 4983230072969 + 3 ^ 40 * 2624535 * 2
def baseEnd_2624535 : Nat := 16637629006765360844969

theorem tailTrace_2624535 : CollatzResearch.WordTrace tailWord_2624535 prefixEnd_2624535 16637629006765360844969 := by
  unfold tailWord_2624535
  simp only [CollatzResearch.WordTrace]
  refine ⟨95724655546765404737307059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63816437031176936491538039 95724655546765404737307059)
  ·
    refine ⟨143586983320148107105960589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95724655546765404737307059 143586983320148107105960589)
    ·
      refine ⟨53845118745055540164735221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143586983320148107105960589 53845118745055540164735221)
      ·
        refine ⟨5047979882348956890443927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53845118745055540164735221 5047979882348956890443927)
        ·
          refine ⟨7571969823523435335665891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5047979882348956890443927 7571969823523435335665891)
          ·
            refine ⟨11357954735285153003498837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7571969823523435335665891 11357954735285153003498837)
            ·
              refine ⟨16637629006765360844969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11357954735285153003498837 16637629006765360844969)
              ·
                rfl

theorem cell23_2624535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 11].length) (baseStart_2624535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624535 prefixEnd_2624535 := by exact prefixLift 2624535
  have htrace : WordTrace (prefixWord ++ tailWord_2624535) baseStart_2624535 baseEnd_2624535 := by
    simpa [prefixWord, tailWord_2624535, baseEnd_2624535] using wordTrace_append hprefix tailTrace_2624535
  have hstable : (prefixWord ++ tailWord_2624535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624535).length < 2 ^ (prefixWord ++ tailWord_2624535).sum := by decide
  have hdescent : baseEnd_2624535 < baseStart_2624535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624546 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_2624546 : Nat := 118140960795 + 2624546 * 2 ^ 59
def prefixEnd_2624546 : Nat := 4983230072969 + 3 ^ 40 * 2624546 * 2
def baseEnd_2624546 : Nat := 1347653597835193685404939

theorem tailTrace_2624546 : CollatzResearch.WordTrace tailWord_2624546 prefixEnd_2624546 1347653597835193685404939 := by
  unfold tailWord_2624546
  simp only [CollatzResearch.WordTrace]
  refine ⟨23931264187431388403989373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63816704499817035743971661 23931264187431388403989373)
  ·
    refine ⟨8974224070286770651496015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23931264187431388403989373 8974224070286770651496015)
    ·
      refine ⟨13461336105430155977244023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8974224070286770651496015 13461336105430155977244023)
      ·
        refine ⟨20192004158145233965866035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13461336105430155977244023 20192004158145233965866035)
        ·
          refine ⟨30288006237217850948799053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20192004158145233965866035 30288006237217850948799053)
          ·
            refine ⟨11358002338956694105799645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30288006237217850948799053 11358002338956694105799645)
            ·
              refine ⟨4259250877108760289674867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11358002338956694105799645 4259250877108760289674867)
              ·
                refine ⟨6388876315663140434512301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4259250877108760289674867 6388876315663140434512301)
                ·
                  refine ⟨2395828618373677662942113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6388876315663140434512301 2395828618373677662942113)
                  ·
                    refine ⟨1796871463780258247206585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2395828618373677662942113 1796871463780258247206585)
                    ·
                      refine ⟨1347653597835193685404939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1796871463780258247206585 1347653597835193685404939)
                      ·
                        rfl

theorem cell23_2624546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_2624546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624546 prefixEnd_2624546 := by exact prefixLift 2624546
  have htrace : WordTrace (prefixWord ++ tailWord_2624546) baseStart_2624546 baseEnd_2624546 := by
    simpa [prefixWord, tailWord_2624546, baseEnd_2624546] using wordTrace_append hprefix tailTrace_2624546
  have hstable : (prefixWord ++ tailWord_2624546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624546).length < 2 ^ (prefixWord ++ tailWord_2624546).sum := by decide
  have hdescent : baseEnd_2624546 < baseStart_2624546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624562 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_2624562 : Nat := 118140960795 + 2624562 * 2 ^ 59
def prefixEnd_2624562 : Nat := 4983230072969 + 3 ^ 40 * 2624562 * 2
def baseEnd_2624562 : Nat := 1347661813525665622804865

theorem tailTrace_2624562 : CollatzResearch.WordTrace tailWord_2624562 prefixEnd_2624562 1347661813525665622804865 := by
  unfold tailWord_2624562
  simp only [CollatzResearch.WordTrace]
  refine ⟨23931410079416897087134985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63817093545111725565693293 23931410079416897087134985)
  ·
    refine ⟨17948557559562672815351239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23931410079416897087134985 17948557559562672815351239)
    ·
      refine ⟨26922836339344009223026859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17948557559562672815351239 26922836339344009223026859)
      ·
        refine ⟨40384254509016013834540289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26922836339344009223026859 40384254509016013834540289)
        ·
          refine ⟨30288190881762010375905217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40384254509016013834540289 30288190881762010375905217)
          ·
            refine ⟨22716143161321507781928913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30288190881762010375905217 22716143161321507781928913)
            ·
              refine ⟨17037107370991130836446685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22716143161321507781928913 17037107370991130836446685)
              ·
                refine ⟨6388915264121674063667507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17037107370991130836446685 6388915264121674063667507)
                ·
                  refine ⟨9583372896182511095501261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6388915264121674063667507 9583372896182511095501261)
                  ·
                    refine ⟨3593764836068441660812973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9583372896182511095501261 3593764836068441660812973)
                    ·
                      refine ⟨1347661813525665622804865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3593764836068441660812973 1347661813525665622804865)
                      ·
                        rfl

theorem cell23_2624562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_2624562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624562 prefixEnd_2624562 := by exact prefixLift 2624562
  have htrace : WordTrace (prefixWord ++ tailWord_2624562) baseStart_2624562 baseEnd_2624562 := by
    simpa [prefixWord, tailWord_2624562, baseEnd_2624562] using wordTrace_append hprefix tailTrace_2624562
  have hstable : (prefixWord ++ tailWord_2624562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624562).length < 2 ^ (prefixWord ++ tailWord_2624562).sum := by decide
  have hdescent : baseEnd_2624562 < baseStart_2624562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624566 : List Nat := [5, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_2624566 : Nat := 118140960795 + 2624566 * 2 ^ 59
def prefixEnd_2624566 : Nat := 4983230072969 + 3 ^ 40 * 2624566 * 2
def baseEnd_2624566 : Nat := 1347663867448283607154847

theorem tailTrace_2624566 : CollatzResearch.WordTrace tailWord_2624566 prefixEnd_2624566 1347663867448283607154847 := by
  unfold tailWord_2624566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5982861638103318564480347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63817190806435398021123701 5982861638103318564480347)
  ·
    refine ⟨8974292457154977846720521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5982861638103318564480347 8974292457154977846720521)
    ·
      refine ⟨6730719342866233385040391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8974292457154977846720521 6730719342866233385040391)
      ·
        refine ⟨10096079014299350077560587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6730719342866233385040391 10096079014299350077560587)
        ·
          refine ⟨15144118521449025116340881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10096079014299350077560587 15144118521449025116340881)
          ·
            refine ⟨11358088891086768837255661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15144118521449025116340881 11358088891086768837255661)
            ·
              refine ⟨4259283334157538313970873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11358088891086768837255661 4259283334157538313970873)
              ·
                refine ⟨3194462500618153735478155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4259283334157538313970873 3194462500618153735478155)
                ·
                  refine ⟨4791693750927230603217233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194462500618153735478155 4791693750927230603217233)
                  ·
                    refine ⟨3593770313195422952412925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4791693750927230603217233 3593770313195422952412925)
                    ·
                      refine ⟨1347663867448283607154847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3593770313195422952412925 1347663867448283607154847)
                      ·
                        rfl

theorem cell23_2624566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_2624566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624566 prefixEnd_2624566 := by exact prefixLift 2624566
  have htrace : WordTrace (prefixWord ++ tailWord_2624566) baseStart_2624566 baseEnd_2624566 := by
    simpa [prefixWord, tailWord_2624566, baseEnd_2624566] using wordTrace_append hprefix tailTrace_2624566
  have hstable : (prefixWord ++ tailWord_2624566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624566).length < 2 ^ (prefixWord ++ tailWord_2624566).sum := by decide
  have hdescent : baseEnd_2624566 < baseStart_2624566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624710 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_2624710 : Nat := 118140960795 + 2624710 * 2 ^ 59
def prefixEnd_2624710 : Nat := 4983230072969 + 3 ^ 40 * 2624710 * 2
def baseEnd_2624710 : Nat := 149748645406947893750465

theorem tailTrace_2624710 : CollatzResearch.WordTrace tailWord_2624710 prefixEnd_2624710 149748645406947893750465 := by
  unfold tailWord_2624710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2991594947535356550778987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63820692214087606416618389 2991594947535356550778987)
  ·
    refine ⟨4487392421303034826168481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2991594947535356550778987 4487392421303034826168481)
    ·
      refine ⟨3365544315977276119626361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4487392421303034826168481 3365544315977276119626361)
      ·
        refine ⟨2524158236982957089719771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3365544315977276119626361 2524158236982957089719771)
        ·
          refine ⟨3786237355474435634579657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2524158236982957089719771 3786237355474435634579657)
          ·
            refine ⟨2839678016605826725934743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3786237355474435634579657 2839678016605826725934743)
            ·
              refine ⟨4259517024908740088902115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839678016605826725934743 4259517024908740088902115)
              ·
                refine ⟨6389275537363110133353173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4259517024908740088902115 6389275537363110133353173)
                ·
                  refine ⟨149748645406947893750465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6389275537363110133353173 149748645406947893750465)
                  ·
                    rfl

theorem cell23_2624710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_2624710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624710 prefixEnd_2624710 := by exact prefixLift 2624710
  have htrace : WordTrace (prefixWord ++ tailWord_2624710) baseStart_2624710 baseEnd_2624710 := by
    simpa [prefixWord, tailWord_2624710, baseEnd_2624710] using wordTrace_append hprefix tailTrace_2624710
  have hstable : (prefixWord ++ tailWord_2624710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624710).length < 2 ^ (prefixWord ++ tailWord_2624710).sum := by decide
  have hdescent : baseEnd_2624710 < baseStart_2624710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624746 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_2624746 : Nat := 118140960795 + 2624746 * 2 ^ 59
def prefixEnd_2624746 : Nat := 4983230072969 + 3 ^ 40 * 2624746 * 2
def baseEnd_2624746 : Nat := 1347756293966092902904019

theorem tailTrace_2624746 : CollatzResearch.WordTrace tailWord_2624746 prefixEnd_2624746 1347756293966092902904019 := by
  unfold tailWord_2624746
  simp only [CollatzResearch.WordTrace]
  refine ⟨23933087837250246943309523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63821567566000658515492061 23933087837250246943309523)
  ·
    refine ⟨35899631755875370414964285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23933087837250246943309523 35899631755875370414964285)
    ·
      refine ⟨13462361908453263905611607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35899631755875370414964285 13462361908453263905611607)
      ·
        refine ⟨20193542862679895858417411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13462361908453263905611607 20193542862679895858417411)
        ·
          refine ⟨30290314294019843787626117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20193542862679895858417411 30290314294019843787626117)
          ·
            refine ⟨5679433930128720710179897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30290314294019843787626117 5679433930128720710179897)
            ·
              refine ⟨4259575447596540532634923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5679433930128720710179897 4259575447596540532634923)
              ·
                refine ⟨6389363171394810798952385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4259575447596540532634923 6389363171394810798952385)
                ·
                  refine ⟨4792022378546108099214289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6389363171394810798952385 4792022378546108099214289)
                  ·
                    refine ⟨3594016783909581074410717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4792022378546108099214289 3594016783909581074410717)
                    ·
                      refine ⟨1347756293966092902904019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3594016783909581074410717 1347756293966092902904019)
                      ·
                        rfl

theorem cell23_2624746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_2624746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624746 prefixEnd_2624746 := by exact prefixLift 2624746
  have htrace : WordTrace (prefixWord ++ tailWord_2624746) baseStart_2624746 baseEnd_2624746 := by
    simpa [prefixWord, tailWord_2624746, baseEnd_2624746] using wordTrace_append hprefix tailTrace_2624746
  have hstable : (prefixWord ++ tailWord_2624746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624746).length < 2 ^ (prefixWord ++ tailWord_2624746).sum := by decide
  have hdescent : baseEnd_2624746 < baseStart_2624746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624759 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 5, 1, 3]
def baseStart_2624759 : Nat := 118140960795 + 2624759 * 2 ^ 59
def prefixEnd_2624759 : Nat := 4983230072969 + 3 ^ 40 * 2624759 * 2
def baseEnd_2624759 : Nat := 1347762969214601352041459

theorem tailTrace_2624759 : CollatzResearch.WordTrace tailWord_2624759 prefixEnd_2624759 1347762969214601352041459 := by
  unfold tailWord_2624759
  simp only [CollatzResearch.WordTrace]
  refine ⟨95732825497953890993461331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63821883665302593995640887 95732825497953890993461331)
  ·
    refine ⟨143599238246930836490191997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95732825497953890993461331 143599238246930836490191997)
    ·
      refine ⟨53849714342599063683821999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143599238246930836490191997 53849714342599063683821999)
      ·
        refine ⟨80774571513898595525732999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53849714342599063683821999 80774571513898595525732999)
        ·
          refine ⟨121161857270847893288599499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80774571513898595525732999 121161857270847893288599499)
          ·
            refine ⟨181742785906271839932899249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121161857270847893288599499 181742785906271839932899249)
            ·
              refine ⟨136307089429703879949674437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181742785906271839932899249 136307089429703879949674437)
              ·
                refine ⟨25557579268069477490563957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136307089429703879949674437 25557579268069477490563957)
                ·
                  refine ⟨2396023056381513514740371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25557579268069477490563957 2396023056381513514740371)
                  ·
                    refine ⟨3594034584572270272110557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2396023056381513514740371 3594034584572270272110557)
                    ·
                      refine ⟨1347762969214601352041459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3594034584572270272110557 1347762969214601352041459)
                      ·
                        rfl

theorem cell23_2624759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_2624759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624759 prefixEnd_2624759 := by exact prefixLift 2624759
  have htrace : WordTrace (prefixWord ++ tailWord_2624759) baseStart_2624759 baseEnd_2624759 := by
    simpa [prefixWord, tailWord_2624759, baseEnd_2624759] using wordTrace_append hprefix tailTrace_2624759
  have hstable : (prefixWord ++ tailWord_2624759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624759).length < 2 ^ (prefixWord ++ tailWord_2624759).sum := by decide
  have hdescent : baseEnd_2624759 < baseStart_2624759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624766 : List Nat := [4, 2, 2, 1, 1, 3, 2, 2, 6]
def baseStart_2624766 : Nat := 118140960795 + 2624766 * 2 ^ 59
def prefixEnd_2624766 : Nat := 4983230072969 + 3 ^ 40 * 2624766 * 2
def baseEnd_2624766 : Nat := 149751840397686980517103

theorem tailTrace_2624766 : CollatzResearch.WordTrace tailWord_2624766 prefixEnd_2624766 149751840397686980517103 := by
  unfold tailWord_2624766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11966635101116066398620769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63822053872619020792644101 11966635101116066398620769)
  ·
    refine ⟨8974976325837049798965577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11966635101116066398620769 8974976325837049798965577)
    ·
      refine ⟨6731232244377787349224183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8974976325837049798965577 6731232244377787349224183)
      ·
        refine ⟨10096848366566681023836275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6731232244377787349224183 10096848366566681023836275)
        ·
          refine ⟨15145272549850021535754413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10096848366566681023836275 15145272549850021535754413)
          ·
            refine ⟨5679477206193758075907905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15145272549850021535754413 5679477206193758075907905)
            ·
              refine ⟨4259607904645318556930929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5679477206193758075907905 4259607904645318556930929)
              ·
                refine ⟨3194705928483988917698197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4259607904645318556930929 3194705928483988917698197)
                ·
                  refine ⟨149751840397686980517103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3194705928483988917698197 149751840397686980517103)
                  ·
                    rfl

theorem cell23_2624766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_2624766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624766 prefixEnd_2624766 := by exact prefixLift 2624766
  have htrace : WordTrace (prefixWord ++ tailWord_2624766) baseStart_2624766 baseEnd_2624766 := by
    simpa [prefixWord, tailWord_2624766, baseEnd_2624766] using wordTrace_append hprefix tailTrace_2624766
  have hstable : (prefixWord ++ tailWord_2624766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624766).length < 2 ^ (prefixWord ++ tailWord_2624766).sum := by decide
  have hdescent : baseEnd_2624766 < baseStart_2624766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624770 : List Nat := [3, 4, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_2624770 : Nat := 118140960795 + 2624770 * 2 ^ 59
def prefixEnd_2624770 : Nat := 4983230072969 + 3 ^ 40 * 2624770 * 2
def baseEnd_2624770 : Nat := 449256205833933603001303

theorem tailTrace_2624770 : CollatzResearch.WordTrace tailWord_2624770 prefixEnd_2624770 449256205833933603001303 := by
  unfold tailWord_2624770
  simp only [CollatzResearch.WordTrace]
  refine ⟨23933306675228509968027941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63822151133942693248074509 23933306675228509968027941)
  ·
    refine ⟨4487495001605345619005239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23933306675228509968027941 4487495001605345619005239)
    ·
      refine ⟨6731242502408018428507859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4487495001605345619005239 6731242502408018428507859)
      ·
        refine ⟨10096863753612027642761789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6731242502408018428507859 10096863753612027642761789)
        ·
          refine ⟨3786323907604510366035671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10096863753612027642761789 3786323907604510366035671)
          ·
            refine ⟨5679485861406765549053507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3786323907604510366035671 5679485861406765549053507)
            ·
              refine ⟨8519228792110148323580261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5679485861406765549053507 8519228792110148323580261)
              ·
                refine ⟨1597355398520652810671299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8519228792110148323580261 1597355398520652810671299)
                ·
                  refine ⟨2396033097780979216006949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597355398520652810671299 2396033097780979216006949)
                  ·
                    refine ⟨449256205833933603001303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2396033097780979216006949 449256205833933603001303)
                    ·
                      rfl

theorem cell23_2624770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_2624770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624770 prefixEnd_2624770 := by exact prefixLift 2624770
  have htrace : WordTrace (prefixWord ++ tailWord_2624770) baseStart_2624770 baseEnd_2624770 := by
    simpa [prefixWord, tailWord_2624770, baseEnd_2624770] using wordTrace_append hprefix tailTrace_2624770
  have hstable : (prefixWord ++ tailWord_2624770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624770).length < 2 ^ (prefixWord ++ tailWord_2624770).sum := by decide
  have hdescent : baseEnd_2624770 < baseStart_2624770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624803 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 2, 3, 2]
def baseStart_2624803 : Nat := 118140960795 + 2624803 * 2 ^ 59
def prefixEnd_2624803 : Nat := 4983230072969 + 3 ^ 40 * 2624803 * 2
def baseEnd_2624803 : Nat := 1347785562363399179891257

theorem tailTrace_2624803 : CollatzResearch.WordTrace tailWord_2624803 prefixEnd_2624803 1347785562363399179891257 := by
  unfold tailWord_2624803
  simp only [CollatzResearch.WordTrace]
  refine ⟨95734430309794486508063063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63822953539862991005375375 95734430309794486508063063)
  ·
    refine ⟨143601645464691729762094595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95734430309794486508063063 143601645464691729762094595)
    ·
      refine ⟨215402468197037594643141893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143601645464691729762094595 215402468197037594643141893)
      ·
        refine ⟨40387962786944548995589105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215402468197037594643141893 40387962786944548995589105)
        ·
          refine ⟨30290972090208411746691829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40387962786944548995589105 30290972090208411746691829)
          ·
            refine ⟨2839778633457038601252359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30290972090208411746691829 2839778633457038601252359)
            ·
              refine ⟨4259667950185557901878539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839778633457038601252359 4259667950185557901878539)
              ·
                refine ⟨6389501925278336852817809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4259667950185557901878539 6389501925278336852817809)
                ·
                  refine ⟨4792126443958752639613357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6389501925278336852817809 4792126443958752639613357)
                  ·
                    refine ⟨1797047416484532239855009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4792126443958752639613357 1797047416484532239855009)
                    ·
                      refine ⟨1347785562363399179891257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1797047416484532239855009 1347785562363399179891257)
                      ·
                        rfl

theorem cell23_2624803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_2624803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624803 prefixEnd_2624803 := by exact prefixLift 2624803
  have htrace : WordTrace (prefixWord ++ tailWord_2624803) baseStart_2624803 baseEnd_2624803 := by
    simpa [prefixWord, tailWord_2624803, baseEnd_2624803] using wordTrace_append hprefix tailTrace_2624803
  have hstable : (prefixWord ++ tailWord_2624803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624803).length < 2 ^ (prefixWord ++ tailWord_2624803).sum := by decide
  have hdescent : baseEnd_2624803 < baseStart_2624803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624810 : List Nat := [3, 1, 4, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_2624810 : Nat := 118140960795 + 2624810 * 2 ^ 59
def prefixEnd_2624810 : Nat := 4983230072969 + 3 ^ 40 * 2624810 * 2
def baseEnd_2624810 : Nat := 1347789156727980652503725

theorem tailTrace_2624810 : CollatzResearch.WordTrace tailWord_2624810 prefixEnd_2624810 1347789156727980652503725 := by
  unfold tailWord_2624810
  simp only [CollatzResearch.WordTrace]
  refine ⟨23933671405192281675891971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63823123747179417802378589 23933671405192281675891971)
  ·
    refine ⟨35900507107788422513837957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23933671405192281675891971 35900507107788422513837957)
    ·
      refine ⟨6731345082710329221344617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35900507107788422513837957 6731345082710329221344617)
      ·
        refine ⟨5048508812032746916008463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6731345082710329221344617 5048508812032746916008463)
        ·
          refine ⟨7572763218049120374012695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5048508812032746916008463 7572763218049120374012695)
          ·
            refine ⟨11359144827073680561019043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7572763218049120374012695 11359144827073680561019043)
            ·
              refine ⟨17038717240610520841528565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11359144827073680561019043 17038717240610520841528565)
              ·
                refine ⟨1597379741307236328893303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17038717240610520841528565 1597379741307236328893303)
                ·
                  refine ⟨2396069611960854493339955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1597379741307236328893303 2396069611960854493339955)
                  ·
                    refine ⟨3594104417941281740009933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2396069611960854493339955 3594104417941281740009933)
                    ·
                      refine ⟨1347789156727980652503725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3594104417941281740009933 1347789156727980652503725)
                      ·
                        rfl

theorem cell23_2624810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_2624810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624810 prefixEnd_2624810 := by exact prefixLift 2624810
  have htrace : WordTrace (prefixWord ++ tailWord_2624810) baseStart_2624810 baseEnd_2624810 := by
    simpa [prefixWord, tailWord_2624810, baseEnd_2624810] using wordTrace_append hprefix tailTrace_2624810
  have hstable : (prefixWord ++ tailWord_2624810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624810).length < 2 ^ (prefixWord ++ tailWord_2624810).sum := by decide
  have hdescent : baseEnd_2624810 < baseStart_2624810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2624812 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_2624812 : Nat := 118140960795 + 2624812 * 2 ^ 59
def prefixEnd_2624812 : Nat := 4983230072969 + 3 ^ 40 * 2624812 * 2
def baseEnd_2624812 : Nat := 1347790183689289644678715

theorem tailTrace_2624812 : CollatzResearch.WordTrace tailWord_2624812 prefixEnd_2624812 1347790183689289644678715 := by
  unfold tailWord_2624812
  simp only [CollatzResearch.WordTrace]
  refine ⟨47867379283380940522570345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63823172377841254030093793 47867379283380940522570345)
  ·
    refine ⟨35900534462535705391927759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47867379283380940522570345 35900534462535705391927759)
    ·
      refine ⟨53850801693803558087891639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35900534462535705391927759 53850801693803558087891639)
      ·
        refine ⟨80776202540705337131837459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53850801693803558087891639 80776202540705337131837459)
        ·
          refine ⟨121164303811058005697756189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80776202540705337131837459 121164303811058005697756189)
          ·
            refine ⟨45436613929146752136658571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121164303811058005697756189 45436613929146752136658571)
            ·
              refine ⟨68154920893720128204987857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45436613929146752136658571 68154920893720128204987857)
              ·
                refine ⟨51116190670290096153740893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68154920893720128204987857 51116190670290096153740893)
                ·
                  refine ⟨19168571501358786057652835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51116190670290096153740893 19168571501358786057652835)
                  ·
                    refine ⟨28752857252038179086479253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19168571501358786057652835 28752857252038179086479253)
                    ·
                      refine ⟨1347790183689289644678715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28752857252038179086479253 1347790183689289644678715)
                      ·
                        rfl

theorem cell23_2624812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_2624812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2624812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2624812 prefixEnd_2624812 := by exact prefixLift 2624812
  have htrace : WordTrace (prefixWord ++ tailWord_2624812) baseStart_2624812 baseEnd_2624812 := by
    simpa [prefixWord, tailWord_2624812, baseEnd_2624812] using wordTrace_append hprefix tailTrace_2624812
  have hstable : (prefixWord ++ tailWord_2624812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2624812).length < 2 ^ (prefixWord ++ tailWord_2624812).sum := by decide
  have hdescent : baseEnd_2624812 < baseStart_2624812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2624812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
