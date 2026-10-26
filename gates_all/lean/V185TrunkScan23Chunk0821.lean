import V185TrunkScan23Chunk0820

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4857119 : List Nat := [1, 1, 2, 4, 4, 2, 1, 3, 1, 2, 2]
def baseStart_4857119 : Nat := 118140960795 + 4857119 * 2 ^ 59
def prefixEnd_4857119 : Nat := 4983230072969 + 3 ^ 40 * 4857119 * 2
def baseEnd_4857119 : Nat := 2494036643085487233275023

theorem tailTrace_4857119 : CollatzResearch.WordTrace tailWord_4857119 prefixEnd_4857119 2494036643085487233275023 := by
  unfold tailWord_4857119
  simp only [CollatzResearch.WordTrace]
  refine ⟨177153683690494867728062411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118102455793663245152041607 177153683690494867728062411)
  ·
    refine ⟨265730525535742301592093617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177153683690494867728062411 265730525535742301592093617)
    ·
      refine ⟨199297894151806726194070213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265730525535742301592093617 199297894151806726194070213)
      ·
        refine ⟨37368355153463761161388165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199297894151806726194070213 37368355153463761161388165)
        ·
          refine ⟨7006566591274455217760281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37368355153463761161388165 7006566591274455217760281)
          ·
            refine ⟨5254924943455841413320211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7006566591274455217760281 5254924943455841413320211)
            ·
              refine ⟨7882387415183762119980317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5254924943455841413320211 7882387415183762119980317)
              ·
                refine ⟨2955895280693910794992619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7882387415183762119980317 2955895280693910794992619)
                ·
                  refine ⟨4433842921040866192488929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955895280693910794992619 4433842921040866192488929)
                  ·
                    refine ⟨3325382190780649644366697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4433842921040866192488929 3325382190780649644366697)
                    ·
                      refine ⟨2494036643085487233275023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3325382190780649644366697 2494036643085487233275023)
                      ·
                        rfl

theorem cell23_4857119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_4857119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857119 prefixEnd_4857119 := by exact prefixLift 4857119
  have htrace : WordTrace (prefixWord ++ tailWord_4857119) baseStart_4857119 baseEnd_4857119 := by
    simpa [prefixWord, tailWord_4857119, baseEnd_4857119] using wordTrace_append hprefix tailTrace_4857119
  have hstable : (prefixWord ++ tailWord_4857119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857119).length < 2 ^ (prefixWord ++ tailWord_4857119).sum := by decide
  have hdescent : baseEnd_4857119 < baseStart_4857119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857144 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_4857144 : Nat := 118140960795 + 4857144 * 2 ^ 59
def prefixEnd_4857144 : Nat := 4983230072969 + 3 ^ 40 * 4857144 * 2
def baseEnd_4857144 : Nat := 2494049480101849635462407

theorem tailTrace_4857144 : CollatzResearch.WordTrace tailWord_4857144 prefixEnd_4857144 2494049480101849635462407 := by
  unfold tailWord_4857144
  simp only [CollatzResearch.WordTrace]
  refine ⟨88577297757702148498861243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118103063676936197998481657 88577297757702148498861243)
  ·
    refine ⟨132865946636553222748291865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88577297757702148498861243 132865946636553222748291865)
    ·
      refine ⟨99649459977414917061218899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132865946636553222748291865 99649459977414917061218899)
      ·
        refine ⟨149474189966122375591828349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99649459977414917061218899 149474189966122375591828349)
        ·
          refine ⟨56052821237295890846935631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149474189966122375591828349 56052821237295890846935631)
          ·
            refine ⟨84079231855943836270403447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56052821237295890846935631 84079231855943836270403447)
            ·
              refine ⟨126118847783915754405605171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84079231855943836270403447 126118847783915754405605171)
              ·
                refine ⟨189178271675873631608407757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126118847783915754405605171 189178271675873631608407757)
                ·
                  refine ⟨70941851878452611853152909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189178271675873631608407757 70941851878452611853152909)
                  ·
                    refine ⟨26603194454419729444932341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70941851878452611853152909 26603194454419729444932341)
                    ·
                      refine ⟨2494049480101849635462407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26603194454419729444932341 2494049480101849635462407)
                      ·
                        rfl

theorem cell23_4857144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_4857144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857144 prefixEnd_4857144 := by exact prefixLift 4857144
  have htrace : WordTrace (prefixWord ++ tailWord_4857144) baseStart_4857144 baseEnd_4857144 := by
    simpa [prefixWord, tailWord_4857144, baseEnd_4857144] using wordTrace_append hprefix tailTrace_4857144
  have hstable : (prefixWord ++ tailWord_4857144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857144).length < 2 ^ (prefixWord ++ tailWord_4857144).sum := by decide
  have hdescent : baseEnd_4857144 < baseStart_4857144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857248 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 4, 4, 2]
def baseStart_4857248 : Nat := 118140960795 + 4857248 * 2 ^ 59
def prefixEnd_4857248 : Nat := 4983230072969 + 3 ^ 40 * 4857248 * 2
def baseEnd_4857248 : Nat := 2494102882089917228561929

theorem tailTrace_4857248 : CollatzResearch.WordTrace tailWord_4857248 prefixEnd_4857248 2494102882089917228561929 := by
  unfold tailWord_4857248
  simp only [CollatzResearch.WordTrace]
  refine ⟨88579194353513761379754199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118105592471351681839672265 88579194353513761379754199)
  ·
    refine ⟨132868791530270642069631299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88579194353513761379754199 132868791530270642069631299)
    ·
      refine ⟨199303187295405963104446949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132868791530270642069631299 199303187295405963104446949)
      ·
        refine ⟨37369347617888618082083803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199303187295405963104446949 37369347617888618082083803)
        ·
          refine ⟨56054021426832927123125705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37369347617888618082083803 56054021426832927123125705)
          ·
            refine ⟨42040516070124695342344279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56054021426832927123125705 42040516070124695342344279)
            ·
              refine ⟨63060774105187043013516419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42040516070124695342344279 63060774105187043013516419)
              ·
                refine ⟨94591161157780564520274629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63060774105187043013516419 94591161157780564520274629)
                ·
                  refine ⟨17735842717083855847551493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94591161157780564520274629 17735842717083855847551493)
                  ·
                    refine ⟨3325470509453222971415905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17735842717083855847551493 3325470509453222971415905)
                    ·
                      refine ⟨2494102882089917228561929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3325470509453222971415905 2494102882089917228561929)
                      ·
                        rfl

theorem cell23_4857248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_4857248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857248 prefixEnd_4857248 := by exact prefixLift 4857248
  have htrace : WordTrace (prefixWord ++ tailWord_4857248) baseStart_4857248 baseEnd_4857248 := by
    simpa [prefixWord, tailWord_4857248, baseEnd_4857248] using wordTrace_append hprefix tailTrace_4857248
  have hstable : (prefixWord ++ tailWord_4857248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857248).length < 2 ^ (prefixWord ++ tailWord_4857248).sum := by decide
  have hdescent : baseEnd_4857248 < baseStart_4857248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857292 : List Nat := [2, 2, 1, 4, 2, 1, 3, 3, 1, 4]
def baseStart_4857292 : Nat := 118140960795 + 4857292 * 2 ^ 59
def prefixEnd_4857292 : Nat := 4983230072969 + 3 ^ 40 * 4857292 * 2
def baseEnd_4857292 : Nat := 831375158412905018803909

theorem tailTrace_4857292 : CollatzResearch.WordTrace tailWord_4857292 prefixEnd_4857292 831375158412905018803909 := by
  unfold tailWord_4857292
  simp only [CollatzResearch.WordTrace]
  refine ⟨88579996759434059137055065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118106662345912078849406753 88579996759434059137055065)
  ·
    refine ⟨66434997569575544352791299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88579996759434059137055065 66434997569575544352791299)
    ·
      refine ⟨99652496354363316529186949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66434997569575544352791299 99652496354363316529186949)
      ·
        refine ⟨18684843066443121849222553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99652496354363316529186949 18684843066443121849222553)
        ·
          refine ⟨14013632299832341386916915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18684843066443121849222553 14013632299832341386916915)
          ·
            refine ⟨21020448449748512080375373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14013632299832341386916915 21020448449748512080375373)
            ·
              refine ⟨7882668168655692030140765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21020448449748512080375373 7882668168655692030140765)
              ·
                refine ⟨2956000563245884511302787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7882668168655692030140765 2956000563245884511302787)
                ·
                  refine ⟨4434000844868826766954181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2956000563245884511302787 4434000844868826766954181)
                  ·
                    refine ⟨831375158412905018803909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4434000844868826766954181 831375158412905018803909)
                    ·
                      rfl

theorem cell23_4857292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_4857292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857292 prefixEnd_4857292 := by exact prefixLift 4857292
  have htrace : WordTrace (prefixWord ++ tailWord_4857292) baseStart_4857292 baseEnd_4857292 := by
    simpa [prefixWord, tailWord_4857292, baseEnd_4857292] using wordTrace_append hprefix tailTrace_4857292
  have hstable : (prefixWord ++ tailWord_4857292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857292).length < 2 ^ (prefixWord ++ tailWord_4857292).sum := by decide
  have hdescent : baseEnd_4857292 < baseStart_4857292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857302 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_4857302 : Nat := 118140960795 + 4857302 * 2 ^ 59
def prefixEnd_4857302 : Nat := 4983230072969 + 3 ^ 40 * 4857302 * 2
def baseEnd_4857302 : Nat := 2494130610045260017286681

theorem tailTrace_4857302 : CollatzResearch.WordTrace tailWord_4857302 prefixEnd_4857302 2494130610045260017286681 := by
  unfold tailWord_4857302
  simp only [CollatzResearch.WordTrace]
  refine ⟨11072522390551993123873385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118106905499221259987982773 11072522390551993123873385)
  ·
    refine ⟨8304391792913994842905039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11072522390551993123873385 8304391792913994842905039)
    ·
      refine ⟨12456587689370992264357559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8304391792913994842905039 12456587689370992264357559)
      ·
        refine ⟨18684881534056488396536339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12456587689370992264357559 18684881534056488396536339)
        ·
          refine ⟨28027322301084732594804509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18684881534056488396536339 28027322301084732594804509)
          ·
            refine ⟨10510245862906774723051691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28027322301084732594804509 10510245862906774723051691)
            ·
              refine ⟨15765368794360162084577537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10510245862906774723051691 15765368794360162084577537)
              ·
                refine ⟨11824026595770121563433153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15765368794360162084577537 11824026595770121563433153)
                ·
                  refine ⟨8868019946827591172574865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11824026595770121563433153 8868019946827591172574865)
                  ·
                    refine ⟨6651014960120693379431149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8868019946827591172574865 6651014960120693379431149)
                    ·
                      refine ⟨2494130610045260017286681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6651014960120693379431149 2494130610045260017286681)
                      ·
                        rfl

theorem cell23_4857302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_4857302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857302 prefixEnd_4857302 := by exact prefixLift 4857302
  have htrace : WordTrace (prefixWord ++ tailWord_4857302) baseStart_4857302 baseEnd_4857302 := by
    simpa [prefixWord, tailWord_4857302, baseEnd_4857302] using wordTrace_append hprefix tailTrace_4857302
  have hstable : (prefixWord ++ tailWord_4857302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857302).length < 2 ^ (prefixWord ++ tailWord_4857302).sum := by decide
  have hdescent : baseEnd_4857302 < baseStart_4857302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857309 : List Nat := [1, 4, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_4857309 : Nat := 118140960795 + 4857309 * 2 ^ 59
def prefixEnd_4857309 : Nat := 4983230072969 + 3 ^ 40 * 4857309 * 2
def baseEnd_4857309 : Nat := 831378068136613829966383

theorem tailTrace_4857309 : CollatzResearch.WordTrace tailWord_4857309 prefixEnd_4857309 831378068136613829966383 := by
  unfold tailWord_4857309
  simp only [CollatzResearch.WordTrace]
  refine ⟨177160613559806530177478981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118107075706537686784985987 177160613559806530177478981)
  ·
    refine ⟨33217615042463724408277309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177160613559806530177478981 33217615042463724408277309)
    ·
      refine ⟨12456605640923896653103991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33217615042463724408277309 12456605640923896653103991)
      ·
        refine ⟨18684908461385844979655987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12456605640923896653103991 18684908461385844979655987)
        ·
          refine ⟨28027362692078767469483981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18684908461385844979655987 28027362692078767469483981)
          ·
            refine ⟨10510261009529537801056493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28027362692078767469483981 10510261009529537801056493)
            ·
              refine ⟨3941347878573576675396185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10510261009529537801056493 3941347878573576675396185)
              ·
                refine ⟨2956010908930182506547139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3941347878573576675396185 2956010908930182506547139)
                ·
                  refine ⟨4434016363395273759820709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2956010908930182506547139 4434016363395273759820709)
                  ·
                    refine ⟨831378068136613829966383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4434016363395273759820709 831378068136613829966383)
                    ·
                      rfl

theorem cell23_4857309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_4857309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857309 prefixEnd_4857309 := by exact prefixLift 4857309
  have htrace : WordTrace (prefixWord ++ tailWord_4857309) baseStart_4857309 baseEnd_4857309 := by
    simpa [prefixWord, tailWord_4857309, baseEnd_4857309] using wordTrace_append hprefix tailTrace_4857309
  have hstable : (prefixWord ++ tailWord_4857309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857309).length < 2 ^ (prefixWord ++ tailWord_4857309).sum := by decide
  have hdescent : baseEnd_4857309 < baseStart_4857309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857322 : List Nat := [3, 1, 3, 1, 4, 2, 2, 1, 6]
def baseStart_4857322 : Nat := 118140960795 + 4857322 * 2 ^ 59
def prefixEnd_4857322 : Nat := 4983230072969 + 3 ^ 40 * 4857322 * 2
def baseEnd_4857322 : Nat := 277126764406483326559621

theorem tailTrace_4857322 : CollatzResearch.WordTrace tailWord_4857322 prefixEnd_4857322 277126764406483326559621 := by
  unfold tailWord_4857322
  simp only [CollatzResearch.WordTrace]
  refine ⟨44290271927189858349425555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118107391805839622265134813 44290271927189858349425555)
  ·
    refine ⟨66435407890784787524138333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44290271927189858349425555 66435407890784787524138333)
    ·
      refine ⟨24913277959044295321551875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66435407890784787524138333 24913277959044295321551875)
      ·
        refine ⟨37369916938566442982327813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24913277959044295321551875 37369916938566442982327813)
        ·
          refine ⟨7006859425981208059186465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37369916938566442982327813 7006859425981208059186465)
          ·
            refine ⟨5255144569485906044389849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7006859425981208059186465 5255144569485906044389849)
            ·
              refine ⟨3941358427114429533292387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5255144569485906044389849 3941358427114429533292387)
              ·
                refine ⟨5912037640671644299938581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3941358427114429533292387 5912037640671644299938581)
                ·
                  refine ⟨277126764406483326559621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5912037640671644299938581 277126764406483326559621)
                  ·
                    rfl

theorem cell23_4857322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 6].length) (baseStart_4857322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857322 prefixEnd_4857322 := by exact prefixLift 4857322
  have htrace : WordTrace (prefixWord ++ tailWord_4857322) baseStart_4857322 baseEnd_4857322 := by
    simpa [prefixWord, tailWord_4857322, baseEnd_4857322] using wordTrace_append hprefix tailTrace_4857322
  have hstable : (prefixWord ++ tailWord_4857322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857322).length < 2 ^ (prefixWord ++ tailWord_4857322).sum := by decide
  have hdescent : baseEnd_4857322 < baseStart_4857322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857338 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_4857338 : Nat := 118140960795 + 4857338 * 2 ^ 59
def prefixEnd_4857338 : Nat := 4983230072969 + 3 ^ 40 * 4857338 * 2
def baseEnd_4857338 : Nat := 2494149095348821876436515

theorem tailTrace_4857338 : CollatzResearch.WordTrace tailWord_4857338 prefixEnd_4857338 2494149095348821876436515 := by
  unfold tailWord_4857338
  simp only [CollatzResearch.WordTrace]
  refine ⟨44290417819175367032571167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118107780851134312086856445 44290417819175367032571167)
  ·
    refine ⟨66435626728763050548856751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44290417819175367032571167 66435626728763050548856751)
    ·
      refine ⟨99653440093144575823285127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66435626728763050548856751 99653440093144575823285127)
      ·
        refine ⟨149480160139716863734927691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99653440093144575823285127 149480160139716863734927691)
        ·
          refine ⟨224220240209575295602391537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149480160139716863734927691 224220240209575295602391537)
          ·
            refine ⟨168165180157181471701793653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224220240209575295602391537 168165180157181471701793653)
            ·
              refine ⟨15765485639735762972043155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168165180157181471701793653 15765485639735762972043155)
              ·
                refine ⟨23648228459603644458064733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15765485639735762972043155 23648228459603644458064733)
                ·
                  refine ⟨8868085672351366671774275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23648228459603644458064733 8868085672351366671774275)
                  ·
                    refine ⟨13302128508527050007661413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8868085672351366671774275 13302128508527050007661413)
                    ·
                      refine ⟨2494149095348821876436515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13302128508527050007661413 2494149095348821876436515)
                      ·
                        rfl

theorem cell23_4857338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_4857338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857338 prefixEnd_4857338 := by exact prefixLift 4857338
  have htrace : WordTrace (prefixWord ++ tailWord_4857338) baseStart_4857338 baseEnd_4857338 := by
    simpa [prefixWord, tailWord_4857338, baseEnd_4857338] using wordTrace_append hprefix tailTrace_4857338
  have hstable : (prefixWord ++ tailWord_4857338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857338).length < 2 ^ (prefixWord ++ tailWord_4857338).sum := by decide
  have hdescent : baseEnd_4857338 < baseStart_4857338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857365 : List Nat := [1, 3, 2, 1, 3, 2, 1, 4, 2, 4]
def baseStart_4857365 : Nat := 118140960795 + 4857365 * 2 ^ 59
def prefixEnd_4857365 : Nat := 4983230072969 + 3 ^ 40 * 4857365 * 2
def baseEnd_4857365 : Nat := 831387653108831090266297

theorem tailTrace_4857365 : CollatzResearch.WordTrace tailWord_4857365 prefixEnd_4857365 831387653108831090266297 := by
  unfold tailWord_4857365
  simp only [CollatzResearch.WordTrace]
  refine ⟨177162656047603651741517549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118108437365069101161011699 177162656047603651741517549)
  ·
    refine ⟨66435996017851369403069081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177162656047603651741517549 66435996017851369403069081)
    ·
      refine ⟨49826997013388527052301811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66435996017851369403069081 49826997013388527052301811)
      ·
        refine ⟨74740495520082790578452717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49826997013388527052301811 74740495520082790578452717)
        ·
          refine ⟨28027685820031046466919769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74740495520082790578452717 28027685820031046466919769)
          ·
            refine ⟨21020764365023284850189827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28027685820031046466919769 21020764365023284850189827)
            ·
              refine ⟨31531146547534927275284741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21020764365023284850189827 31531146547534927275284741)
              ·
                refine ⟨5912089977662798864115889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31531146547534927275284741 5912089977662798864115889)
                ·
                  refine ⟨4434067483247099148086917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5912089977662798864115889 4434067483247099148086917)
                  ·
                    refine ⟨831387653108831090266297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4434067483247099148086917 831387653108831090266297)
                    ·
                      rfl

theorem cell23_4857365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_4857365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857365 prefixEnd_4857365 := by exact prefixLift 4857365
  have htrace : WordTrace (prefixWord ++ tailWord_4857365) baseStart_4857365 baseEnd_4857365 := by
    simpa [prefixWord, tailWord_4857365, baseEnd_4857365] using wordTrace_append hprefix tailTrace_4857365
  have hstable : (prefixWord ++ tailWord_4857365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857365).length < 2 ^ (prefixWord ++ tailWord_4857365).sum := by decide
  have hdescent : baseEnd_4857365 < baseStart_4857365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857372 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_4857372 : Nat := 118140960795 + 4857372 * 2 ^ 59
def prefixEnd_4857372 : Nat := 4983230072969 + 3 ^ 40 * 4857372 * 2
def baseEnd_4857372 : Nat := 2494166553691074743411359

theorem tailTrace_4857372 : CollatzResearch.WordTrace tailWord_4857372 prefixEnd_4857372 2494166553691074743411359 := by
  unfold tailWord_4857372
  simp only [CollatzResearch.WordTrace]
  refine ⟨88581455679289145968511185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118108607572385527958014913 88581455679289145968511185)
  ·
    refine ⟨66436091759466859476383389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88581455679289145968511185 66436091759466859476383389)
    ·
      refine ⟨24913534409800072303643771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66436091759466859476383389 24913534409800072303643771)
      ·
        refine ⟨37370301614700108455465657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24913534409800072303643771 37370301614700108455465657)
        ·
          refine ⟨28027726211025081341599243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37370301614700108455465657 28027726211025081341599243)
          ·
            refine ⟨42041589316537622012398865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28027726211025081341599243 42041589316537622012398865)
            ·
              refine ⟨31531191987403216509299149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42041589316537622012398865 31531191987403216509299149)
              ·
                refine ⟨11824196995276206190987181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31531191987403216509299149 11824196995276206190987181)
                ·
                  refine ⟨4434073873228577321620193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11824196995276206190987181 4434073873228577321620193)
                  ·
                    refine ⟨3325555404921432991215145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4434073873228577321620193 3325555404921432991215145)
                    ·
                      refine ⟨2494166553691074743411359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3325555404921432991215145 2494166553691074743411359)
                      ·
                        rfl

theorem cell23_4857372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_4857372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857372 prefixEnd_4857372 := by exact prefixLift 4857372
  have htrace : WordTrace (prefixWord ++ tailWord_4857372) baseStart_4857372 baseEnd_4857372 := by
    simpa [prefixWord, tailWord_4857372, baseEnd_4857372] using wordTrace_append hprefix tailTrace_4857372
  have hstable : (prefixWord ++ tailWord_4857372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857372).length < 2 ^ (prefixWord ++ tailWord_4857372).sum := by decide
  have hdescent : baseEnd_4857372 < baseStart_4857372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857378 : List Nat := [3, 3, 1, 1, 1, 1, 5, 8]
def baseStart_4857378 : Nat := 118140960795 + 4857378 * 2 ^ 59
def prefixEnd_4857378 : Nat := 4983230072969 + 3 ^ 40 * 4857378 * 2
def baseEnd_4857378 : Nat := 92376653132407471108753

theorem tailTrace_4857378 : CollatzResearch.WordTrace tailWord_4857378 prefixEnd_4857378 92376653132407471108753 := by
  unfold tailWord_4857378
  simp only [CollatzResearch.WordTrace]
  refine ⟨44290782549139138740435197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118108753464371036641160525 44290782549139138740435197)
  ·
    refine ⟨16609043455927177027663199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44290782549139138740435197 16609043455927177027663199)
    ·
      refine ⟨24913565183890765541494799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16609043455927177027663199 24913565183890765541494799)
      ·
        refine ⟨37370347775836148312242199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24913565183890765541494799 37370347775836148312242199)
        ·
          refine ⟨56055521663754222468363299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37370347775836148312242199 56055521663754222468363299)
          ·
            refine ⟨84083282495631333702544949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56055521663754222468363299 84083282495631333702544949)
            ·
              refine ⟨7882807733965437534613589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84083282495631333702544949 7882807733965437534613589)
              ·
                refine ⟨92376653132407471108753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7882807733965437534613589 92376653132407471108753)
                ·
                  rfl

theorem cell23_4857378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 8].length) (baseStart_4857378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857378 prefixEnd_4857378 := by exact prefixLift 4857378
  have htrace : WordTrace (prefixWord ++ tailWord_4857378) baseStart_4857378 baseEnd_4857378 := by
    simpa [prefixWord, tailWord_4857378, baseEnd_4857378] using wordTrace_append hprefix tailTrace_4857378
  have hstable : (prefixWord ++ tailWord_4857378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857378).length < 2 ^ (prefixWord ++ tailWord_4857378).sum := by decide
  have hdescent : baseEnd_4857378 < baseStart_4857378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857496 : List Nat := [2, 1, 2, 4, 1, 2, 4, 1, 2, 2, 2]
def baseStart_4857496 : Nat := 118140960795 + 4857496 * 2 ^ 59
def prefixEnd_4857496 : Nat := 4983230072969 + 3 ^ 40 * 4857496 * 2
def baseEnd_4857496 : Nat := 2494230225292232258260789

theorem tailTrace_4857496 : CollatzResearch.WordTrace tailWord_4857496 prefixEnd_4857496 2494230225292232258260789 := by
  unfold tailWord_4857496
  simp only [CollatzResearch.WordTrace]
  refine ⟨88583717005064530557268171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118111622673419374076357561 88583717005064530557268171)
  ·
    refine ⟨132875575507596795835902257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88583717005064530557268171 132875575507596795835902257)
    ·
      refine ⟨99656681630697596876926693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132875575507596795835902257 99656681630697596876926693)
      ·
        refine ⟨18685627805755799414423755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99656681630697596876926693 18685627805755799414423755)
        ·
          refine ⟨28028441708633699121635633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18685627805755799414423755 28028441708633699121635633)
          ·
            refine ⟨21021331281475274341226725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28028441708633699121635633 21021331281475274341226725)
            ·
              refine ⟨3941499615276613938980011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21021331281475274341226725 3941499615276613938980011)
              ·
                refine ⟨5912249422914920908470017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3941499615276613938980011 5912249422914920908470017)
                ·
                  refine ⟨4434187067186190681352513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5912249422914920908470017 4434187067186190681352513)
                  ·
                    refine ⟨3325640300389643011014385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4434187067186190681352513 3325640300389643011014385)
                    ·
                      refine ⟨2494230225292232258260789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3325640300389643011014385 2494230225292232258260789)
                      ·
                        rfl

theorem cell23_4857496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_4857496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857496 prefixEnd_4857496 := by exact prefixLift 4857496
  have htrace : WordTrace (prefixWord ++ tailWord_4857496) baseStart_4857496 baseEnd_4857496 := by
    simpa [prefixWord, tailWord_4857496, baseEnd_4857496] using wordTrace_append hprefix tailTrace_4857496
  have hstable : (prefixWord ++ tailWord_4857496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857496).length < 2 ^ (prefixWord ++ tailWord_4857496).sum := by decide
  have hdescent : baseEnd_4857496 < baseStart_4857496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857535 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 4]
def baseStart_4857535 : Nat := 118140960795 + 4857535 * 2 ^ 59
def prefixEnd_4857535 : Nat := 4983230072969 + 3 ^ 40 * 4857535 * 2
def baseEnd_4857535 : Nat := 2494250251037757605673109

theorem tailTrace_4857535 : CollatzResearch.WordTrace tailWord_4857535 prefixEnd_4857535 2494250251037757605673109 := by
  unfold tailWord_4857535
  simp only [CollatzResearch.WordTrace]
  refine ⟨177168856456987770775206059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118112570971325180516804039 177168856456987770775206059)
  ·
    refine ⟨265753284685481656162809089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177168856456987770775206059 265753284685481656162809089)
    ·
      refine ⟨199314963514111242122106817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265753284685481656162809089 199314963514111242122106817)
      ·
        refine ⟨149486222635583431591580113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199314963514111242122106817 149486222635583431591580113)
        ·
          refine ⟨112114666976687573693685085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149486222635583431591580113 112114666976687573693685085)
          ·
            refine ⟨42043000116257840135131907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112114666976687573693685085 42043000116257840135131907)
            ·
              refine ⟨63064500174386760202697861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42043000116257840135131907 63064500174386760202697861)
              ·
                refine ⟨11824593782697517538005849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63064500174386760202697861 11824593782697517538005849)
                ·
                  refine ⟨8868445337023138153504387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11824593782697517538005849 8868445337023138153504387)
                  ·
                    refine ⟨13302668005534707230256581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8868445337023138153504387 13302668005534707230256581)
                    ·
                      refine ⟨2494250251037757605673109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13302668005534707230256581 2494250251037757605673109)
                      ·
                        rfl

theorem cell23_4857535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_4857535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857535 prefixEnd_4857535 := by exact prefixLift 4857535
  have htrace : WordTrace (prefixWord ++ tailWord_4857535) baseStart_4857535 baseEnd_4857535 := by
    simpa [prefixWord, tailWord_4857535, baseEnd_4857535] using wordTrace_append hprefix tailTrace_4857535
  have hstable : (prefixWord ++ tailWord_4857535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857535).length < 2 ^ (prefixWord ++ tailWord_4857535).sum := by decide
  have hdescent : baseEnd_4857535 < baseStart_4857535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857562 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 3, 4]
def baseStart_4857562 : Nat := 118140960795 + 4857562 * 2 ^ 59
def prefixEnd_4857562 : Nat := 4983230072969 + 3 ^ 40 * 4857562 * 2
def baseEnd_4857562 : Nat := 831421371671809666678495

theorem tailTrace_4857562 : CollatzResearch.WordTrace tailWord_4857562 prefixEnd_4857562 831421371671809666678495 := by
  unfold tailWord_4857562
  simp only [CollatzResearch.WordTrace]
  refine ⟨44292460306972488596609735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118113227485259969590959293 44292460306972488596609735)
  ·
    refine ⟨66438690460458732894914603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44292460306972488596609735 66438690460458732894914603)
    ·
      refine ⟨99658035690688099342371905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66438690460458732894914603 99658035690688099342371905)
      ·
        refine ⟨74743526768016074506778929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99658035690688099342371905 74743526768016074506778929)
        ·
          refine ⟨56057645076012055880084197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74743526768016074506778929 56057645076012055880084197)
          ·
            refine ⟨10510808451752260477515787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56057645076012055880084197 10510808451752260477515787)
            ·
              refine ⟨15766212677628390716273681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10510808451752260477515787 15766212677628390716273681)
              ·
                refine ⟨11824659508221293037205261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15766212677628390716273681 11824659508221293037205261)
                ·
                  refine ⟨4434247315582984888951973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11824659508221293037205261 4434247315582984888951973)
                  ·
                    refine ⟨831421371671809666678495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4434247315582984888951973 831421371671809666678495)
                    ·
                      rfl

theorem cell23_4857562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_4857562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857562 prefixEnd_4857562 := by exact prefixLift 4857562
  have htrace : WordTrace (prefixWord ++ tailWord_4857562) baseStart_4857562 baseEnd_4857562 := by
    simpa [prefixWord, tailWord_4857562, baseEnd_4857562] using wordTrace_append hprefix tailTrace_4857562
  have hstable : (prefixWord ++ tailWord_4857562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857562).length < 2 ^ (prefixWord ++ tailWord_4857562).sum := by decide
  have hdescent : baseEnd_4857562 < baseStart_4857562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857569 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_4857569 : Nat := 118140960795 + 4857569 * 2 ^ 59
def prefixEnd_4857569 : Nat := 4983230072969 + 3 ^ 40 * 4857569 * 2
def baseEnd_4857569 : Nat := 2494267709380010472647953

theorem tailTrace_4857569 : CollatzResearch.WordTrace tailWord_4857569 prefixEnd_4857569 2494267709380010472647953 := by
  unfold tailWord_4857569
  simp only [CollatzResearch.WordTrace]
  refine ⟨177170096538864594581943761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118113397692576396387962507 177170096538864594581943761)
  ·
    refine ⟨132877572404148445936457821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177170096538864594581943761 132877572404148445936457821)
    ·
      refine ⟨49829089651555667226171683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132877572404148445936457821 49829089651555667226171683)
      ·
        refine ⟨74743634477333500839257525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49829089651555667226171683 74743634477333500839257525)
        ·
          refine ⟨7007215732250015703680393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74743634477333500839257525 7007215732250015703680393)
          ·
            refine ⟨5255411799187511777760295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7007215732250015703680393 5255411799187511777760295)
            ·
              refine ⟨7883117698781267666640443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5255411799187511777760295 7883117698781267666640443)
              ·
                refine ⟨11824676548171901499960665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7883117698781267666640443 11824676548171901499960665)
                ·
                  refine ⟨8868507411128926124970499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11824676548171901499960665 8868507411128926124970499)
                  ·
                    refine ⟨13302761116693389187455749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8868507411128926124970499 13302761116693389187455749)
                    ·
                      refine ⟨2494267709380010472647953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13302761116693389187455749 2494267709380010472647953)
                      ·
                        rfl

theorem cell23_4857569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_4857569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857569 prefixEnd_4857569 := by exact prefixLift 4857569
  have htrace : WordTrace (prefixWord ++ tailWord_4857569) baseStart_4857569 baseEnd_4857569 := by
    simpa [prefixWord, tailWord_4857569, baseEnd_4857569] using wordTrace_append hprefix tailTrace_4857569
  have hstable : (prefixWord ++ tailWord_4857569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857569).length < 2 ^ (prefixWord ++ tailWord_4857569).sum := by decide
  have hdescent : baseEnd_4857569 < baseStart_4857569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857612 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 1, 5, 2]
def baseStart_4857612 : Nat := 118140960795 + 4857612 * 2 ^ 59
def prefixEnd_4857612 : Nat := 4983230072969 + 3 ^ 40 * 4857612 * 2
def baseEnd_4857612 : Nat := 2494289789048153804410255

theorem tailTrace_4857612 : CollatzResearch.WordTrace tailWord_4857612 prefixEnd_4857612 2494289789048153804410255 := by
  unfold tailWord_4857612
  simp only [CollatzResearch.WordTrace]
  refine ⟨88585832438854406462879545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118114443251805875283839393 88585832438854406462879545)
  ·
    refine ⟨66439374329140804847159659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88585832438854406462879545 66439374329140804847159659)
    ·
      refine ⟨99659061493711207270739489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66439374329140804847159659 99659061493711207270739489)
      ·
        refine ⟨74744296120283405453054617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99659061493711207270739489 74744296120283405453054617)
        ·
          refine ⟨56058222090212554089790963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74744296120283405453054617 56058222090212554089790963)
          ·
            refine ⟨84087333135318831134686445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56058222090212554089790963 84087333135318831134686445)
            ·
              refine ⟨31532749925744561675507417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84087333135318831134686445 31532749925744561675507417)
              ·
                refine ⟨23649562444308421256630563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31532749925744561675507417 23649562444308421256630563)
                ·
                  refine ⟨35474343666462631884945845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23649562444308421256630563 35474343666462631884945845)
                  ·
                    refine ⟨3325719718730871739213673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35474343666462631884945845 3325719718730871739213673)
                    ·
                      refine ⟨2494289789048153804410255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3325719718730871739213673 2494289789048153804410255)
                      ·
                        rfl

theorem cell23_4857612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_4857612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857612 prefixEnd_4857612 := by exact prefixLift 4857612
  have htrace : WordTrace (prefixWord ++ tailWord_4857612) baseStart_4857612 baseEnd_4857612 := by
    simpa [prefixWord, tailWord_4857612, baseEnd_4857612] using wordTrace_append hprefix tailTrace_4857612
  have hstable : (prefixWord ++ tailWord_4857612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857612).length < 2 ^ (prefixWord ++ tailWord_4857612).sum := by decide
  have hdescent : baseEnd_4857612 < baseStart_4857612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857625 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 7, 1, 4]
def baseStart_4857625 : Nat := 118140960795 + 4857625 * 2 ^ 59
def prefixEnd_4857625 : Nat := 4983230072969 + 3 ^ 40 * 4857625 * 2
def baseEnd_4857625 : Nat := 2494296464296662253547695

theorem tailTrace_4857625 : CollatzResearch.WordTrace tailWord_4857625 prefixEnd_4857625 2494296464296662253547695 := by
  unfold tailWord_4857625
  simp only [CollatzResearch.WordTrace]
  refine ⟨177172139026661716145982329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118114759351107810763988219 177172139026661716145982329)
  ·
    refine ⟨132879104269996287109486747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177172139026661716145982329 132879104269996287109486747)
    ·
      refine ⟨199318656404994430664230121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132879104269996287109486747 199318656404994430664230121)
      ·
        refine ⟨149488992303745822998172591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199318656404994430664230121 149488992303745822998172591)
        ·
          refine ⟨224233488455618734497258887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149488992303745822998172591 224233488455618734497258887)
          ·
            refine ⟨336350232683428101745888331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224233488455618734497258887 336350232683428101745888331)
            ·
              refine ⟨504525349025142152618832497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336350232683428101745888331 504525349025142152618832497)
              ·
                refine ⟨378394011768856614464124373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504525349025142152618832497 378394011768856614464124373)
                ·
                  refine ⟨8868609650832576901502915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 378394011768856614464124373 8868609650832576901502915)
                  ·
                    refine ⟨13302914476248865352254373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8868609650832576901502915 13302914476248865352254373)
                    ·
                      refine ⟨2494296464296662253547695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13302914476248865352254373 2494296464296662253547695)
                      ·
                        rfl

theorem cell23_4857625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_4857625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857625 prefixEnd_4857625 := by exact prefixLift 4857625
  have htrace : WordTrace (prefixWord ++ tailWord_4857625) baseStart_4857625 baseEnd_4857625 := by
    simpa [prefixWord, tailWord_4857625, baseEnd_4857625] using wordTrace_append hprefix tailTrace_4857625
  have hstable : (prefixWord ++ tailWord_4857625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857625).length < 2 ^ (prefixWord ++ tailWord_4857625).sum := by decide
  have hdescent : baseEnd_4857625 < baseStart_4857625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857635 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 1, 6]
def baseStart_4857635 : Nat := 118140960795 + 4857635 * 2 ^ 59
def prefixEnd_4857635 : Nat := 4983230072969 + 3 ^ 40 * 4857635 * 2
def baseEnd_4857635 : Nat := 831433866367735738140883

theorem tailTrace_4857635 : CollatzResearch.WordTrace tailWord_4857635 prefixEnd_4857635 831433866367735738140883 := by
  unfold tailWord_4857635
  simp only [CollatzResearch.WordTrace]
  refine ⟨177172503756625487853846359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118115002504416991902564239 177172503756625487853846359)
  ·
    refine ⟨265758755634938231780769539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177172503756625487853846359 265758755634938231780769539)
    ·
      refine ⟨398638133452407347671154309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265758755634938231780769539 398638133452407347671154309)
      ·
        refine ⟨74744650022326377688341433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 398638133452407347671154309 74744650022326377688341433)
        ·
          refine ⟨56058487516744783266256075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74744650022326377688341433 56058487516744783266256075)
          ·
            refine ⟨84087731275117174899384113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56058487516744783266256075 84087731275117174899384113)
            ·
              refine ⟨63065798456337881174538085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84087731275117174899384113 63065798456337881174538085)
              ·
                refine ⟨11824837210563352720225891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63065798456337881174538085 11824837210563352720225891)
                ·
                  refine ⟨17737255815845029080338837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11824837210563352720225891 17737255815845029080338837)
                  ·
                    refine ⟨831433866367735738140883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17737255815845029080338837 831433866367735738140883)
                    ·
                      rfl

theorem cell23_4857635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 6].length) (baseStart_4857635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857635 prefixEnd_4857635 := by exact prefixLift 4857635
  have htrace : WordTrace (prefixWord ++ tailWord_4857635) baseStart_4857635 baseEnd_4857635 := by
    simpa [prefixWord, tailWord_4857635, baseEnd_4857635] using wordTrace_append hprefix tailTrace_4857635
  have hstable : (prefixWord ++ tailWord_4857635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857635).length < 2 ^ (prefixWord ++ tailWord_4857635).sum := by decide
  have hdescent : baseEnd_4857635 < baseStart_4857635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857653 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_4857653 : Nat := 118140960795 + 4857653 * 2 ^ 59
def prefixEnd_4857653 : Nat := 4983230072969 + 3 ^ 40 * 4857653 * 2
def baseEnd_4857653 : Nat := 2494310841754988143997567

theorem tailTrace_4857653 : CollatzResearch.WordTrace tailWord_4857653 prefixEnd_4857653 2494310841754988143997567 := by
  unfold tailWord_4857653
  simp only [CollatzResearch.WordTrace]
  refine ⟨177173160270560276928001613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118115440180373517952001075 177173160270560276928001613)
  ·
    refine ⟨66439935101460103848000605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177173160270560276928001613 66439935101460103848000605)
    ·
      refine ⟨24914975663047538943000227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66439935101460103848000605 24914975663047538943000227)
      ·
        refine ⟨37372463494571308414500341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24914975663047538943000227 37372463494571308414500341)
        ·
          refine ⟨3503668452616060163859407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37372463494571308414500341 3503668452616060163859407)
          ·
            refine ⟨5255502678924090245789111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3503668452616060163859407 5255502678924090245789111)
            ·
              refine ⟨7883254018386135368683667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5255502678924090245789111 7883254018386135368683667)
              ·
                refine ⟨11824881027579203053025501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7883254018386135368683667 11824881027579203053025501)
                ·
                  refine ⟨4434330385342201144884563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11824881027579203053025501 4434330385342201144884563)
                  ·
                    refine ⟨6651495578013301717326845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4434330385342201144884563 6651495578013301717326845)
                    ·
                      refine ⟨2494310841754988143997567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6651495578013301717326845 2494310841754988143997567)
                      ·
                        rfl

theorem cell23_4857653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_4857653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857653 prefixEnd_4857653 := by exact prefixLift 4857653
  have htrace : WordTrace (prefixWord ++ tailWord_4857653) baseStart_4857653 baseEnd_4857653 := by
    simpa [prefixWord, tailWord_4857653, baseEnd_4857653] using wordTrace_append hprefix tailTrace_4857653
  have hstable : (prefixWord ++ tailWord_4857653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857653).length < 2 ^ (prefixWord ++ tailWord_4857653).sum := by decide
  have hdescent : baseEnd_4857653 < baseStart_4857653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857655 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_4857655 : Nat := 118140960795 + 4857655 * 2 ^ 59
def prefixEnd_4857655 : Nat := 4983230072969 + 3 ^ 40 * 4857655 * 2
def baseEnd_4857655 : Nat := 2494311868716297136172557

theorem tailTrace_4857655 : CollatzResearch.WordTrace tailWord_4857655 prefixEnd_4857655 2494311868716297136172557 := by
  unfold tailWord_4857655
  simp only [CollatzResearch.WordTrace]
  refine ⟨177173233216553031269574419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118115488811035354179716279 177173233216553031269574419)
  ·
    refine ⟨265759849824829546904361629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177173233216553031269574419 265759849824829546904361629)
    ·
      refine ⟨99659943684311080089135611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265759849824829546904361629 99659943684311080089135611)
      ·
        refine ⟨149489915526466620133703417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99659943684311080089135611 149489915526466620133703417)
        ·
          refine ⟨112117436644849965100277563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149489915526466620133703417 112117436644849965100277563)
          ·
            refine ⟨168176154967274947650416345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112117436644849965100277563 168176154967274947650416345)
            ·
              refine ⟨126132116225456210737812259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168176154967274947650416345 126132116225456210737812259)
              ·
                refine ⟨189198174338184316106718389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126132116225456210737812259 189198174338184316106718389)
                ·
                  refine ⟨17737328844204779635004849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 189198174338184316106718389 17737328844204779635004849)
                  ·
                    refine ⟨13302996633153584726253637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17737328844204779635004849 13302996633153584726253637)
                    ·
                      refine ⟨2494311868716297136172557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13302996633153584726253637 2494311868716297136172557)
                      ·
                        rfl

theorem cell23_4857655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_4857655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857655 prefixEnd_4857655 := by exact prefixLift 4857655
  have htrace : WordTrace (prefixWord ++ tailWord_4857655) baseStart_4857655 baseEnd_4857655 := by
    simpa [prefixWord, tailWord_4857655, baseEnd_4857655] using wordTrace_append hprefix tailTrace_4857655
  have hstable : (prefixWord ++ tailWord_4857655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857655).length < 2 ^ (prefixWord ++ tailWord_4857655).sum := by decide
  have hdescent : baseEnd_4857655 < baseStart_4857655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857676 : List Nat := [2, 2, 1, 3, 4, 2, 1, 2, 1, 1, 4]
def baseStart_4857676 : Nat := 118140960795 + 4857676 * 2 ^ 59
def prefixEnd_4857676 : Nat := 4983230072969 + 3 ^ 40 * 4857676 * 2
def baseEnd_4857676 : Nat := 2494322651810041554009961

theorem tailTrace_4857676 : CollatzResearch.WordTrace tailWord_4857676 prefixEnd_4857676 2494322651810041554009961 := by
  unfold tailWord_4857676
  simp only [CollatzResearch.WordTrace]
  refine ⟨88586999574738475928044441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118115999432984634570725921 88586999574738475928044441)
  ·
    refine ⟨66440249681053856946033331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88586999574738475928044441 66440249681053856946033331)
    ·
      refine ⟨99660374521580785419049997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66440249681053856946033331 99660374521580785419049997)
      ·
        refine ⟨37372640445592794532143749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99660374521580785419049997 37372640445592794532143749)
        ·
          refine ⟨7007370083548648974776953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37372640445592794532143749 7007370083548648974776953)
          ·
            refine ⟨5255527562661486731082715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7007370083548648974776953 5255527562661486731082715)
            ·
              refine ⟨7883291343992230096624073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5255527562661486731082715 7883291343992230096624073)
              ·
                refine ⟨5912468507994172572468055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7883291343992230096624073 5912468507994172572468055)
                ·
                  refine ⟨8868702761991258858702083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5912468507994172572468055 8868702761991258858702083)
                  ·
                    refine ⟨13303054142986888288053125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8868702761991258858702083 13303054142986888288053125)
                    ·
                      refine ⟨2494322651810041554009961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13303054142986888288053125 2494322651810041554009961)
                      ·
                        rfl

theorem cell23_4857676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_4857676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857676 prefixEnd_4857676 := by exact prefixLift 4857676
  have htrace : WordTrace (prefixWord ++ tailWord_4857676) baseStart_4857676 baseEnd_4857676 := by
    simpa [prefixWord, tailWord_4857676, baseEnd_4857676] using wordTrace_append hprefix tailTrace_4857676
  have hstable : (prefixWord ++ tailWord_4857676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857676).length < 2 ^ (prefixWord ++ tailWord_4857676).sum := by decide
  have hdescent : baseEnd_4857676 < baseStart_4857676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857696 : List Nat := [2, 1, 1, 3, 3, 3, 3, 1, 1, 2, 3]
def baseStart_4857696 : Nat := 118140960795 + 4857696 * 2 ^ 59
def prefixEnd_4857696 : Nat := 4983230072969 + 3 ^ 40 * 4857696 * 2
def baseEnd_4857696 : Nat := 2494332921423131475759869

theorem tailTrace_4857696 : CollatzResearch.WordTrace tailWord_4857696 prefixEnd_4857696 2494332921423131475759869 := by
  unfold tailWord_4857696
  simp only [CollatzResearch.WordTrace]
  refine ⟨88587364304702247635908471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118116485739602996847877961 88587364304702247635908471)
  ·
    refine ⟨132881046457053371453862707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88587364304702247635908471 132881046457053371453862707)
    ·
      refine ⟨199321569685580057180794061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132881046457053371453862707 199321569685580057180794061)
      ·
        refine ⟨74745588632092521442797773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199321569685580057180794061 74745588632092521442797773)
        ·
          refine ⟨28029595737034695541049165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74745588632092521442797773 28029595737034695541049165)
          ·
            refine ⟨10511098401388010827893437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28029595737034695541049165 10511098401388010827893437)
            ·
              refine ⟨3941661900520504060460039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10511098401388010827893437 3941661900520504060460039)
              ·
                refine ⟨5912492850780756090690059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3941661900520504060460039 5912492850780756090690059)
                ·
                  refine ⟨8868739276171134136035089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5912492850780756090690059 8868739276171134136035089)
                  ·
                    refine ⟨6651554457128350602026317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8868739276171134136035089 6651554457128350602026317)
                    ·
                      refine ⟨2494332921423131475759869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6651554457128350602026317 2494332921423131475759869)
                      ·
                        rfl

theorem cell23_4857696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_4857696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857696 prefixEnd_4857696 := by exact prefixLift 4857696
  have htrace : WordTrace (prefixWord ++ tailWord_4857696) baseStart_4857696 baseEnd_4857696 := by
    simpa [prefixWord, tailWord_4857696, baseEnd_4857696] using wordTrace_append hprefix tailTrace_4857696
  have hstable : (prefixWord ++ tailWord_4857696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857696).length < 2 ^ (prefixWord ++ tailWord_4857696).sum := by decide
  have hdescent : baseEnd_4857696 < baseStart_4857696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857705 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 5]
def baseStart_4857705 : Nat := 118140960795 + 4857705 * 2 ^ 59
def prefixEnd_4857705 : Nat := 4983230072969 + 3 ^ 40 * 4857705 * 2
def baseEnd_4857705 : Nat := 2494337542749021940547327

theorem tailTrace_4857705 : CollatzResearch.WordTrace tailWord_4857705 prefixEnd_4857705 2494337542749021940547327 := by
  unfold tailWord_4857705
  simp only [CollatzResearch.WordTrace]
  refine ⟨177175056866371889808894569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118116704577581259872596379 177175056866371889808894569)
  ·
    refine ⟨132881292649778917356670927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177175056866371889808894569 132881292649778917356670927)
    ·
      refine ⟨199321938974668376035006391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132881292649778917356670927 199321938974668376035006391)
      ·
        refine ⟨298982908462002564052509587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199321938974668376035006391 298982908462002564052509587)
        ·
          refine ⟨448474362693003846078764381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298982908462002564052509587 448474362693003846078764381)
          ·
            refine ⟨168177886009876442279536643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 448474362693003846078764381 168177886009876442279536643)
            ·
              refine ⟨252266829014814663419304965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168177886009876442279536643 252266829014814663419304965)
              ·
                refine ⟨47300030440277749391119681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252266829014814663419304965 47300030440277749391119681)
                ·
                  refine ⟨35475022830208312043339761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47300030440277749391119681 35475022830208312043339761)
                  ·
                    refine ⟨26606267122656234032504821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35475022830208312043339761 26606267122656234032504821)
                    ·
                      refine ⟨2494337542749021940547327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26606267122656234032504821 2494337542749021940547327)
                      ·
                        rfl

theorem cell23_4857705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_4857705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857705 prefixEnd_4857705 := by exact prefixLift 4857705
  have htrace : WordTrace (prefixWord ++ tailWord_4857705) baseStart_4857705 baseEnd_4857705 := by
    simpa [prefixWord, tailWord_4857705, baseEnd_4857705] using wordTrace_append hprefix tailTrace_4857705
  have hstable : (prefixWord ++ tailWord_4857705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857705).length < 2 ^ (prefixWord ++ tailWord_4857705).sum := by decide
  have hdescent : baseEnd_4857705 < baseStart_4857705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857709 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_4857709 : Nat := 118140960795 + 4857709 * 2 ^ 59
def prefixEnd_4857709 : Nat := 4983230072969 + 3 ^ 40 * 4857709 * 2
def baseEnd_4857709 : Nat := 2494339596671639924897309

theorem tailTrace_4857709 : CollatzResearch.WordTrace tailWord_4857709 prefixEnd_4857709 2494339596671639924897309 := by
  unfold tailWord_4857709
  simp only [CollatzResearch.WordTrace]
  refine ⟨177175202758357398492040181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118116801838904932328026787 177175202758357398492040181)
  ·
    refine ⟨16610175258596006108628767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177175202758357398492040181 16610175258596006108628767)
    ·
      refine ⟨24915262887894009162943151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16610175258596006108628767 24915262887894009162943151)
      ·
        refine ⟨37372894331841013744414727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24915262887894009162943151 37372894331841013744414727)
        ·
          refine ⟨56059341497761520616622091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37372894331841013744414727 56059341497761520616622091)
          ·
            refine ⟨84089012246642280924933137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56059341497761520616622091 84089012246642280924933137)
            ·
              refine ⟨63066759184981710693699853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84089012246642280924933137 63066759184981710693699853)
              ·
                refine ⟨23650034694368141510137445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63066759184981710693699853 23650034694368141510137445)
                ·
                  refine ⟨4434381505194026533150771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23650034694368141510137445 4434381505194026533150771)
                  ·
                    refine ⟨6651572257791039799726157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4434381505194026533150771 6651572257791039799726157)
                    ·
                      refine ⟨2494339596671639924897309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6651572257791039799726157 2494339596671639924897309)
                      ·
                        rfl

theorem cell23_4857709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_4857709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857709 prefixEnd_4857709 := by exact prefixLift 4857709
  have htrace : WordTrace (prefixWord ++ tailWord_4857709) baseStart_4857709 baseEnd_4857709 := by
    simpa [prefixWord, tailWord_4857709, baseEnd_4857709] using wordTrace_append hprefix tailTrace_4857709
  have hstable : (prefixWord ++ tailWord_4857709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857709).length < 2 ^ (prefixWord ++ tailWord_4857709).sum := by decide
  have hdescent : baseEnd_4857709 < baseStart_4857709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857710 : List Nat := [4, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_4857710 : Nat := 118140960795 + 4857710 * 2 ^ 59
def prefixEnd_4857710 : Nat := 4983230072969 + 3 ^ 40 * 4857710 * 2
def baseEnd_4857710 : Nat := 2494340110152294420984805

theorem tailTrace_4857710 : CollatzResearch.WordTrace tailWord_4857710 prefixEnd_4857710 2494340110152294420984805 := by
  unfold tailWord_4857710
  simp only [CollatzResearch.WordTrace]
  refine ⟨22146904903919221957853323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118116826154235850441884389 22146904903919221957853323)
  ·
    refine ⟨33220357355878832936779985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22146904903919221957853323 33220357355878832936779985)
    ·
      refine ⟨24915268016909124702584989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33220357355878832936779985 24915268016909124702584989)
      ·
        refine ⟨9343225506340921763469371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24915268016909124702584989 9343225506340921763469371)
        ·
          refine ⟨14014838259511382645204057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9343225506340921763469371 14014838259511382645204057)
          ·
            refine ⟨10511128694633536983903043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14014838259511382645204057 10511128694633536983903043)
            ·
              refine ⟨15766693041950305475854565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10511128694633536983903043 15766693041950305475854565)
              ·
                refine ⟨2956254945365682276722731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15766693041950305475854565 2956254945365682276722731)
                ·
                  refine ⟨4434382418048523415084097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2956254945365682276722731 4434382418048523415084097)
                  ·
                    refine ⟨3325786813536392561313073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4434382418048523415084097 3325786813536392561313073)
                    ·
                      refine ⟨2494340110152294420984805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3325786813536392561313073 2494340110152294420984805)
                      ·
                        rfl

theorem cell23_4857710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_4857710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857710 prefixEnd_4857710 := by exact prefixLift 4857710
  have htrace : WordTrace (prefixWord ++ tailWord_4857710) baseStart_4857710 baseEnd_4857710 := by
    simpa [prefixWord, tailWord_4857710, baseEnd_4857710] using wordTrace_append hprefix tailTrace_4857710
  have hstable : (prefixWord ++ tailWord_4857710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857710).length < 2 ^ (prefixWord ++ tailWord_4857710).sum := by decide
  have hdescent : baseEnd_4857710 < baseStart_4857710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857726 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4857726 : Nat := 118140960795 + 4857726 * 2 ^ 59
def prefixEnd_4857726 : Nat := 4983230072969 + 3 ^ 40 * 4857726 * 2
def baseEnd_4857726 : Nat := 2494348325842766358384731

theorem tailTrace_4857726 : CollatzResearch.WordTrace tailWord_4857726 prefixEnd_4857726 2494348325842766358384731 := by
  unfold tailWord_4857726
  simp only [CollatzResearch.WordTrace]
  refine ⟨22146977849911976299426129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118117215199530540263606021 22146977849911976299426129)
  ·
    refine ⟨16610233387433982224569597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22146977849911976299426129 16610233387433982224569597)
    ·
      refine ⟨6228837520287743334213599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16610233387433982224569597 6228837520287743334213599)
      ·
        refine ⟨9343256280431615001320399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6228837520287743334213599 9343256280431615001320399)
        ·
          refine ⟨14014884420647422501980599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9343256280431615001320399 14014884420647422501980599)
          ·
            refine ⟨21022326630971133752970899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14014884420647422501980599 21022326630971133752970899)
            ·
              refine ⟨31533489946456700629456349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21022326630971133752970899 31533489946456700629456349)
              ·
                refine ⟨11825058729921262736046131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31533489946456700629456349 11825058729921262736046131)
                ·
                  refine ⟨17737588094881894104069197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11825058729921262736046131 17737588094881894104069197)
                  ·
                    refine ⟨6651595535580710289025949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17737588094881894104069197 6651595535580710289025949)
                    ·
                      refine ⟨2494348325842766358384731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6651595535580710289025949 2494348325842766358384731)
                      ·
                        rfl

theorem cell23_4857726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4857726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857726 prefixEnd_4857726 := by exact prefixLift 4857726
  have htrace : WordTrace (prefixWord ++ tailWord_4857726) baseStart_4857726 baseEnd_4857726 := by
    simpa [prefixWord, tailWord_4857726, baseEnd_4857726] using wordTrace_append hprefix tailTrace_4857726
  have hstable : (prefixWord ++ tailWord_4857726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857726).length < 2 ^ (prefixWord ++ tailWord_4857726).sum := by decide
  have hdescent : baseEnd_4857726 < baseStart_4857726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857749 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 1, 4, 2]
def baseStart_4857749 : Nat := 118140960795 + 4857749 * 2 ^ 59
def prefixEnd_4857749 : Nat := 4983230072969 + 3 ^ 40 * 4857749 * 2
def baseEnd_4857749 : Nat := 2494360135897819768397125

theorem tailTrace_4857749 : CollatzResearch.WordTrace tailWord_4857749 prefixEnd_4857749 2494360135897819768397125 := by
  unfold tailWord_4857749
  simp only [CollatzResearch.WordTrace]
  refine ⟨177176661678212485323496301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118117774452141656882330867 177176661678212485323496301)
  ·
    refine ⟨66441248129329681996311113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177176661678212485323496301 66441248129329681996311113)
    ·
      refine ⟨49830936096997261497233335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66441248129329681996311113 49830936096997261497233335)
      ·
        refine ⟨74746404145495892245850003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49830936096997261497233335 74746404145495892245850003)
        ·
          refine ⟨112119606218243838368775005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74746404145495892245850003 112119606218243838368775005)
          ·
            refine ⟨42044852331841439388290627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112119606218243838368775005 42044852331841439388290627)
            ·
              refine ⟨63067278497762159082435941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42044852331841439388290627 63067278497762159082435941)
              ·
                refine ⟨11825114718330404827956739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63067278497762159082435941 11825114718330404827956739)
                ·
                  refine ⟨17737672077495607241935109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11825114718330404827956739 17737672077495607241935109)
                  ·
                    refine ⟨3325813514530426357862833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17737672077495607241935109 3325813514530426357862833)
                    ·
                      refine ⟨2494360135897819768397125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3325813514530426357862833 2494360135897819768397125)
                      ·
                        rfl

theorem cell23_4857749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_4857749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857749 prefixEnd_4857749 := by exact prefixLift 4857749
  have htrace : WordTrace (prefixWord ++ tailWord_4857749) baseStart_4857749 baseEnd_4857749 := by
    simpa [prefixWord, tailWord_4857749, baseEnd_4857749] using wordTrace_append hprefix tailTrace_4857749
  have hstable : (prefixWord ++ tailWord_4857749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857749).length < 2 ^ (prefixWord ++ tailWord_4857749).sum := by decide
  have hdescent : baseEnd_4857749 < baseStart_4857749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857802 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 1, 7]
def baseStart_4857802 : Nat := 118140960795 + 4857802 * 2 ^ 59
def prefixEnd_4857802 : Nat := 4983230072969 + 3 ^ 40 * 4857802 * 2
def baseEnd_4857802 : Nat := 831462450124169353678127

theorem tailTrace_4857802 : CollatzResearch.WordTrace tailWord_4857802 prefixEnd_4857802 831462450124169353678127 := by
  unfold tailWord_4857802
  simp only [CollatzResearch.WordTrace]
  refine ⟨44294648686755118843793915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118119063164680316916783773 44294648686755118843793915)
  ·
    refine ⟨66441973030132678265690873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44294648686755118843793915 66441973030132678265690873)
    ·
      refine ⟨49831479772599508699268155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66441973030132678265690873 49831479772599508699268155)
      ·
        refine ⟨74747219658899263048902233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49831479772599508699268155 74747219658899263048902233)
        ·
          refine ⟨56060414744174447286676675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74747219658899263048902233 56060414744174447286676675)
          ·
            refine ⟨84090622116261670930015013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56060414744174447286676675 84090622116261670930015013)
            ·
              refine ⟨15766991646799063299377815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84090622116261670930015013 15766991646799063299377815)
              ·
                refine ⟨23650487470198594949066723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15766991646799063299377815 23650487470198594949066723)
                ·
                  refine ⟨35475731205297892423600085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23650487470198594949066723 35475731205297892423600085)
                  ·
                    refine ⟨831462450124169353678127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35475731205297892423600085 831462450124169353678127)
                    ·
                      rfl

theorem cell23_4857802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_4857802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857802 prefixEnd_4857802 := by exact prefixLift 4857802
  have htrace : WordTrace (prefixWord ++ tailWord_4857802) baseStart_4857802 baseEnd_4857802 := by
    simpa [prefixWord, tailWord_4857802, baseEnd_4857802] using wordTrace_append hprefix tailTrace_4857802
  have hstable : (prefixWord ++ tailWord_4857802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857802).length < 2 ^ (prefixWord ++ tailWord_4857802).sum := by decide
  have hdescent : baseEnd_4857802 < baseStart_4857802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857839 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 1, 6, 2]
def baseStart_4857839 : Nat := 118140960795 + 4857839 * 2 ^ 59
def prefixEnd_4857839 : Nat := 4983230072969 + 3 ^ 40 * 4857839 * 2
def baseEnd_4857839 : Nat := 2494406349156724416271711

theorem tailTrace_4857839 : CollatzResearch.WordTrace tailWord_4857839 prefixEnd_4857839 2494406349156724416271711 := by
  unfold tailWord_4857839
  simp only [CollatzResearch.WordTrace]
  refine ⟨177179944247886430694272571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118119962831924287129515047 177179944247886430694272571)
  ·
    refine ⟨265769916371829646041408857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177179944247886430694272571 265769916371829646041408857)
    ·
      refine ⟨199327437278872234531056643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265769916371829646041408857 199327437278872234531056643)
      ·
        refine ⟨298991155918308351796584965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199327437278872234531056643 298991155918308351796584965)
        ·
          refine ⟨56060841734682815961859681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 298991155918308351796584965 56060841734682815961859681)
          ·
            refine ⟨42045631301012111971394761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56060841734682815961859681 42045631301012111971394761)
            ·
              refine ⟨31534223475759083978546071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42045631301012111971394761 31534223475759083978546071)
              ·
                refine ⟨47301335213638625967819107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31534223475759083978546071 47301335213638625967819107)
                ·
                  refine ⟨70952002820457938951728661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47301335213638625967819107 70952002820457938951728661)
                  ·
                    refine ⟨3325875132208965888362281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70952002820457938951728661 3325875132208965888362281)
                    ·
                      refine ⟨2494406349156724416271711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3325875132208965888362281 2494406349156724416271711)
                      ·
                        rfl

theorem cell23_4857839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 6, 2].length) (baseStart_4857839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857839 prefixEnd_4857839 := by exact prefixLift 4857839
  have htrace : WordTrace (prefixWord ++ tailWord_4857839) baseStart_4857839 baseEnd_4857839 := by
    simpa [prefixWord, tailWord_4857839, baseEnd_4857839] using wordTrace_append hprefix tailTrace_4857839
  have hstable : (prefixWord ++ tailWord_4857839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857839).length < 2 ^ (prefixWord ++ tailWord_4857839).sum := by decide
  have hdescent : baseEnd_4857839 < baseStart_4857839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857906 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_4857906 : Nat := 118140960795 + 4857906 * 2 ^ 59
def prefixEnd_4857906 : Nat := 4983230072969 + 3 ^ 40 * 4857906 * 2
def baseEnd_4857906 : Nat := 2494440752360575654133903

theorem tailTrace_4857906 : CollatzResearch.WordTrace tailWord_4857906 prefixEnd_4857906 2494440752360575654133903 := by
  unfold tailWord_4857906
  simp only [CollatzResearch.WordTrace]
  refine ⟨44295596984660925284240393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118121591959095800757974381 44295596984660925284240393)
  ·
    refine ⟨33221697738495693963180295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44295596984660925284240393 33221697738495693963180295)
    ·
      refine ⟨49832546607743540944770443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33221697738495693963180295 49832546607743540944770443)
      ·
        refine ⟨74748819911615311417155665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49832546607743540944770443 74748819911615311417155665)
        ·
          refine ⟨56061614933711483562866749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74748819911615311417155665 56061614933711483562866749)
          ·
            refine ⟨21023105600141806336075031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56061614933711483562866749 21023105600141806336075031)
            ·
              refine ⟨31534658400212709504112547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21023105600141806336075031 31534658400212709504112547)
              ·
                refine ⟨47301987600319064256168821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31534658400212709504112547 47301987600319064256168821)
                ·
                  refine ⟨4434561337529912274015827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47301987600319064256168821 4434561337529912274015827)
                  ·
                    refine ⟨6651842006294868411023741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4434561337529912274015827 6651842006294868411023741)
                    ·
                      refine ⟨2494440752360575654133903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6651842006294868411023741 2494440752360575654133903)
                      ·
                        rfl

theorem cell23_4857906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_4857906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857906 prefixEnd_4857906 := by exact prefixLift 4857906
  have htrace : WordTrace (prefixWord ++ tailWord_4857906) baseStart_4857906 baseEnd_4857906 := by
    simpa [prefixWord, tailWord_4857906, baseEnd_4857906] using wordTrace_append hprefix tailTrace_4857906
  have hstable : (prefixWord ++ tailWord_4857906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857906).length < 2 ^ (prefixWord ++ tailWord_4857906).sum := by decide
  have hdescent : baseEnd_4857906 < baseStart_4857906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857909 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 3, 5]
def baseStart_4857909 : Nat := 118140960795 + 4857909 * 2 ^ 59
def prefixEnd_4857909 : Nat := 4983230072969 + 3 ^ 40 * 4857909 * 2
def baseEnd_4857909 : Nat := 831480764267513047465463

theorem tailTrace_4857909 : CollatzResearch.WordTrace tailWord_4857909 prefixEnd_4857909 831480764267513047465463 := by
  unfold tailWord_4857909
  simp only [CollatzResearch.WordTrace]
  refine ⟨177182497357632832649320781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118121664905088555099547187 177182497357632832649320781)
  ·
    refine ⟨66443436509112312243495293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177182497357632832649320781 66443436509112312243495293)
    ·
      refine ⟨24916288690917117091310735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66443436509112312243495293 24916288690917117091310735)
      ·
        refine ⟨37374433036375675636966103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24916288690917117091310735 37374433036375675636966103)
        ·
          refine ⟨56061649554563513455449155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37374433036375675636966103 56061649554563513455449155)
          ·
            refine ⟨84092474331845270183173733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56061649554563513455449155 84092474331845270183173733)
            ·
              refine ⟨15767338937220988159345075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84092474331845270183173733 15767338937220988159345075)
              ·
                refine ⟨23651008405831482239017613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15767338937220988159345075 23651008405831482239017613)
                ·
                  refine ⟨8869128152186805839631605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23651008405831482239017613 8869128152186805839631605)
                  ·
                    refine ⟨831480764267513047465463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8869128152186805839631605 831480764267513047465463)
                    ·
                      rfl

theorem cell23_4857909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_4857909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857909 prefixEnd_4857909 := by exact prefixLift 4857909
  have htrace : WordTrace (prefixWord ++ tailWord_4857909) baseStart_4857909 baseEnd_4857909 := by
    simpa [prefixWord, tailWord_4857909, baseEnd_4857909] using wordTrace_append hprefix tailTrace_4857909
  have hstable : (prefixWord ++ tailWord_4857909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857909).length < 2 ^ (prefixWord ++ tailWord_4857909).sum := by decide
  have hdescent : baseEnd_4857909 < baseStart_4857909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857916 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 1, 5, 2]
def baseStart_4857916 : Nat := 118140960795 + 4857916 * 2 ^ 59
def prefixEnd_4857916 : Nat := 4983230072969 + 3 ^ 40 * 4857916 * 2
def baseEnd_4857916 : Nat := 2494445887167120615008857

theorem tailTrace_4857916 : CollatzResearch.WordTrace tailWord_4857916 prefixEnd_4857916 2494445887167120615008857 := by
  unfold tailWord_4857916
  simp only [CollatzResearch.WordTrace]
  refine ⟨88591376334303736422412801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118121835112404981896550401 88591376334303736422412801)
  ·
    refine ⟨66443532250727802316809601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88591376334303736422412801 66443532250727802316809601)
    ·
      refine ⟨49832649188045851737607201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66443532250727802316809601 49832649188045851737607201)
      ·
        refine ⟨37374486891034388803205401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49832649188045851737607201 37374486891034388803205401)
        ·
          refine ⟨28030865168275791602404051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37374486891034388803205401 28030865168275791602404051)
          ·
            refine ⟨42046297752413687403606077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28030865168275791602404051 42046297752413687403606077)
            ·
              refine ⟨15767361657155132776352279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42046297752413687403606077 15767361657155132776352279)
              ·
                refine ⟨23651042485732699164528419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15767361657155132776352279 23651042485732699164528419)
                ·
                  refine ⟨35476563728599048746792629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23651042485732699164528419 35476563728599048746792629)
                  ·
                    refine ⟨3325927849556160820011809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35476563728599048746792629 3325927849556160820011809)
                    ·
                      refine ⟨2494445887167120615008857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3325927849556160820011809 2494445887167120615008857)
                      ·
                        rfl

theorem cell23_4857916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_4857916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857916 prefixEnd_4857916 := by exact prefixLift 4857916
  have htrace : WordTrace (prefixWord ++ tailWord_4857916) baseStart_4857916 baseEnd_4857916 := by
    simpa [prefixWord, tailWord_4857916, baseEnd_4857916] using wordTrace_append hprefix tailTrace_4857916
  have hstable : (prefixWord ++ tailWord_4857916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857916).length < 2 ^ (prefixWord ++ tailWord_4857916).sum := by decide
  have hdescent : baseEnd_4857916 < baseStart_4857916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857933 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_4857933 : Nat := 118140960795 + 4857933 * 2 ^ 59
def prefixEnd_4857933 : Nat := 4983230072969 + 3 ^ 40 * 4857933 * 2
def baseEnd_4857933 : Nat := 2494454616338247048496279

theorem tailTrace_4857933 : CollatzResearch.WordTrace tailWord_4857933 prefixEnd_4857933 2494454616338247048496279 := by
  unfold tailWord_4857933
  simp only [CollatzResearch.WordTrace]
  refine ⟨177183372709545884748194453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118122248473030589832129635 177183372709545884748194453)
  ·
    refine ⟨8305470595759963347571615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 177183372709545884748194453 8305470595759963347571615)
    ·
      refine ⟨12458205893639945021357423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8305470595759963347571615 12458205893639945021357423)
      ·
        refine ⟨18687308840459917532036135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12458205893639945021357423 18687308840459917532036135)
        ·
          refine ⟨28030963260689876298054203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18687308840459917532036135 28030963260689876298054203)
          ·
            refine ⟨42046444891034814447081305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28030963260689876298054203 42046444891034814447081305)
            ·
              refine ⟨31534833668276110835310979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42046444891034814447081305 31534833668276110835310979)
              ·
                refine ⟨47302250502414166252966469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31534833668276110835310979 47302250502414166252966469)
                ·
                  refine ⟨8869171969202656172431213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47302250502414166252966469 8869171969202656172431213)
                  ·
                    refine ⟨3325939488450996064661705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8869171969202656172431213 3325939488450996064661705)
                    ·
                      refine ⟨2494454616338247048496279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3325939488450996064661705 2494454616338247048496279)
                      ·
                        rfl

theorem cell23_4857933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_4857933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857933 prefixEnd_4857933 := by exact prefixLift 4857933
  have htrace : WordTrace (prefixWord ++ tailWord_4857933) baseStart_4857933 baseEnd_4857933 := by
    simpa [prefixWord, tailWord_4857933, baseEnd_4857933] using wordTrace_append hprefix tailTrace_4857933
  have hstable : (prefixWord ++ tailWord_4857933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857933).length < 2 ^ (prefixWord ++ tailWord_4857933).sum := by decide
  have hdescent : baseEnd_4857933 < baseStart_4857933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857956 : List Nat := [2, 3, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_4857956 : Nat := 118140960795 + 4857956 * 2 ^ 59
def prefixEnd_4857956 : Nat := 4983230072969 + 3 ^ 40 * 4857956 * 2
def baseEnd_4857956 : Nat := 831488808797766819502891

theorem tailTrace_4857956 : CollatzResearch.WordTrace tailWord_4857956 prefixEnd_4857956 831488808797766819502891 := by
  unfold tailWord_4857956
  simp only [CollatzResearch.WordTrace]
  refine ⟨88592105794231279838140861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118122807725641706450854481 88592105794231279838140861)
  ·
    refine ⟨33222039672836729939302823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88592105794231279838140861 33222039672836729939302823)
    ·
      refine ⟨49833059509255094908954235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33222039672836729939302823 49833059509255094908954235)
      ·
        refine ⟨74749589263882642363431353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49833059509255094908954235 74749589263882642363431353)
        ·
          refine ⟨56062191947911981772573515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74749589263882642363431353 56062191947911981772573515)
          ·
            refine ⟨84093287921867972658860273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56062191947911981772573515 84093287921867972658860273)
            ·
              refine ⟨63069965941400979494145205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84093287921867972658860273 63069965941400979494145205)
              ·
                refine ⟨5912809307006341827576113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63069965941400979494145205 5912809307006341827576113)
                ·
                  refine ⟨4434606980254756370682085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5912809307006341827576113 4434606980254756370682085)
                  ·
                    refine ⟨831488808797766819502891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4434606980254756370682085 831488808797766819502891)
                    ·
                      rfl

theorem cell23_4857956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_4857956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857956 prefixEnd_4857956 := by exact prefixLift 4857956
  have htrace : WordTrace (prefixWord ++ tailWord_4857956) baseStart_4857956 baseEnd_4857956 := by
    simpa [prefixWord, tailWord_4857956, baseEnd_4857956] using wordTrace_append hprefix tailTrace_4857956
  have hstable : (prefixWord ++ tailWord_4857956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857956).length < 2 ^ (prefixWord ++ tailWord_4857956).sum := by decide
  have hdescent : baseEnd_4857956 < baseStart_4857956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4857959 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_4857959 : Nat := 118140960795 + 4857959 * 2 ^ 59
def prefixEnd_4857959 : Nat := 4983230072969 + 3 ^ 40 * 4857959 * 2
def baseEnd_4857959 : Nat := 2494467966835263946771159

theorem tailTrace_4857959 : CollatzResearch.WordTrace tailWord_4857959 prefixEnd_4857959 2494467966835263946771159 := by
  unfold tailWord_4857959
  simp only [CollatzResearch.WordTrace]
  refine ⟨177184321007451691188640931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118122880671634460792427287 177184321007451691188640931)
  ·
    refine ⟨265776481511177536782961397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177184321007451691188640931 265776481511177536782961397)
    ·
      refine ⟨24916545141672894073402631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 265776481511177536782961397 24916545141672894073402631)
      ·
        refine ⟨37374817712509341110103947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24916545141672894073402631 37374817712509341110103947)
        ·
          refine ⟨56062226568764011665155921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37374817712509341110103947 56062226568764011665155921)
          ·
            refine ⟨42046669926573008748866941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56062226568764011665155921 42046669926573008748866941)
            ·
              refine ⟨15767501222464878280825103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42046669926573008748866941 15767501222464878280825103)
              ·
                refine ⟨23651251833697317421237655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15767501222464878280825103 23651251833697317421237655)
                ·
                  refine ⟨35476877750545976131856483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23651251833697317421237655 35476877750545976131856483)
                  ·
                    refine ⟨53215316625818964197784725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35476877750545976131856483 53215316625818964197784725)
                    ·
                      refine ⟨2494467966835263946771159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53215316625818964197784725 2494467966835263946771159)
                      ·
                        rfl

theorem cell23_4857959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_4857959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4857959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4857959 prefixEnd_4857959 := by exact prefixLift 4857959
  have htrace : WordTrace (prefixWord ++ tailWord_4857959) baseStart_4857959 baseEnd_4857959 := by
    simpa [prefixWord, tailWord_4857959, baseEnd_4857959] using wordTrace_append hprefix tailTrace_4857959
  have hstable : (prefixWord ++ tailWord_4857959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4857959).length < 2 ^ (prefixWord ++ tailWord_4857959).sum := by decide
  have hdescent : baseEnd_4857959 < baseStart_4857959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4857959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858007 : List Nat := [1, 1, 3, 3, 5, 1, 2, 1, 2, 4]
def baseStart_4858007 : Nat := 118140960795 + 4858007 * 2 ^ 59
def prefixEnd_4858007 : Nat := 4983230072969 + 3 ^ 40 * 4858007 * 2
def baseEnd_4858007 : Nat := 831497537968893252990313

theorem tailTrace_4858007 : CollatzResearch.WordTrace tailWord_4858007 prefixEnd_4858007 831497537968893252990313 := by
  unfold tailWord_4858007
  simp only [CollatzResearch.WordTrace]
  refine ⟨177186071711277795386388275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118124047807518530257592183 177186071711277795386388275)
  ·
    refine ⟨265779107566916693079582413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177186071711277795386388275 265779107566916693079582413)
    ·
      refine ⟨99667165337593759904843405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265779107566916693079582413 99667165337593759904843405)
      ·
        refine ⟨37375187001597659964316277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99667165337593759904843405 37375187001597659964316277)
        ·
          refine ⟨3503923781399780621654651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37375187001597659964316277 3503923781399780621654651)
          ·
            refine ⟨5255885672099670932481977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3503923781399780621654651 5255885672099670932481977)
            ·
              refine ⟨3941914254074753199361483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5255885672099670932481977 3941914254074753199361483)
              ·
                refine ⟨5912871381112129799042225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3941914254074753199361483 5912871381112129799042225)
                ·
                  refine ⟨4434653535834097349281669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5912871381112129799042225 4434653535834097349281669)
                  ·
                    refine ⟨831497537968893252990313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4434653535834097349281669 831497537968893252990313)
                    ·
                      rfl

theorem cell23_4858007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_4858007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858007 prefixEnd_4858007 := by exact prefixLift 4858007
  have htrace : WordTrace (prefixWord ++ tailWord_4858007) baseStart_4858007 baseEnd_4858007 := by
    simpa [prefixWord, tailWord_4858007, baseEnd_4858007] using wordTrace_append hprefix tailTrace_4858007
  have hstable : (prefixWord ++ tailWord_4858007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858007).length < 2 ^ (prefixWord ++ tailWord_4858007).sum := by decide
  have hdescent : baseEnd_4858007 < baseStart_4858007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858040 : List Nat := [2, 1, 2, 1, 2, 1, 7, 1, 1, 3, 2]
def baseStart_4858040 : Nat := 118140960795 + 4858040 * 2 ^ 59
def prefixEnd_4858040 : Nat := 4983230072969 + 3 ^ 40 * 4858040 * 2
def baseEnd_4858040 : Nat := 2494509558768278129858287

theorem tailTrace_4858040 : CollatzResearch.WordTrace tailWord_4858040 prefixEnd_4858040 2494509558768278129858287 := by
  unfold tailWord_4858040
  simp only [CollatzResearch.WordTrace]
  refine ⟨88593637660079121011169787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118124850213438828014893049 88593637660079121011169787)
  ·
    refine ⟨132890456490118681516754681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88593637660079121011169787 132890456490118681516754681)
    ·
      refine ⟨99667842367589011137566011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132890456490118681516754681 99667842367589011137566011)
      ·
        refine ⟨149501763551383516706349017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99667842367589011137566011 149501763551383516706349017)
        ·
          refine ⟨112126322663537637529761763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149501763551383516706349017 112126322663537637529761763)
          ·
            refine ⟨168189483995306456294642645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112126322663537637529761763 168189483995306456294642645)
            ·
              refine ⟨3941941031139995069405687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 168189483995306456294642645 3941941031139995069405687)
              ·
                refine ⟨5912911546709992604108531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3941941031139995069405687 5912911546709992604108531)
                ·
                  refine ⟨8869367320064988906162797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5912911546709992604108531 8869367320064988906162797)
                  ·
                    refine ⟨3326012745024370839811049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8869367320064988906162797 3326012745024370839811049)
                    ·
                      refine ⟨2494509558768278129858287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3326012745024370839811049 2494509558768278129858287)
                      ·
                        rfl

theorem cell23_4858040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 1, 3, 2].length) (baseStart_4858040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858040 prefixEnd_4858040 := by exact prefixLift 4858040
  have htrace : WordTrace (prefixWord ++ tailWord_4858040) baseStart_4858040 baseEnd_4858040 := by
    simpa [prefixWord, tailWord_4858040, baseEnd_4858040] using wordTrace_append hprefix tailTrace_4858040
  have hstable : (prefixWord ++ tailWord_4858040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858040).length < 2 ^ (prefixWord ++ tailWord_4858040).sum := by decide
  have hdescent : baseEnd_4858040 < baseStart_4858040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858053 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 4, 2, 2]
def baseStart_4858053 : Nat := 118140960795 + 4858053 * 2 ^ 59
def prefixEnd_4858053 : Nat := 4983230072969 + 3 ^ 40 * 4858053 * 2
def baseEnd_4858053 : Nat := 2494516234016786578995727

theorem tailTrace_4858053 : CollatzResearch.WordTrace tailWord_4858053 prefixEnd_4858053 2494516234016786578995727 := by
  unfold tailWord_4858053
  simp only [CollatzResearch.WordTrace]
  refine ⟨177187749469111145242562813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118125166312740763495041875 177187749469111145242562813)
  ·
    refine ⟨66445406050916679465961055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177187749469111145242562813 66445406050916679465961055)
    ·
      refine ⟨99668109076375019198941583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66445406050916679465961055 99668109076375019198941583)
      ·
        refine ⟨149502163614562528798412375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99668109076375019198941583 149502163614562528798412375)
        ·
          refine ⟨224253245421843793197618563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149502163614562528798412375 224253245421843793197618563)
          ·
            refine ⟨336379868132765689796427845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224253245421843793197618563 336379868132765689796427845)
            ·
              refine ⟨63071225274893566836830221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 336379868132765689796427845 63071225274893566836830221)
              ·
                refine ⟨23651709478085087563811333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63071225274893566836830221 23651709478085087563811333)
                ·
                  refine ⟨4434695527140953918214625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23651709478085087563811333 4434695527140953918214625)
                  ·
                    refine ⟨3326021645355715438660969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4434695527140953918214625 3326021645355715438660969)
                    ·
                      refine ⟨2494516234016786578995727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3326021645355715438660969 2494516234016786578995727)
                      ·
                        rfl

theorem cell23_4858053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 2, 2].length) (baseStart_4858053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858053 prefixEnd_4858053 := by exact prefixLift 4858053
  have htrace : WordTrace (prefixWord ++ tailWord_4858053) baseStart_4858053 baseEnd_4858053 := by
    simpa [prefixWord, tailWord_4858053, baseEnd_4858053] using wordTrace_append hprefix tailTrace_4858053
  have hstable : (prefixWord ++ tailWord_4858053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858053).length < 2 ^ (prefixWord ++ tailWord_4858053).sum := by decide
  have hdescent : baseEnd_4858053 < baseStart_4858053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858059 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 7]
def baseStart_4858059 : Nat := 118140960795 + 4858059 * 2 ^ 59
def prefixEnd_4858059 : Nat := 4983230072969 + 3 ^ 40 * 4858059 * 2
def baseEnd_4858059 : Nat := 277168812766745950613411

theorem tailTrace_4858059 : CollatzResearch.WordTrace tailWord_4858059 prefixEnd_4858059 277168812766745950613411 := by
  unfold tailWord_4858059
  simp only [CollatzResearch.WordTrace]
  refine ⟨177187968307089408267281231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118125312204726272178187487 177187968307089408267281231)
  ·
    refine ⟨265781952460634112400921847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177187968307089408267281231 265781952460634112400921847)
    ·
      refine ⟨398672928690951168601382771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265781952460634112400921847 398672928690951168601382771)
      ·
        refine ⟨598009393036426752902074157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398672928690951168601382771 598009393036426752902074157)
        ·
          refine ⟨224253522388660032338277809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 598009393036426752902074157 224253522388660032338277809)
          ·
            refine ⟨168190141791495024253708357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224253522388660032338277809 168190141791495024253708357)
            ·
              refine ⟨31535651585905317047570317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168190141791495024253708357 31535651585905317047570317)
              ·
                refine ⟨11825869344714493892838869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31535651585905317047570317 11825869344714493892838869)
                ·
                  refine ⟨277168812766745950613411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11825869344714493892838869 277168812766745950613411)
                  ·
                    rfl

theorem cell23_4858059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 7].length) (baseStart_4858059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858059 prefixEnd_4858059 := by exact prefixLift 4858059
  have htrace : WordTrace (prefixWord ++ tailWord_4858059) baseStart_4858059 baseEnd_4858059 := by
    simpa [prefixWord, tailWord_4858059, baseEnd_4858059] using wordTrace_append hprefix tailTrace_4858059
  have hstable : (prefixWord ++ tailWord_4858059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858059).length < 2 ^ (prefixWord ++ tailWord_4858059).sum := by decide
  have hdescent : baseEnd_4858059 < baseStart_4858059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858066 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_4858066 : Nat := 118140960795 + 4858066 * 2 ^ 59
def prefixEnd_4858066 : Nat := 4983230072969 + 3 ^ 40 * 4858066 * 2
def baseEnd_4858066 : Nat := 2494522909265295028133167

theorem tailTrace_4858066 : CollatzResearch.WordTrace tailWord_4858066 prefixEnd_4858066 2494522909265295028133167 := by
  unfold tailWord_4858066
  simp only [CollatzResearch.WordTrace]
  refine ⟨44297055904516012115696513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118125482412042698975190701 44297055904516012115696513)
  ·
    refine ⟨33222791928387009086772385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44297055904516012115696513 33222791928387009086772385)
    ·
      refine ⟨24917093946290256815079289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33222791928387009086772385 24917093946290256815079289)
      ·
        refine ⟨18687820459717692611309467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24917093946290256815079289 18687820459717692611309467)
        ·
          refine ⟨28031730689576538916964201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18687820459717692611309467 28031730689576538916964201)
          ·
            refine ⟨21023798017182404187723151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28031730689576538916964201 21023798017182404187723151)
            ·
              refine ⟨31535697025773606281584727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21023798017182404187723151 31535697025773606281584727)
              ·
                refine ⟨47303545538660409422377091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31535697025773606281584727 47303545538660409422377091)
                ·
                  refine ⟨70955318307990614133565637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47303545538660409422377091 70955318307990614133565637)
                  ·
                    refine ⟨13304122182748240150043557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70955318307990614133565637 13304122182748240150043557)
                    ·
                      refine ⟨2494522909265295028133167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13304122182748240150043557 2494522909265295028133167)
                      ·
                        rfl

theorem cell23_4858066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_4858066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858066 prefixEnd_4858066 := by exact prefixLift 4858066
  have htrace : WordTrace (prefixWord ++ tailWord_4858066) baseStart_4858066 baseEnd_4858066 := by
    simpa [prefixWord, tailWord_4858066, baseEnd_4858066] using wordTrace_append hprefix tailTrace_4858066
  have hstable : (prefixWord ++ tailWord_4858066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858066).length < 2 ^ (prefixWord ++ tailWord_4858066).sum := by decide
  have hdescent : baseEnd_4858066 < baseStart_4858066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858089 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 1, 7]
def baseStart_4858089 : Nat := 118140960795 + 4858089 * 2 ^ 59
def prefixEnd_4858089 : Nat := 4983230072969 + 3 ^ 40 * 4858089 * 2
def baseEnd_4858089 : Nat := 831511573106782812715187

theorem tailTrace_4858089 : CollatzResearch.WordTrace tailWord_4858089 prefixEnd_4858089 831511573106782812715187 := by
  unfold tailWord_4858089
  simp only [CollatzResearch.WordTrace]
  refine ⟨177189062496980723390873321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118126041664653815593915547 177189062496980723390873321)
  ·
    refine ⟨132891796872735542543154991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177189062496980723390873321 132891796872735542543154991)
    ·
      refine ⟨199337695309103313814732487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132891796872735542543154991 199337695309103313814732487)
      ·
        refine ⟨299006542963654970722098731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199337695309103313814732487 299006542963654970722098731)
        ·
          refine ⟨448509814445482456083148097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299006542963654970722098731 448509814445482456083148097)
          ·
            refine ⟨336382360834111842062361073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448509814445482456083148097 336382360834111842062361073)
            ·
              refine ⟨252286770625583881546770805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336382360834111842062361073 252286770625583881546770805)
              ·
                refine ⟨23651884746148488895009763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 252286770625583881546770805 23651884746148488895009763)
                ·
                  refine ⟨35477827119222733342514645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23651884746148488895009763 35477827119222733342514645)
                  ·
                    refine ⟨831511573106782812715187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35477827119222733342514645 831511573106782812715187)
                    ·
                      rfl

theorem cell23_4858089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_4858089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858089 prefixEnd_4858089 := by exact prefixLift 4858089
  have htrace : WordTrace (prefixWord ++ tailWord_4858089) baseStart_4858089 baseEnd_4858089 := by
    simpa [prefixWord, tailWord_4858089, baseEnd_4858089] using wordTrace_append hprefix tailTrace_4858089
  have hstable : (prefixWord ++ tailWord_4858089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858089).length < 2 ^ (prefixWord ++ tailWord_4858089).sum := by decide
  have hdescent : baseEnd_4858089 < baseStart_4858089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858126 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_4858126 : Nat := 118140960795 + 4858126 * 2 ^ 59
def prefixEnd_4858126 : Nat := 4983230072969 + 3 ^ 40 * 4858126 * 2
def baseEnd_4858126 : Nat := 2494553718104564793382891

theorem tailTrace_4858126 : CollatzResearch.WordTrace tailWord_4858126 prefixEnd_4858126 2494553718104564793382891 := by
  unfold tailWord_4858126
  simp only [CollatzResearch.WordTrace]
  refine ⟨22148801499730834838746279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118126941331897785806646821 22148801499730834838746279)
  ·
    refine ⟨33223202249596252258119419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22148801499730834838746279 33223202249596252258119419)
    ·
      refine ⟨49834803374394378387179129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33223202249596252258119419 49834803374394378387179129)
      ·
        refine ⟨37376102530795783790384347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49834803374394378387179129 37376102530795783790384347)
        ·
          refine ⟨56064153796193675685576521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37376102530795783790384347 56064153796193675685576521)
          ·
            refine ⟨42048115347145256764182391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56064153796193675685576521 42048115347145256764182391)
            ·
              refine ⟨63072173020717885146273587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42048115347145256764182391 63072173020717885146273587)
              ·
                refine ⟨94608259531076827719410381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63072173020717885146273587 94608259531076827719410381)
                ·
                  refine ⟨35478097324153810394778893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94608259531076827719410381 35478097324153810394778893)
                  ·
                    refine ⟨13304286496557678898042085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35478097324153810394778893 13304286496557678898042085)
                    ·
                      refine ⟨2494553718104564793382891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13304286496557678898042085 2494553718104564793382891)
                      ·
                        rfl

theorem cell23_4858126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_4858126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858126 prefixEnd_4858126 := by exact prefixLift 4858126
  have htrace : WordTrace (prefixWord ++ tailWord_4858126) baseStart_4858126 baseEnd_4858126 := by
    simpa [prefixWord, tailWord_4858126, baseEnd_4858126] using wordTrace_append hprefix tailTrace_4858126
  have hstable : (prefixWord ++ tailWord_4858126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858126).length < 2 ^ (prefixWord ++ tailWord_4858126).sum := by decide
  have hdescent : baseEnd_4858126 < baseStart_4858126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858163 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 3]
def baseStart_4858163 : Nat := 118140960795 + 4858163 * 2 ^ 59
def prefixEnd_4858163 : Nat := 4983230072969 + 3 ^ 40 * 4858163 * 2
def baseEnd_4858163 : Nat := 2494572716888781148620221

theorem tailTrace_4858163 : CollatzResearch.WordTrace tailWord_4858163 prefixEnd_4858163 2494572716888781148620221 := by
  unfold tailWord_4858163
  simp only [CollatzResearch.WordTrace]
  refine ⟨177191761498712634029067143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118127840999141756019378095 177191761498712634029067143)
  ·
    refine ⟨265787642248068951043600715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177191761498712634029067143 265787642248068951043600715)
    ·
      refine ⟨398681463372103426565401073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265787642248068951043600715 398681463372103426565401073)
      ·
        refine ⟨299011097529077569924050805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398681463372103426565401073 299011097529077569924050805)
        ·
          refine ⟨28032290393351022180379763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 299011097529077569924050805 28032290393351022180379763)
          ·
            refine ⟨42048435590026533270569645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28032290393351022180379763 42048435590026533270569645)
            ·
              refine ⟨15768163346259949976463617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42048435590026533270569645 15768163346259949976463617)
              ·
                refine ⟨11826122509694962482347713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15768163346259949976463617 11826122509694962482347713)
                ·
                  refine ⟨8869591882271221861760785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11826122509694962482347713 8869591882271221861760785)
                  ·
                    refine ⟨6652193911703416396320589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8869591882271221861760785 6652193911703416396320589)
                    ·
                      refine ⟨2494572716888781148620221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6652193911703416396320589 2494572716888781148620221)
                      ·
                        rfl

theorem cell23_4858163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 3].length) (baseStart_4858163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858163 prefixEnd_4858163 := by exact prefixLift 4858163
  have htrace : WordTrace (prefixWord ++ tailWord_4858163) baseStart_4858163 baseEnd_4858163 := by
    simpa [prefixWord, tailWord_4858163, baseEnd_4858163] using wordTrace_append hprefix tailTrace_4858163
  have hstable : (prefixWord ++ tailWord_4858163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858163).length < 2 ^ (prefixWord ++ tailWord_4858163).sum := by decide
  have hdescent : baseEnd_4858163 < baseStart_4858163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858170 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 3, 4]
def baseStart_4858170 : Nat := 118140960795 + 4858170 * 2 ^ 59
def prefixEnd_4858170 : Nat := 4983230072969 + 3 ^ 40 * 4858170 * 2
def baseEnd_4858170 : Nat := 831525437084454207077563

theorem tailTrace_4858170 : CollatzResearch.WordTrace tailWord_4858170 prefixEnd_4858170 831525437084454207077563 := by
  unfold tailWord_4858170
  simp only [CollatzResearch.WordTrace]
  refine ⟨44298004202421818556142991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118128011206458182816381309 44298004202421818556142991)
  ·
    refine ⟨66447006303632727834214487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44298004202421818556142991 66447006303632727834214487)
    ·
      refine ⟨99670509455449091751321731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66447006303632727834214487 99670509455449091751321731)
      ·
        refine ⟨149505764183173637626982597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99670509455449091751321731 149505764183173637626982597)
        ·
          refine ⟨28032330784345057055059237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149505764183173637626982597 28032330784345057055059237)
          ·
            refine ⟨5256062022064698197823607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28032330784345057055059237 5256062022064698197823607)
            ·
              refine ⟨7884093033097047296735411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5256062022064698197823607 7884093033097047296735411)
              ·
                refine ⟨11826139549645570945103117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7884093033097047296735411 11826139549645570945103117)
                ·
                  refine ⟨4434802331117089104413669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11826139549645570945103117 4434802331117089104413669)
                  ·
                    refine ⟨831525437084454207077563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4434802331117089104413669 831525437084454207077563)
                    ·
                      rfl

theorem cell23_4858170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_4858170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858170 prefixEnd_4858170 := by exact prefixLift 4858170
  have htrace : WordTrace (prefixWord ++ tailWord_4858170) baseStart_4858170 baseEnd_4858170 := by
    simpa [prefixWord, tailWord_4858170, baseEnd_4858170] using wordTrace_append hprefix tailTrace_4858170
  have hstable : (prefixWord ++ tailWord_4858170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858170).length < 2 ^ (prefixWord ++ tailWord_4858170).sum := by decide
  have hdescent : baseEnd_4858170 < baseStart_4858170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858176 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 3]
def baseStart_4858176 : Nat := 118140960795 + 4858176 * 2 ^ 59
def prefixEnd_4858176 : Nat := 4983230072969 + 3 ^ 40 * 4858176 * 2
def baseEnd_4858176 : Nat := 2494579392137289597757661

theorem tailTrace_4858176 : CollatzResearch.WordTrace tailWord_4858176 prefixEnd_4858176 2494579392137289597757661 := by
  unfold tailWord_4858176
  simp only [CollatzResearch.WordTrace]
  refine ⟨88596117823832768624645191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118128157098443691499526921 88596117823832768624645191)
  ·
    refine ⟨132894176735749152936967787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88596117823832768624645191 132894176735749152936967787)
    ·
      refine ⟨199341265103623729405451681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132894176735749152936967787 199341265103623729405451681)
      ·
        refine ⟨149505948827717797054088761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199341265103623729405451681 149505948827717797054088761)
        ·
          refine ⟨112129461620788347790566571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149505948827717797054088761 112129461620788347790566571)
          ·
            refine ⟨168194192431182521685849857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112129461620788347790566571 168194192431182521685849857)
            ·
              refine ⟨126145644323386891264387393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168194192431182521685849857 126145644323386891264387393)
              ·
                refine ⟨94609233242540168448290545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126145644323386891264387393 94609233242540168448290545)
                ·
                  refine ⟨70956924931905126336217909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94609233242540168448290545 70956924931905126336217909)
                  ·
                    refine ⟨6652211712366105594020429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70956924931905126336217909 6652211712366105594020429)
                    ·
                      refine ⟨2494579392137289597757661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6652211712366105594020429 2494579392137289597757661)
                      ·
                        rfl

theorem cell23_4858176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_4858176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858176 prefixEnd_4858176 := by exact prefixLift 4858176
  have htrace : WordTrace (prefixWord ++ tailWord_4858176) baseStart_4858176 baseEnd_4858176 := by
    simpa [prefixWord, tailWord_4858176, baseEnd_4858176] using wordTrace_append hprefix tailTrace_4858176
  have hstable : (prefixWord ++ tailWord_4858176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858176).length < 2 ^ (prefixWord ++ tailWord_4858176).sum := by decide
  have hdescent : baseEnd_4858176 < baseStart_4858176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858233 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 2, 6, 2]
def baseStart_4858233 : Nat := 118140960795 + 4858233 * 2 ^ 59
def prefixEnd_4858233 : Nat := 4983230072969 + 3 ^ 40 * 4858233 * 2
def baseEnd_4858233 : Nat := 2494608660534595874744899

theorem tailTrace_4858233 : CollatzResearch.WordTrace tailWord_4858233 prefixEnd_4858233 2494608660534595874744899 := by
  unfold tailWord_4858233
  simp only [CollatzResearch.WordTrace]
  refine ⟨177194314608459035984115353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118129543072306023989410235 177194314608459035984115353)
  ·
    refine ⟨132895735956344276988086515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177194314608459035984115353 132895735956344276988086515)
    ·
      refine ⟨199343603934516415482129773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132895735956344276988086515 199343603934516415482129773)
      ·
        refine ⟨74753851475443655805798665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199343603934516415482129773 74753851475443655805798665)
        ·
          refine ⟨56065388606582741854348999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74753851475443655805798665 56065388606582741854348999)
          ·
            refine ⟨84098082909874112781523499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56065388606582741854348999 84098082909874112781523499)
            ·
              refine ⟨126147124364811169172285249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84098082909874112781523499 126147124364811169172285249)
              ·
                refine ⟨94610343273608376879213937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126147124364811169172285249 94610343273608376879213937)
                ·
                  refine ⟨70957757455206282659410453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94610343273608376879213937 70957757455206282659410453)
                  ·
                    refine ⟨3326144880712794499659865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70957757455206282659410453 3326144880712794499659865)
                    ·
                      refine ⟨2494608660534595874744899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3326144880712794499659865 2494608660534595874744899)
                      ·
                        rfl

theorem cell23_4858233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_4858233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858233 prefixEnd_4858233 := by exact prefixLift 4858233
  have htrace : WordTrace (prefixWord ++ tailWord_4858233) baseStart_4858233 baseEnd_4858233 := by
    simpa [prefixWord, tailWord_4858233, baseEnd_4858233] using wordTrace_append hprefix tailTrace_4858233
  have hstable : (prefixWord ++ tailWord_4858233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858233).length < 2 ^ (prefixWord ++ tailWord_4858233).sum := by decide
  have hdescent : baseEnd_4858233 < baseStart_4858233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858254 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2]
def baseStart_4858254 : Nat := 118140960795 + 4858254 * 2 ^ 59
def prefixEnd_4858254 : Nat := 4983230072969 + 3 ^ 40 * 4858254 * 2
def baseEnd_4858254 : Nat := 2494619443628340292582303

theorem tailTrace_4858254 : CollatzResearch.WordTrace tailWord_4858254 prefixEnd_4858254 2494619443628340292582303 := by
  unfold tailWord_4858254
  simp only [CollatzResearch.WordTrace]
  refine ⟨22149385067672869571328727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118130053694255304380419877 22149385067672869571328727)
  ·
    refine ⟨33224077601509304356993091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22149385067672869571328727 33224077601509304356993091)
    ·
      refine ⟨49836116402263956535489637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33224077601509304356993091 49836116402263956535489637)
      ·
        refine ⟨9344271825424491850404307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49836116402263956535489637 9344271825424491850404307)
        ·
          refine ⟨14016407738136737775606461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9344271825424491850404307 14016407738136737775606461)
          ·
            refine ⟨5256152901801276665852423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14016407738136737775606461 5256152901801276665852423)
            ·
              refine ⟨7884229352701914998778635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5256152901801276665852423 7884229352701914998778635)
              ·
                refine ⟨11826344029052872498167953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7884229352701914998778635 11826344029052872498167953)
                ·
                  refine ⟨8869758021789654373625965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11826344029052872498167953 8869758021789654373625965)
                  ·
                    refine ⟨3326159258171120390109737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8869758021789654373625965 3326159258171120390109737)
                    ·
                      refine ⟨2494619443628340292582303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3326159258171120390109737 2494619443628340292582303)
                      ·
                        rfl

theorem cell23_4858254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_4858254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858254 prefixEnd_4858254 := by exact prefixLift 4858254
  have htrace : WordTrace (prefixWord ++ tailWord_4858254) baseStart_4858254 baseEnd_4858254 := by
    simpa [prefixWord, tailWord_4858254, baseEnd_4858254] using wordTrace_append hprefix tailTrace_4858254
  have hstable : (prefixWord ++ tailWord_4858254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858254).length < 2 ^ (prefixWord ++ tailWord_4858254).sum := by decide
  have hdescent : baseEnd_4858254 < baseStart_4858254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858263 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_4858263 : Nat := 118140960795 + 4858263 * 2 ^ 59
def prefixEnd_4858263 : Nat := 4983230072969 + 3 ^ 40 * 4858263 * 2
def baseEnd_4858263 : Nat := 2494624064954230757369761

theorem tailTrace_4858263 : CollatzResearch.WordTrace tailWord_4858263 prefixEnd_4858263 2494624064954230757369761 := by
  unfold tailWord_4858263
  simp only [CollatzResearch.WordTrace]
  refine ⟨177195408798350351107707443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118130272532233567405138295 177195408798350351107707443)
  ·
    refine ⟨265793113197525526661561165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177195408798350351107707443 265793113197525526661561165)
    ·
      refine ⟨99672417449072072498085437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265793113197525526661561165 99672417449072072498085437)
      ·
        refine ⟨37377156543402027186782039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99672417449072072498085437 37377156543402027186782039)
        ·
          refine ⟨56065734815103040780173059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37377156543402027186782039 56065734815103040780173059)
          ·
            refine ⟨84098602222654561170259589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56065734815103040780173059 84098602222654561170259589)
            ·
              refine ⟨15768487916747730219423673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84098602222654561170259589 15768487916747730219423673)
              ·
                refine ⟨11826365937560797664567755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15768487916747730219423673 11826365937560797664567755)
                ·
                  refine ⟨17739548906341196496851633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11826365937560797664567755 17739548906341196496851633)
                  ·
                    refine ⟨13304661679755897372638725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17739548906341196496851633 13304661679755897372638725)
                    ·
                      refine ⟨2494624064954230757369761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13304661679755897372638725 2494624064954230757369761)
                      ·
                        rfl

theorem cell23_4858263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_4858263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858263 prefixEnd_4858263 := by exact prefixLift 4858263
  have htrace : WordTrace (prefixWord ++ tailWord_4858263) baseStart_4858263 baseEnd_4858263 := by
    simpa [prefixWord, tailWord_4858263, baseEnd_4858263] using wordTrace_append hprefix tailTrace_4858263
  have hstable : (prefixWord ++ tailWord_4858263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858263).length < 2 ^ (prefixWord ++ tailWord_4858263).sum := by decide
  have hdescent : baseEnd_4858263 < baseStart_4858263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858343 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_4858343 : Nat := 118140960795 + 4858343 * 2 ^ 59
def prefixEnd_4858343 : Nat := 4983230072969 + 3 ^ 40 * 4858343 * 2
def baseEnd_4858343 : Nat := 2494665143406590444369393

theorem tailTrace_4858343 : CollatzResearch.WordTrace tailWord_4858343 prefixEnd_4858343 2494665143406590444369393 := by
  unfold tailWord_4858343
  simp only [CollatzResearch.WordTrace]
  refine ⟨177198326638060524770619683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118132217758707016513746455 177198326638060524770619683)
  ·
    refine ⟨265797489957090787155929525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177198326638060524770619683 265797489957090787155929525)
    ·
      refine ⟨24918514683477261295868393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 265797489957090787155929525 24918514683477261295868393)
      ·
        refine ⟨18688886012607945971901295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24918514683477261295868393 18688886012607945971901295)
        ·
          refine ⟨28033329018911918957851943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18688886012607945971901295 28033329018911918957851943)
          ·
            refine ⟨42049993528367878436777915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28033329018911918957851943 42049993528367878436777915)
            ·
              refine ⟨63074990292551817655166873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42049993528367878436777915 63074990292551817655166873)
              ·
                refine ⟨47306242719413863241375155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63074990292551817655166873 47306242719413863241375155)
                ·
                  refine ⟨70959364079120794862062733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47306242719413863241375155 70959364079120794862062733)
                  ·
                    refine ⟨26609761529670298073273525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70959364079120794862062733 26609761529670298073273525)
                    ·
                      refine ⟨2494665143406590444369393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26609761529670298073273525 2494665143406590444369393)
                      ·
                        rfl

theorem cell23_4858343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_4858343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858343 prefixEnd_4858343 := by exact prefixLift 4858343
  have htrace : WordTrace (prefixWord ++ tailWord_4858343) baseStart_4858343 baseEnd_4858343 := by
    simpa [prefixWord, tailWord_4858343, baseEnd_4858343] using wordTrace_append hprefix tailTrace_4858343
  have hstable : (prefixWord ++ tailWord_4858343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858343).length < 2 ^ (prefixWord ++ tailWord_4858343).sum := by decide
  have hdescent : baseEnd_4858343 < baseStart_4858343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858353 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_4858353 : Nat := 118140960795 + 4858353 * 2 ^ 59
def prefixEnd_4858353 : Nat := 4983230072969 + 3 ^ 40 * 4858353 * 2
def baseEnd_4858353 : Nat := 2494670278213135405244347

theorem tailTrace_4858353 : CollatzResearch.WordTrace tailWord_4858353 prefixEnd_4858353 2494670278213135405244347 := by
  unfold tailWord_4858353
  simp only [CollatzResearch.WordTrace]
  refine ⟨177198691368024296478483713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118132460912016197652322475 177198691368024296478483713)
  ·
    refine ⟨132899018526018222358862785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177198691368024296478483713 132899018526018222358862785)
    ·
      refine ⟨99674263894513666769147089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132899018526018222358862785 99674263894513666769147089)
      ·
        refine ⟨74755697920885250076860317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99674263894513666769147089 74755697920885250076860317)
        ·
          refine ⟨28033386720331968778822619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74755697920885250076860317 28033386720331968778822619)
          ·
            refine ⟨42050080080497953168233929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28033386720331968778822619 42050080080497953168233929)
            ·
              refine ⟨31537560060373464876175447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42050080080497953168233929 31537560060373464876175447)
              ·
                refine ⟨47306340090560197314263171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31537560060373464876175447 47306340090560197314263171)
                ·
                  refine ⟨70959510135840295971394757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47306340090560197314263171 70959510135840295971394757)
                  ·
                    refine ⟨13304908150470055494636517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70959510135840295971394757 13304908150470055494636517)
                    ·
                      refine ⟨2494670278213135405244347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13304908150470055494636517 2494670278213135405244347)
                      ·
                        rfl

theorem cell23_4858353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_4858353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858353 prefixEnd_4858353 := by exact prefixLift 4858353
  have htrace : WordTrace (prefixWord ++ tailWord_4858353) baseStart_4858353 baseEnd_4858353 := by
    simpa [prefixWord, tailWord_4858353, baseEnd_4858353] using wordTrace_append hprefix tailTrace_4858353
  have hstable : (prefixWord ++ tailWord_4858353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858353).length < 2 ^ (prefixWord ++ tailWord_4858353).sum := by decide
  have hdescent : baseEnd_4858353 < baseStart_4858353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858397 : List Nat := [1, 4, 2, 2, 1, 3, 1, 4, 5]
def baseStart_4858397 : Nat := 118140960795 + 4858397 * 2 ^ 59
def prefixEnd_4858397 : Nat := 4983230072969 + 3 ^ 40 * 4858397 * 2
def baseEnd_4858397 : Nat := 277188096817992581454905

theorem tailTrace_4858397 : CollatzResearch.WordTrace tailWord_4858397 prefixEnd_4858397 277188096817992581454905 := by
  unfold tailWord_4858397
  simp only [CollatzResearch.WordTrace]
  refine ⟨177200296179864891993085445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118133530786576594662056963 177200296179864891993085445)
  ·
    refine ⟨33225055533724667248703521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177200296179864891993085445 33225055533724667248703521)
    ·
      refine ⟨24918791650293500436527641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33225055533724667248703521 24918791650293500436527641)
      ·
        refine ⟨18689093737720125327395731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24918791650293500436527641 18689093737720125327395731)
        ·
          refine ⟨28033640606580187991093597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18689093737720125327395731 28033640606580187991093597)
          ·
            refine ⟨10512615227467570496660099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28033640606580187991093597 10512615227467570496660099)
            ·
              refine ⟨15768922841201355744990149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10512615227467570496660099 15768922841201355744990149)
              ·
                refine ⟨2956673032725254202185653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15768922841201355744990149 2956673032725254202185653)
                ·
                  refine ⟨277188096817992581454905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2956673032725254202185653 277188096817992581454905)
                  ·
                    rfl

theorem cell23_4858397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_4858397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858397 prefixEnd_4858397 := by exact prefixLift 4858397
  have htrace : WordTrace (prefixWord ++ tailWord_4858397) baseStart_4858397 baseEnd_4858397 := by
    simpa [prefixWord, tailWord_4858397, baseEnd_4858397] using wordTrace_append hprefix tailTrace_4858397
  have hstable : (prefixWord ++ tailWord_4858397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858397).length < 2 ^ (prefixWord ++ tailWord_4858397).sum := by decide
  have hdescent : baseEnd_4858397 < baseStart_4858397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858443 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 6]
def baseStart_4858443 : Nat := 118140960795 + 4858443 * 2 ^ 59
def prefixEnd_4858443 : Nat := 4983230072969 + 3 ^ 40 * 4858443 * 2
def baseEnd_4858443 : Nat := 2494716491472040053118933

theorem tailTrace_4858443 : CollatzResearch.WordTrace tailWord_4858443 prefixEnd_4858443 2494716491472040053118933 := by
  unfold tailWord_4858443
  simp only [CollatzResearch.WordTrace]
  refine ⟨177201973937698241849259983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118134649291798827899506655 177201973937698241849259983)
  ·
    refine ⟨265802960906547362773889975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177201973937698241849259983 265802960906547362773889975)
    ·
      refine ⟨398704441359821044160834963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265802960906547362773889975 398704441359821044160834963)
      ·
        refine ⟨598056662039731566241252445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398704441359821044160834963 598056662039731566241252445)
        ·
          refine ⟨224271248264899337340469667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 598056662039731566241252445 224271248264899337340469667)
          ·
            refine ⟨336406872397349006010704501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224271248264899337340469667 336406872397349006010704501)
            ·
              refine ⟨31538144287251469313503547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 336406872397349006010704501 31538144287251469313503547)
              ·
                refine ⟨47307216430877203970255321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31538144287251469313503547 47307216430877203970255321)
                ·
                  refine ⟨35480412323157902977691491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47307216430877203970255321 35480412323157902977691491)
                  ·
                    refine ⟨53220618484736854466537237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35480412323157902977691491 53220618484736854466537237)
                    ·
                      refine ⟨2494716491472040053118933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53220618484736854466537237 2494716491472040053118933)
                      ·
                        rfl

theorem cell23_4858443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 6].length) (baseStart_4858443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858443 prefixEnd_4858443 := by exact prefixLift 4858443
  have htrace : WordTrace (prefixWord ++ tailWord_4858443) baseStart_4858443 baseEnd_4858443 := by
    simpa [prefixWord, tailWord_4858443, baseEnd_4858443] using wordTrace_append hprefix tailTrace_4858443
  have hstable : (prefixWord ++ tailWord_4858443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858443).length < 2 ^ (prefixWord ++ tailWord_4858443).sum := by decide
  have hdescent : baseEnd_4858443 < baseStart_4858443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858473 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 6]
def baseStart_4858473 : Nat := 118140960795 + 4858473 * 2 ^ 59
def prefixEnd_4858473 : Nat := 4983230072969 + 3 ^ 40 * 4858473 * 2
def baseEnd_4858473 : Nat := 2494731895891674935743795

theorem tailTrace_4858473 : CollatzResearch.WordTrace tailWord_4858473 prefixEnd_4858473 2494731895891674935743795 := by
  unfold tailWord_4858473
  simp only [CollatzResearch.WordTrace]
  refine ⟨177203068127589556972852073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118135378751726371315234715 177203068127589556972852073)
  ·
    refine ⟨132902301095692167729639055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177203068127589556972852073 132902301095692167729639055)
    ·
      refine ⟨199353451643538251594458583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132902301095692167729639055 199353451643538251594458583)
      ·
        refine ⟨299030177465307377391687875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199353451643538251594458583 299030177465307377391687875)
        ·
          refine ⟨448545266197961066087531813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299030177465307377391687875 448545266197961066087531813)
          ·
            refine ⟨84102237412117699891412215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 448545266197961066087531813 84102237412117699891412215)
            ·
              refine ⟨126153356118176549837118323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84102237412117699891412215 126153356118176549837118323)
              ·
                refine ⟨189230034177264824755677485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126153356118176549837118323 189230034177264824755677485)
                ·
                  refine ⟨70961262816474309283379057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189230034177264824755677485 70961262816474309283379057)
                  ·
                    refine ⟨53220947112355731962534293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70961262816474309283379057 53220947112355731962534293)
                    ·
                      refine ⟨2494731895891674935743795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53220947112355731962534293 2494731895891674935743795)
                      ·
                        rfl

theorem cell23_4858473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_4858473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858473 prefixEnd_4858473 := by exact prefixLift 4858473
  have htrace : WordTrace (prefixWord ++ tailWord_4858473) baseStart_4858473 baseEnd_4858473 := by
    simpa [prefixWord, tailWord_4858473, baseEnd_4858473] using wordTrace_append hprefix tailTrace_4858473
  have hstable : (prefixWord ++ tailWord_4858473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858473).length < 2 ^ (prefixWord ++ tailWord_4858473).sum := by decide
  have hdescent : baseEnd_4858473 < baseStart_4858473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858498 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4858498 : Nat := 118140960795 + 4858498 * 2 ^ 59
def prefixEnd_4858498 : Nat := 4983230072969 + 3 ^ 40 * 4858498 * 2
def baseEnd_4858498 : Nat := 2494744732908037337931181

theorem tailTrace_4858498 : CollatzResearch.WordTrace tailWord_4858498 prefixEnd_4858498 2494744732908037337931181 := by
  unfold tailWord_4858498
  simp only [CollatzResearch.WordTrace]
  refine ⟨44300994988124746560628037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118135986634999324161674765 44300994988124746560628037)
  ·
    refine ⟨8306436560273389980117757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44300994988124746560628037 8306436560273389980117757)
    ·
      refine ⟨3114913710102521242544159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8306436560273389980117757 3114913710102521242544159)
      ·
        refine ⟨4672370565153781863816239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3114913710102521242544159 4672370565153781863816239)
        ·
          refine ⟨7008555847730672795724359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4672370565153781863816239 7008555847730672795724359)
          ·
            refine ⟨10512833771596009193586539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7008555847730672795724359 10512833771596009193586539)
            ·
              refine ⟨15769250657394013790379809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10512833771596009193586539 15769250657394013790379809)
              ·
                refine ⟨11826937993045510342784857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15769250657394013790379809 11826937993045510342784857)
                ·
                  refine ⟨8870203494784132757088643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11826937993045510342784857 8870203494784132757088643)
                  ·
                    refine ⟨13305305242176199135632965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8870203494784132757088643 13305305242176199135632965)
                    ·
                      refine ⟨2494744732908037337931181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13305305242176199135632965 2494744732908037337931181)
                      ·
                        rfl

theorem cell23_4858498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4858498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858498 prefixEnd_4858498 := by exact prefixLift 4858498
  have htrace : WordTrace (prefixWord ++ tailWord_4858498) baseStart_4858498 baseEnd_4858498 := by
    simpa [prefixWord, tailWord_4858498, baseEnd_4858498] using wordTrace_append hprefix tailTrace_4858498
  have hstable : (prefixWord ++ tailWord_4858498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858498).length < 2 ^ (prefixWord ++ tailWord_4858498).sum := by decide
  have hdescent : baseEnd_4858498 < baseStart_4858498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858541 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_4858541 : Nat := 118140960795 + 4858541 * 2 ^ 59
def prefixEnd_4858541 : Nat := 4983230072969 + 3 ^ 40 * 4858541 * 2
def baseEnd_4858541 : Nat := 2494766812576180669693483

theorem tailTrace_4858541 : CollatzResearch.WordTrace tailWord_4858541 prefixEnd_4858541 2494766812576180669693483 := by
  unfold tailWord_4858541
  simp only [CollatzResearch.WordTrace]
  refine ⟨177205548291343204586327477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118137032194228803057551651 177205548291343204586327477)
  ·
    refine ⟨16613020152313425429968201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177205548291343204586327477 16613020152313425429968201)
    ·
      refine ⟨12459765114235069072476151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16613020152313425429968201 12459765114235069072476151)
      ·
        refine ⟨18689647671352603608714227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12459765114235069072476151 18689647671352603608714227)
        ·
          refine ⟨28034471507028905413071341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18689647671352603608714227 28034471507028905413071341)
          ·
            refine ⟨10512926815135839529901753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28034471507028905413071341 10512926815135839529901753)
            ·
              refine ⟨7884695111351879647426315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10512926815135839529901753 7884695111351879647426315)
              ·
                refine ⟨11827042667027819471139473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7884695111351879647426315 11827042667027819471139473)
                ·
                  refine ⟨8870282000270864603354605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11827042667027819471139473 8870282000270864603354605)
                  ·
                    refine ⟨3326355750101574226257977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8870282000270864603354605 3326355750101574226257977)
                    ·
                      refine ⟨2494766812576180669693483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3326355750101574226257977 2494766812576180669693483)
                      ·
                        rfl

theorem cell23_4858541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_4858541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858541 prefixEnd_4858541 := by exact prefixLift 4858541
  have htrace : WordTrace (prefixWord ++ tailWord_4858541) baseStart_4858541 baseEnd_4858541 := by
    simpa [prefixWord, tailWord_4858541, baseEnd_4858541] using wordTrace_append hprefix tailTrace_4858541
  have hstable : (prefixWord ++ tailWord_4858541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858541).length < 2 ^ (prefixWord ++ tailWord_4858541).sum := by decide
  have hdescent : baseEnd_4858541 < baseStart_4858541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858554 : List Nat := [3, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4]
def baseStart_4858554 : Nat := 118140960795 + 4858554 * 2 ^ 59
def prefixEnd_4858554 : Nat := 4983230072969 + 3 ^ 40 * 4858554 * 2
def baseEnd_4858554 : Nat := 2494773487824689118830923

theorem tailTrace_4858554 : CollatzResearch.WordTrace tailWord_4858554 prefixEnd_4858554 2494773487824689118830923 := by
  unfold tailWord_4858554
  simp only [CollatzResearch.WordTrace]
  refine ⟨44301505610074026951637679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118137348293530738537700477 44301505610074026951637679)
  ·
    refine ⟨66452258415111040427456519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44301505610074026951637679 66452258415111040427456519)
    ·
      refine ⟨99678387622666560641184779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66452258415111040427456519 99678387622666560641184779)
      ·
        refine ⟨149517581433999840961777169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99678387622666560641184779 149517581433999840961777169)
        ·
          refine ⟨112138186075499880721332877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149517581433999840961777169 112138186075499880721332877)
          ·
            refine ⟨42051819778312455270499829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112138186075499880721332877 42051819778312455270499829)
            ·
              refine ⟨3942358104216792681609359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42051819778312455270499829 3942358104216792681609359)
              ·
                refine ⟨5913537156325189022414039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3942358104216792681609359 5913537156325189022414039)
                ·
                  refine ⟨8870305734487783533621059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5913537156325189022414039 8870305734487783533621059)
                  ·
                    refine ⟨13305458601731675300431589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8870305734487783533621059 13305458601731675300431589)
                    ·
                      refine ⟨2494773487824689118830923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13305458601731675300431589 2494773487824689118830923)
                      ·
                        rfl

theorem cell23_4858554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4].length) (baseStart_4858554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858554 prefixEnd_4858554 := by exact prefixLift 4858554
  have htrace : WordTrace (prefixWord ++ tailWord_4858554) baseStart_4858554 baseEnd_4858554 := by
    simpa [prefixWord, tailWord_4858554, baseEnd_4858554] using wordTrace_append hprefix tailTrace_4858554
  have hstable : (prefixWord ++ tailWord_4858554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858554).length < 2 ^ (prefixWord ++ tailWord_4858554).sum := by decide
  have hdescent : baseEnd_4858554 < baseStart_4858554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858557 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_4858557 : Nat := 118140960795 + 4858557 * 2 ^ 59
def prefixEnd_4858557 : Nat := 4983230072969 + 3 ^ 40 * 4858557 * 2
def baseEnd_4858557 : Nat := 2494775028266652607093409

theorem tailTrace_4858557 : CollatzResearch.WordTrace tailWord_4858557 prefixEnd_4858557 2494775028266652607093409 := by
  unfold tailWord_4858557
  simp only [CollatzResearch.WordTrace]
  refine ⟨177206131859285239318909925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118137421239523492879273283 177206131859285239318909925)
  ·
    refine ⟨33226149723615982372295611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177206131859285239318909925 33226149723615982372295611)
    ·
      refine ⟨49839224585423973558443417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33226149723615982372295611 49839224585423973558443417)
      ·
        refine ⟨37379418439067980168832563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49839224585423973558443417 37379418439067980168832563)
        ·
          refine ⟨56069127658601970253248845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37379418439067980168832563 56069127658601970253248845)
          ·
            refine ⟨21025922871975738844968317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56069127658601970253248845 21025922871975738844968317)
            ·
              refine ⟨7884721076990902066863119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21025922871975738844968317 7884721076990902066863119)
              ·
                refine ⟨11827081615486353100294679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7884721076990902066863119 11827081615486353100294679)
                ·
                  refine ⟨17740622423229529650442019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11827081615486353100294679 17740622423229529650442019)
                  ·
                    refine ⟨26610933634844294475663029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17740622423229529650442019 26610933634844294475663029)
                    ·
                      refine ⟨2494775028266652607093409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26610933634844294475663029 2494775028266652607093409)
                      ·
                        rfl

theorem cell23_4858557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_4858557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858557 prefixEnd_4858557 := by exact prefixLift 4858557
  have htrace : WordTrace (prefixWord ++ tailWord_4858557) baseStart_4858557 baseEnd_4858557 := by
    simpa [prefixWord, tailWord_4858557, baseEnd_4858557] using wordTrace_append hprefix tailTrace_4858557
  have hstable : (prefixWord ++ tailWord_4858557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858557).length < 2 ^ (prefixWord ++ tailWord_4858557).sum := by decide
  have hdescent : baseEnd_4858557 < baseStart_4858557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858564 : List Nat := [2, 3, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_4858564 : Nat := 118140960795 + 4858564 * 2 ^ 59
def prefixEnd_4858564 : Nat := 4983230072969 + 3 ^ 40 * 4858564 * 2
def baseEnd_4858564 : Nat := 831592874210411359901959

theorem tailTrace_4858564 : CollatzResearch.WordTrace tailWord_4858564 prefixEnd_4858564 831592874210411359901959 := by
  unfold tailWord_4858564
  simp only [CollatzResearch.WordTrace]
  refine ⟨88603193585129939757207373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118137591446839919676276497 88603193585129939757207373)
  ·
    refine ⟨33226197594423727408952765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88603193585129939757207373 33226197594423727408952765)
    ·
      refine ⟨12459824097908897778357287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33226197594423727408952765 12459824097908897778357287)
      ·
        refine ⟨18689736146863346667535931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12459824097908897778357287 18689736146863346667535931)
        ·
          refine ⟨28034604220295020001303897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18689736146863346667535931 28034604220295020001303897)
          ·
            refine ⟨21025953165221265000977923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28034604220295020001303897 21025953165221265000977923)
            ·
              refine ⟨31538929747831897501466885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21025953165221265000977923 31538929747831897501466885)
              ·
                refine ⟨5913549327718480781525041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31538929747831897501466885 5913549327718480781525041)
                ·
                  refine ⟨4435161995788860586143781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5913549327718480781525041 4435161995788860586143781)
                  ·
                    refine ⟨831592874210411359901959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4435161995788860586143781 831592874210411359901959)
                    ·
                      rfl

theorem cell23_4858564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_4858564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858564 prefixEnd_4858564 := by exact prefixLift 4858564
  have htrace : WordTrace (prefixWord ++ tailWord_4858564) baseStart_4858564 baseEnd_4858564 := by
    simpa [prefixWord, tailWord_4858564, baseEnd_4858564] using wordTrace_append hprefix tailTrace_4858564
  have hstable : (prefixWord ++ tailWord_4858564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858564).length < 2 ^ (prefixWord ++ tailWord_4858564).sum := by decide
  have hdescent : baseEnd_4858564 < baseStart_4858564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858588 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_4858588 : Nat := 118140960795 + 4858588 * 2 ^ 59
def prefixEnd_4858588 : Nat := 4983230072969 + 3 ^ 40 * 4858588 * 2
def baseEnd_4858588 : Nat := 2494790946166941985805767

theorem tailTrace_4858588 : CollatzResearch.WordTrace tailWord_4858588 prefixEnd_4858588 2494790946166941985805767 := by
  unfold tailWord_4858588
  simp only [CollatzResearch.WordTrace]
  refine ⟨88603631261086465806644209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118138175014781954408858945 88603631261086465806644209)
  ·
    refine ⟨66452723445814849354983157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88603631261086465806644209 66452723445814849354983157)
    ·
      refine ⟨6229942823045142127029671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66452723445814849354983157 6229942823045142127029671)
      ·
        refine ⟨9344914234567713190544507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6229942823045142127029671 9344914234567713190544507)
        ·
          refine ⟨14017371351851569785816761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9344914234567713190544507 14017371351851569785816761)
          ·
            refine ⟨10513028513888677339362571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14017371351851569785816761 10513028513888677339362571)
            ·
              refine ⟨15769542770833016009043857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10513028513888677339362571 15769542770833016009043857)
              ·
                refine ⟨11827157078124762006782893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15769542770833016009043857 11827157078124762006782893)
                ·
                  refine ⟨4435183904296785752543585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11827157078124762006782893 4435183904296785752543585)
                  ·
                    refine ⟨3326387928222589314407689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4435183904296785752543585 3326387928222589314407689)
                    ·
                      refine ⟨2494790946166941985805767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3326387928222589314407689 2494790946166941985805767)
                      ·
                        rfl

theorem cell23_4858588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_4858588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858588 prefixEnd_4858588 := by exact prefixLift 4858588
  have htrace : WordTrace (prefixWord ++ tailWord_4858588) baseStart_4858588 baseEnd_4858588 := by
    simpa [prefixWord, tailWord_4858588, baseEnd_4858588] using wordTrace_append hprefix tailTrace_4858588
  have hstable : (prefixWord ++ tailWord_4858588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858588).length < 2 ^ (prefixWord ++ tailWord_4858588).sum := by decide
  have hdescent : baseEnd_4858588 < baseStart_4858588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858714 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 2, 5]
def baseStart_4858714 : Nat := 118140960795 + 4858714 * 2 ^ 59
def prefixEnd_4858714 : Nat := 4983230072969 + 3 ^ 40 * 4858714 * 2
def baseEnd_4858714 : Nat := 831618548243136164276729

theorem tailTrace_4858714 : CollatzResearch.WordTrace tailWord_4858714 prefixEnd_4858714 831618548243136164276729 := by
  unfold tailWord_4858714
  simp only [CollatzResearch.WordTrace]
  refine ⟨44302964529929113783093799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118141238746477636754916797 44302964529929113783093799)
  ·
    refine ⟨66454446794893670674640699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44302964529929113783093799 66454446794893670674640699)
    ·
      refine ⟨99681670192340506011961049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66454446794893670674640699 99681670192340506011961049)
      ·
        refine ⟨74761252644255379508970787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99681670192340506011961049 74761252644255379508970787)
        ·
          refine ⟨112141878966383069263456181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74761252644255379508970787 112141878966383069263456181)
          ·
            refine ⟨10513301153098412743449017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112141878966383069263456181 10513301153098412743449017)
            ·
              refine ⟨7884975864823809557586763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10513301153098412743449017 7884975864823809557586763)
              ·
                refine ⟨11827463797235714336380145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7884975864823809557586763 11827463797235714336380145)
                ·
                  refine ⟨8870597847926785752285109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11827463797235714336380145 8870597847926785752285109)
                  ·
                    refine ⟨831618548243136164276729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8870597847926785752285109 831618548243136164276729)
                    ·
                      rfl

theorem cell23_4858714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_4858714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858714 prefixEnd_4858714 := by exact prefixLift 4858714
  have htrace : WordTrace (prefixWord ++ tailWord_4858714) baseStart_4858714 baseEnd_4858714 := by
    simpa [prefixWord, tailWord_4858714, baseEnd_4858714] using wordTrace_append hprefix tailTrace_4858714
  have hstable : (prefixWord ++ tailWord_4858714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858714).length < 2 ^ (prefixWord ++ tailWord_4858714).sum := by decide
  have hdescent : baseEnd_4858714 < baseStart_4858714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858838 : List Nat := [5, 2, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_4858838 : Nat := 118140960795 + 4858838 * 2 ^ 59
def prefixEnd_4858838 : Nat := 4983230072969 + 3 ^ 40 * 4858838 * 2
def baseEnd_4858838 : Nat := 831639772110188669226539

theorem tailTrace_4858838 : CollatzResearch.WordTrace tailWord_4858838 prefixEnd_4858838 831639772110188669226539 := by
  unfold tailWord_4858838
  simp only [CollatzResearch.WordTrace]
  refine ⟨11076023798204201519368073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118144253847511482873259445 11076023798204201519368073)
  ·
    refine ⟨8307017848653151139526055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11076023798204201519368073 8307017848653151139526055)
    ·
      refine ⟨12460526772979726709289083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8307017848653151139526055 12460526772979726709289083)
      ·
        refine ⟨18690790159469590063933625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12460526772979726709289083 18690790159469590063933625)
        ·
          refine ⟨14018092619602192547950219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18690790159469590063933625 14018092619602192547950219)
          ·
            refine ⟨21027138929403288821925329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14018092619602192547950219 21027138929403288821925329)
            ·
              refine ⟨15770354197052466616443997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21027138929403288821925329 15770354197052466616443997)
              ·
                refine ⟨5913882823894674981166499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15770354197052466616443997 5913882823894674981166499)
                ·
                  refine ⟨8870824235842012471749749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5913882823894674981166499 8870824235842012471749749)
                  ·
                    refine ⟨831639772110188669226539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8870824235842012471749749 831639772110188669226539)
                    ·
                      rfl

theorem cell23_4858838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_4858838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858838 prefixEnd_4858838 := by exact prefixLift 4858838
  have htrace : WordTrace (prefixWord ++ tailWord_4858838) baseStart_4858838 baseEnd_4858838 := by
    simpa [prefixWord, tailWord_4858838, baseEnd_4858838] using wordTrace_append hprefix tailTrace_4858838
  have hstable : (prefixWord ++ tailWord_4858838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858838).length < 2 ^ (prefixWord ++ tailWord_4858838).sum := by decide
  have hdescent : baseEnd_4858838 < baseStart_4858838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858841 : List Nat := [1, 2, 1, 2, 5, 1, 2, 3, 1, 1, 4]
def baseStart_4858841 : Nat := 118140960795 + 4858841 * 2 ^ 59
def prefixEnd_4858841 : Nat := 4983230072969 + 3 ^ 40 * 4858841 * 2
def baseEnd_4858841 : Nat := 2494920856772529495942103

theorem tailTrace_4858841 : CollatzResearch.WordTrace tailWord_4858841 prefixEnd_4858841 2494920856772529495942103 := by
  unfold tailWord_4858841
  simp only [CollatzResearch.WordTrace]
  refine ⟨177216490190256355822248377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118144326793504237214832251 177216490190256355822248377)
  ·
    refine ⟨132912367642692266866686283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177216490190256355822248377 132912367642692266866686283)
    ·
      refine ⟨199368551464038400300029425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132912367642692266866686283 199368551464038400300029425)
      ·
        refine ⟨149526413598028800225022069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199368551464038400300029425 149526413598028800225022069)
        ·
          refine ⟨14018101274815200021095819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149526413598028800225022069 14018101274815200021095819)
          ·
            refine ⟨21027151912222800031643729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14018101274815200021095819 21027151912222800031643729)
            ·
              refine ⟨15770363934167100023732797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21027151912222800031643729 15770363934167100023732797)
              ·
                refine ⟨5913886475312662508899799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15770363934167100023732797 5913886475312662508899799)
                ·
                  refine ⟨8870829712968993763349699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5913886475312662508899799 8870829712968993763349699)
                  ·
                    refine ⟨13306244569453490645024549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8870829712968993763349699 13306244569453490645024549)
                    ·
                      refine ⟨2494920856772529495942103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13306244569453490645024549 2494920856772529495942103)
                      ·
                        rfl

theorem cell23_4858841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_4858841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858841 prefixEnd_4858841 := by exact prefixLift 4858841
  have htrace : WordTrace (prefixWord ++ tailWord_4858841) baseStart_4858841 baseEnd_4858841 := by
    simpa [prefixWord, tailWord_4858841, baseEnd_4858841] using wordTrace_append hprefix tailTrace_4858841
  have hstable : (prefixWord ++ tailWord_4858841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858841).length < 2 ^ (prefixWord ++ tailWord_4858841).sum := by decide
  have hdescent : baseEnd_4858841 < baseStart_4858841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858851 : List Nat := [1, 1, 1, 6, 1, 1, 2, 4, 2, 4]
def baseStart_4858851 : Nat := 118140960795 + 4858851 * 2 ^ 59
def prefixEnd_4858851 : Nat := 4983230072969 + 3 ^ 40 * 4858851 * 2
def baseEnd_4858851 : Nat := 831641997193024818939019

theorem tailTrace_4858851 : CollatzResearch.WordTrace tailWord_4858851 prefixEnd_4858851 831641997193024818939019 := by
  unfold tailWord_4858851
  simp only [CollatzResearch.WordTrace]
  refine ⟨177216854920220127530112407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118144569946813418353408271 177216854920220127530112407)
  ·
    refine ⟨265825282380330191295168611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177216854920220127530112407 265825282380330191295168611)
    ·
      refine ⟨398737923570495286942752917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265825282380330191295168611 398737923570495286942752917)
      ·
        refine ⟨18690840167366966575441543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 398737923570495286942752917 18690840167366966575441543)
        ·
          refine ⟨28036260251050449863162315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18690840167366966575441543 28036260251050449863162315)
          ·
            refine ⟨42054390376575674794743473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28036260251050449863162315 42054390376575674794743473)
            ·
              refine ⟨31540792782431756096057605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42054390376575674794743473 31540792782431756096057605)
              ·
                refine ⟨5913898646705954268010801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31540792782431756096057605 5913898646705954268010801)
                ·
                  refine ⟨4435423985029465701008101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5913898646705954268010801 4435423985029465701008101)
                  ·
                    refine ⟨831641997193024818939019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4435423985029465701008101 831641997193024818939019)
                    ·
                      rfl

theorem cell23_4858851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 4].length) (baseStart_4858851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858851 prefixEnd_4858851 := by exact prefixLift 4858851
  have htrace : WordTrace (prefixWord ++ tailWord_4858851) baseStart_4858851 baseEnd_4858851 := by
    simpa [prefixWord, tailWord_4858851, baseEnd_4858851] using wordTrace_append hprefix tailTrace_4858851
  have hstable : (prefixWord ++ tailWord_4858851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858851).length < 2 ^ (prefixWord ++ tailWord_4858851).sum := by decide
  have hdescent : baseEnd_4858851 < baseStart_4858851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858874 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3]
def baseStart_4858874 : Nat := 118140960795 + 4858874 * 2 ^ 59
def prefixEnd_4858874 : Nat := 4983230072969 + 3 ^ 40 * 4858874 * 2
def baseEnd_4858874 : Nat := 2494937801634127866829451

theorem tailTrace_4858874 : CollatzResearch.WordTrace tailWord_4858874 prefixEnd_4858874 2494937801634127866829451 := by
  unfold tailWord_4858874
  simp only [CollatzResearch.WordTrace]
  refine ⟨44304423449784200614549919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118145129199424534972133117 44304423449784200614549919)
  ·
    refine ⟨66456635174676300921824879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44304423449784200614549919 66456635174676300921824879)
    ·
      refine ⟨99684952762014451382737319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66456635174676300921824879 99684952762014451382737319)
      ·
        refine ⟨149527429143021677074105979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99684952762014451382737319 149527429143021677074105979)
        ·
          refine ⟨224291143714532515611158969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149527429143021677074105979 224291143714532515611158969)
          ·
            refine ⟨168218357785899386708369227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224291143714532515611158969 168218357785899386708369227)
            ·
              refine ⟨252327536678849080062553841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168218357785899386708369227 252327536678849080062553841)
              ·
                refine ⟨189245652509136810046915381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252327536678849080062553841 189245652509136810046915381)
                ·
                  refine ⟨17741779922731575941898317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 189245652509136810046915381 17741779922731575941898317)
                  ·
                    refine ⟨6653167471024340978211869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17741779922731575941898317 6653167471024340978211869)
                    ·
                      refine ⟨2494937801634127866829451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6653167471024340978211869 2494937801634127866829451)
                      ·
                        rfl

theorem cell23_4858874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_4858874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858874 prefixEnd_4858874 := by exact prefixLift 4858874
  have htrace : WordTrace (prefixWord ++ tailWord_4858874) baseStart_4858874 baseEnd_4858874 := by
    simpa [prefixWord, tailWord_4858874, baseEnd_4858874] using wordTrace_append hprefix tailTrace_4858874
  have hstable : (prefixWord ++ tailWord_4858874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858874).length < 2 ^ (prefixWord ++ tailWord_4858874).sum := by decide
  have hdescent : baseEnd_4858874 < baseStart_4858874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858891 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 3]
def baseStart_4858891 : Nat := 118140960795 + 4858891 * 2 ^ 59
def prefixEnd_4858891 : Nat := 4983230072969 + 3 ^ 40 * 4858891 * 2
def baseEnd_4858891 : Nat := 2494946530805254300316873

theorem tailTrace_4858891 : CollatzResearch.WordTrace tailWord_4858891 prefixEnd_4858891 2494946530805254300316873 := by
  unfold tailWord_4858891
  simp only [CollatzResearch.WordTrace]
  refine ⟨177218313840075214361568527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118145542560050142907712351 177218313840075214361568527)
  ·
    refine ⟨265827470760112821542352791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177218313840075214361568527 265827470760112821542352791)
    ·
      refine ⟨398741206140169232313529187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265827470760112821542352791 398741206140169232313529187)
      ·
        refine ⟨598111809210253848470293781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398741206140169232313529187 598111809210253848470293781)
        ·
          refine ⟨28036491056730649147045021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 598111809210253848470293781 28036491056730649147045021)
          ·
            refine ⟨10513684146273993430141883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28036491056730649147045021 10513684146273993430141883)
            ·
              refine ⟨15770526219410990145212825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10513684146273993430141883 15770526219410990145212825)
              ·
                refine ⟨11827894664558242608909619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15770526219410990145212825 11827894664558242608909619)
                ·
                  refine ⟨17741841996837363913364429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11827894664558242608909619 17741841996837363913364429)
                  ·
                    refine ⟨6653190748814011467511661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17741841996837363913364429 6653190748814011467511661)
                    ·
                      refine ⟨2494946530805254300316873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6653190748814011467511661 2494946530805254300316873)
                      ·
                        rfl

theorem cell23_4858891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 3].length) (baseStart_4858891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858891 prefixEnd_4858891 := by exact prefixLift 4858891
  have htrace : WordTrace (prefixWord ++ tailWord_4858891) baseStart_4858891 baseEnd_4858891 := by
    simpa [prefixWord, tailWord_4858891, baseEnd_4858891] using wordTrace_append hprefix tailTrace_4858891
  have hstable : (prefixWord ++ tailWord_4858891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858891).length < 2 ^ (prefixWord ++ tailWord_4858891).sum := by decide
  have hdescent : baseEnd_4858891 < baseStart_4858891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858898 : List Nat := [3, 2, 5, 1, 1, 11]
def baseStart_4858898 : Nat := 118140960795 + 4858898 * 2 ^ 59
def prefixEnd_4858898 : Nat := 4983230072969 + 3 ^ 40 * 4858898 * 2
def baseEnd_4858898 : Nat := 10267284465719488777487

theorem tailTrace_4858898 : CollatzResearch.WordTrace tailWord_4858898 prefixEnd_4858898 10267284465719488777487 := by
  unfold tailWord_4858898
  simp only [CollatzResearch.WordTrace]
  refine ⟨44304642287762463639268337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118145712767366569704715565 44304642287762463639268337)
  ·
    refine ⟨33228481715821847729451253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44304642287762463639268337 33228481715821847729451253)
    ·
      refine ⟨3115170160858298224636055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33228481715821847729451253 3115170160858298224636055)
      ·
        refine ⟨4672755241287447336954083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3115170160858298224636055 4672755241287447336954083)
        ·
          refine ⟨7009132861931171005431125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4672755241287447336954083 7009132861931171005431125)
          ·
            refine ⟨10267284465719488777487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7009132861931171005431125 10267284465719488777487)
            ·
              rfl

theorem cell23_4858898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 11].length) (baseStart_4858898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858898 prefixEnd_4858898 := by exact prefixLift 4858898
  have htrace : WordTrace (prefixWord ++ tailWord_4858898) baseStart_4858898 baseEnd_4858898 := by
    simpa [prefixWord, tailWord_4858898, baseEnd_4858898] using wordTrace_append hprefix tailTrace_4858898
  have hstable : (prefixWord ++ tailWord_4858898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858898).length < 2 ^ (prefixWord ++ tailWord_4858898).sum := by decide
  have hdescent : baseEnd_4858898 < baseStart_4858898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858924 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 2, 6]
def baseStart_4858924 : Nat := 118140960795 + 4858924 * 2 ^ 59
def prefixEnd_4858924 : Nat := 4983230072969 + 3 ^ 40 * 4858924 * 2
def baseEnd_4858924 : Nat := 831654491888950890401407

theorem tailTrace_4858924 : CollatzResearch.WordTrace tailWord_4858924 prefixEnd_4858924 831654491888950890401407 := by
  unfold tailWord_4858924
  simp only [CollatzResearch.WordTrace]
  refine ⟨88609758724477830498759913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118146344965970440665013217 88609758724477830498759913)
  ·
    refine ⟨66457319043358372874069935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88609758724477830498759913 66457319043358372874069935)
    ·
      refine ⟨99685978565037559311104903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66457319043358372874069935 99685978565037559311104903)
      ·
        refine ⟨149528967847556338966657355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99685978565037559311104903 149528967847556338966657355)
        ·
          refine ⟨224293451771334508449986033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149528967847556338966657355 224293451771334508449986033)
          ·
            refine ⟨168220088828500881337489525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224293451771334508449986033 168220088828500881337489525)
            ·
              refine ⟨15770633327671957625389643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168220088828500881337489525 15770633327671957625389643)
              ·
                refine ⟨23655949991507936438084465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15770633327671957625389643 23655949991507936438084465)
                ·
                  refine ⟨17741962493630952328563349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23655949991507936438084465 17741962493630952328563349)
                  ·
                    refine ⟨831654491888950890401407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17741962493630952328563349 831654491888950890401407)
                    ·
                      rfl

theorem cell23_4858924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_4858924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858924 prefixEnd_4858924 := by exact prefixLift 4858924
  have htrace : WordTrace (prefixWord ++ tailWord_4858924) baseStart_4858924 baseEnd_4858924 := by
    simpa [prefixWord, tailWord_4858924, baseEnd_4858924] using wordTrace_append hprefix tailTrace_4858924
  have hstable : (prefixWord ++ tailWord_4858924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858924).length < 2 ^ (prefixWord ++ tailWord_4858924).sum := by decide
  have hdescent : baseEnd_4858924 < baseStart_4858924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858944 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 4]
def baseStart_4858944 : Nat := 118140960795 + 4858944 * 2 ^ 59
def prefixEnd_4858944 : Nat := 4983230072969 + 3 ^ 40 * 4858944 * 2
def baseEnd_4858944 : Nat := 2494973745279942592954129

theorem tailTrace_4858944 : CollatzResearch.WordTrace tailWord_4858944 prefixEnd_4858944 2494973745279942592954129 := by
  unfold tailWord_4858944
  simp only [CollatzResearch.WordTrace]
  refine ⟨88610123454441602206623943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118146831272588802942165257 88610123454441602206623943)
  ·
    refine ⟨132915185181662403309935915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88610123454441602206623943 132915185181662403309935915)
    ·
      refine ⟨199372777772493604964903873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132915185181662403309935915 199372777772493604964903873)
      ·
        refine ⟨149529583329370203723677905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199372777772493604964903873 149529583329370203723677905)
        ·
          refine ⟨112147187497027652792758429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149529583329370203723677905 112147187497027652792758429)
          ·
            refine ⟨42055195311385369797284411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112147187497027652792758429 42055195311385369797284411)
            ·
              refine ⟨63082792967078054695926617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42055195311385369797284411 63082792967078054695926617)
              ·
                refine ⟨47312094725308541021944963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63082792967078054695926617 47312094725308541021944963)
                ·
                  refine ⟨70968142087962811532917445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47312094725308541021944963 70968142087962811532917445)
                  ·
                    refine ⟨13306526641493027162422021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70968142087962811532917445 13306526641493027162422021)
                    ·
                      refine ⟨2494973745279942592954129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13306526641493027162422021 2494973745279942592954129)
                      ·
                        rfl

theorem cell23_4858944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_4858944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858944 prefixEnd_4858944 := by exact prefixLift 4858944
  have htrace : WordTrace (prefixWord ++ tailWord_4858944) baseStart_4858944 baseEnd_4858944 := by
    simpa [prefixWord, tailWord_4858944, baseEnd_4858944] using wordTrace_append hprefix tailTrace_4858944
  have hstable : (prefixWord ++ tailWord_4858944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858944).length < 2 ^ (prefixWord ++ tailWord_4858944).sum := by decide
  have hdescent : baseEnd_4858944 < baseStart_4858944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858978 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4858978 : Nat := 118140960795 + 4858978 * 2 ^ 59
def prefixEnd_4858978 : Nat := 4983230072969 + 3 ^ 40 * 4858978 * 2
def baseEnd_4858978 : Nat := 2494991203622195459928973

theorem tailTrace_4858978 : CollatzResearch.WordTrace tailWord_4858978 prefixEnd_4858978 2494991203622195459928973 := by
  unfold tailWord_4858978
  simp only [CollatzResearch.WordTrace]
  refine ⟨44305371747690007054996397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118147657993840018813323725 44305371747690007054996397)
  ·
    refine ⟨16614514405383752645623649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44305371747690007054996397 16614514405383752645623649)
    ·
      refine ⟨12460885804037814484217737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16614514405383752645623649 12460885804037814484217737)
      ·
        refine ⟨9345664353028360863163303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12460885804037814484217737 9345664353028360863163303)
        ·
          refine ⟨14018496529542541294744955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9345664353028360863163303 14018496529542541294744955)
          ·
            refine ⟨21027744794313811942117433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14018496529542541294744955 21027744794313811942117433)
            ·
              refine ⟨15770808595735358956588075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21027744794313811942117433 15770808595735358956588075)
              ·
                refine ⟨23656212893603038434882113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15770808595735358956588075 23656212893603038434882113)
                ·
                  refine ⟨17742159670202278826161585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23656212893603038434882113 17742159670202278826161585)
                  ·
                    refine ⟨13306619752651709119621189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17742159670202278826161585 13306619752651709119621189)
                    ·
                      refine ⟨2494991203622195459928973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13306619752651709119621189 2494991203622195459928973)
                      ·
                        rfl

theorem cell23_4858978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4858978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858978 prefixEnd_4858978 := by exact prefixLift 4858978
  have htrace : WordTrace (prefixWord ++ tailWord_4858978) baseStart_4858978 baseEnd_4858978 := by
    simpa [prefixWord, tailWord_4858978, baseEnd_4858978] using wordTrace_append hprefix tailTrace_4858978
  have hstable : (prefixWord ++ tailWord_4858978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858978).length < 2 ^ (prefixWord ++ tailWord_4858978).sum := by decide
  have hdescent : baseEnd_4858978 < baseStart_4858978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4858981 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 2, 3, 3]
def baseStart_4858981 : Nat := 118140960795 + 4858981 * 2 ^ 59
def prefixEnd_4858981 : Nat := 4983230072969 + 3 ^ 40 * 4858981 * 2
def baseEnd_4858981 : Nat := 2494992744064158948191459

theorem tailTrace_4858981 : CollatzResearch.WordTrace tailWord_4858981 prefixEnd_4858981 2494992744064158948191459 := by
  unfold tailWord_4858981
  simp only [CollatzResearch.WordTrace]
  refine ⟨177221596409749159732344797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118147730939832773154896531 177221596409749159732344797)
  ·
    refine ⟨66458098653655934899629299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177221596409749159732344797 66458098653655934899629299)
    ·
      refine ⟨99687147980483902349443949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66458098653655934899629299 99687147980483902349443949)
      ·
        refine ⟨37382680492681463381041481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99687147980483902349443949 37382680492681463381041481)
        ·
          refine ⟨28037010369511097535781111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37382680492681463381041481 28037010369511097535781111)
          ·
            refine ⟨42055515554266646303671667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28037010369511097535781111 42055515554266646303671667)
            ·
              refine ⟨63083273331399969455507501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42055515554266646303671667 63083273331399969455507501)
              ·
                refine ⟨23656227499274988545815313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63083273331399969455507501 23656227499274988545815313)
                ·
                  refine ⟨17742170624456241409361485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23656227499274988545815313 17742170624456241409361485)
                  ·
                    refine ⟨6653313984171090528510557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17742170624456241409361485 6653313984171090528510557)
                    ·
                      refine ⟨2494992744064158948191459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6653313984171090528510557 2494992744064158948191459)
                      ·
                        rfl

theorem cell23_4858981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_4858981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4858981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4858981 prefixEnd_4858981 := by exact prefixLift 4858981
  have htrace : WordTrace (prefixWord ++ tailWord_4858981) baseStart_4858981 baseEnd_4858981 := by
    simpa [prefixWord, tailWord_4858981, baseEnd_4858981] using wordTrace_append hprefix tailTrace_4858981
  have hstable : (prefixWord ++ tailWord_4858981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4858981).length < 2 ^ (prefixWord ++ tailWord_4858981).sum := by decide
  have hdescent : baseEnd_4858981 < baseStart_4858981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4858981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859024 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 5]
def baseStart_4859024 : Nat := 118140960795 + 4859024 * 2 ^ 59
def prefixEnd_4859024 : Nat := 4983230072969 + 3 ^ 40 * 4859024 * 2
def baseEnd_4859024 : Nat := 2495014823732302279953761

theorem tailTrace_4859024 : CollatzResearch.WordTrace tailWord_4859024 prefixEnd_4859024 2495014823732302279953761 := by
  unfold tailWord_4859024
  simp only [CollatzResearch.WordTrace]
  refine ⟨88611582374296689038080063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118148776499062252050773417 88611582374296689038080063)
  ·
    refine ⟨132917373561445033557120095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88611582374296689038080063 132917373561445033557120095)
    ·
      refine ⟨199376060342167550335680143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132917373561445033557120095 199376060342167550335680143)
      ·
        refine ⟨299064090513251325503520215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199376060342167550335680143 299064090513251325503520215)
        ·
          refine ⟨448596135769876988255280323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299064090513251325503520215 448596135769876988255280323)
          ·
            refine ⟨672894203654815482382920485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448596135769876988255280323 672894203654815482382920485)
            ·
              refine ⟨126167663185277902946797591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 672894203654815482382920485 126167663185277902946797591)
              ·
                refine ⟨189251494777916854420196387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126167663185277902946797591 189251494777916854420196387)
                ·
                  refine ⟨283877242166875281630294581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189251494777916854420196387 283877242166875281630294581)
                  ·
                    refine ⟨26613491453144557652840117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 283877242166875281630294581 26613491453144557652840117)
                    ·
                      refine ⟨2495014823732302279953761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26613491453144557652840117 2495014823732302279953761)
                      ·
                        rfl

theorem cell23_4859024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_4859024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859024 prefixEnd_4859024 := by exact prefixLift 4859024
  have htrace : WordTrace (prefixWord ++ tailWord_4859024) baseStart_4859024 baseEnd_4859024 := by
    simpa [prefixWord, tailWord_4859024, baseEnd_4859024] using wordTrace_append hprefix tailTrace_4859024
  have hstable : (prefixWord ++ tailWord_4859024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859024).length < 2 ^ (prefixWord ++ tailWord_4859024).sum := by decide
  have hdescent : baseEnd_4859024 < baseStart_4859024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859058 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_4859058 : Nat := 118140960795 + 4859058 * 2 ^ 59
def prefixEnd_4859058 : Nat := 4983230072969 + 3 ^ 40 * 4859058 * 2
def baseEnd_4859058 : Nat := 2495032282074555146928605

theorem tailTrace_4859058 : CollatzResearch.WordTrace tailWord_4859058 prefixEnd_4859058 2495032282074555146928605 := by
  unfold tailWord_4859058
  simp only [CollatzResearch.WordTrace]
  refine ⟨44306101207617550470724457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118149603220313467921931885 44306101207617550470724457)
  ·
    refine ⟨33229575905713162853043343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44306101207617550470724457 33229575905713162853043343)
    ·
      refine ⟨49844363858569744279565015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33229575905713162853043343 49844363858569744279565015)
      ·
        refine ⟨74766545787854616419347523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49844363858569744279565015 74766545787854616419347523)
        ·
          refine ⟨112149818681781924629021285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74766545787854616419347523 112149818681781924629021285)
          ·
            refine ⟨21028091002834110867941491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112149818681781924629021285 21028091002834110867941491)
            ·
              refine ⟨31542136504251166301912237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21028091002834110867941491 31542136504251166301912237)
              ·
                refine ⟨11828301189094187363217089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31542136504251166301912237 11828301189094187363217089)
                ·
                  refine ⟨8871225891820640522412817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11828301189094187363217089 8871225891820640522412817)
                  ·
                    refine ⟨6653419418865480391809613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8871225891820640522412817 6653419418865480391809613)
                    ·
                      refine ⟨2495032282074555146928605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6653419418865480391809613 2495032282074555146928605)
                      ·
                        rfl

theorem cell23_4859058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_4859058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859058 prefixEnd_4859058 := by exact prefixLift 4859058
  have htrace : WordTrace (prefixWord ++ tailWord_4859058) baseStart_4859058 baseEnd_4859058 := by
    simpa [prefixWord, tailWord_4859058, baseEnd_4859058] using wordTrace_append hprefix tailTrace_4859058
  have hstable : (prefixWord ++ tailWord_4859058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859058).length < 2 ^ (prefixWord ++ tailWord_4859058).sum := by decide
  have hdescent : baseEnd_4859058 < baseStart_4859058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859082 : List Nat := [3, 1, 2, 1, 3, 2, 4, 2, 1, 4]
def baseStart_4859082 : Nat := 118140960795 + 4859082 * 2 ^ 59
def prefixEnd_4859082 : Nat := 4983230072969 + 3 ^ 40 * 4859082 * 2
def baseEnd_4859082 : Nat := 831681535203421017676165

theorem tailTrace_4859082 : CollatzResearch.WordTrace tailWord_4859082 prefixEnd_4859082 831681535203421017676165 := by
  unfold tailWord_4859082
  simp only [CollatzResearch.WordTrace]
  refine ⟨44306320045595813495442875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118150186788255502654514333 44306320045595813495442875)
  ·
    refine ⟨66459480068393720243164313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44306320045595813495442875 66459480068393720243164313)
    ·
      refine ⟨49844610051295290182373235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66459480068393720243164313 49844610051295290182373235)
      ·
        refine ⟨74766915076942935273559853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49844610051295290182373235 74766915076942935273559853)
        ·
          refine ⟨28037593153853600727584945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74766915076942935273559853 28037593153853600727584945)
          ·
            refine ⟨21028194865390200545688709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28037593153853600727584945 21028194865390200545688709)
            ·
              refine ⟨3942786537260662602316633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21028194865390200545688709 3942786537260662602316633)
              ·
                refine ⟨2957089902945496951737475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3942786537260662602316633 2957089902945496951737475)
                ·
                  refine ⟨4435634854418245427606213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957089902945496951737475 4435634854418245427606213)
                  ·
                    refine ⟨831681535203421017676165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4435634854418245427606213 831681535203421017676165)
                    ·
                      rfl

theorem cell23_4859082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_4859082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859082 prefixEnd_4859082 := by exact prefixLift 4859082
  have htrace : WordTrace (prefixWord ++ tailWord_4859082) baseStart_4859082 baseEnd_4859082 := by
    simpa [prefixWord, tailWord_4859082, baseEnd_4859082] using wordTrace_append hprefix tailTrace_4859082
  have hstable : (prefixWord ++ tailWord_4859082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859082).length < 2 ^ (prefixWord ++ tailWord_4859082).sum := by decide
  have hdescent : baseEnd_4859082 < baseStart_4859082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859098 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2]
def baseStart_4859098 : Nat := 118140960795 + 4859098 * 2 ^ 59
def prefixEnd_4859098 : Nat := 4983230072969 + 3 ^ 40 * 4859098 * 2
def baseEnd_4859098 : Nat := 2495052821300734990428421

theorem tailTrace_4859098 : CollatzResearch.WordTrace tailWord_4859098 prefixEnd_4859098 2495052821300734990428421 := by
  unfold tailWord_4859098
  simp only [CollatzResearch.WordTrace]
  refine ⟨44306465937581322178588487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118150575833550192476235965 44306465937581322178588487)
  ·
    refine ⟨66459698906371983267882731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44306465937581322178588487 66459698906371983267882731)
    ·
      refine ⟨99689548359557974901824097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66459698906371983267882731 99689548359557974901824097)
      ·
        refine ⟨74767161269668481176368073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99689548359557974901824097 74767161269668481176368073)
        ·
          refine ⟨56075370952251360882276055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74767161269668481176368073 56075370952251360882276055)
          ·
            refine ⟨84113056428377041323414083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56075370952251360882276055 84113056428377041323414083)
            ·
              refine ⟨126169584642565561985121125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84113056428377041323414083 126169584642565561985121125)
              ·
                refine ⟨23656797120481042872210211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126169584642565561985121125 23656797120481042872210211)
                ·
                  refine ⟨35485195680721564308315317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23656797120481042872210211 35485195680721564308315317)
                  ·
                    refine ⟨3326737095067646653904561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35485195680721564308315317 3326737095067646653904561)
                    ·
                      refine ⟨2495052821300734990428421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3326737095067646653904561 2495052821300734990428421)
                      ·
                        rfl

theorem cell23_4859098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_4859098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859098 prefixEnd_4859098 := by exact prefixLift 4859098
  have htrace : WordTrace (prefixWord ++ tailWord_4859098) baseStart_4859098 baseEnd_4859098 := by
    simpa [prefixWord, tailWord_4859098, baseEnd_4859098] using wordTrace_append hprefix tailTrace_4859098
  have hstable : (prefixWord ++ tailWord_4859098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859098).length < 2 ^ (prefixWord ++ tailWord_4859098).sum := by decide
  have hdescent : baseEnd_4859098 < baseStart_4859098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859105 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_4859105 : Nat := 118140960795 + 4859105 * 2 ^ 59
def prefixEnd_4859105 : Nat := 4983230072969 + 3 ^ 40 * 4859105 * 2
def baseEnd_4859105 : Nat := 2495056415665316463040889

theorem tailTrace_4859105 : CollatzResearch.WordTrace tailWord_4859105 prefixEnd_4859105 2495056415665316463040889 := by
  unfold tailWord_4859105
  simp only [CollatzResearch.WordTrace]
  refine ⟨177226119061299928909858769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118150746040866619273239179 177226119061299928909858769)
  ·
    refine ⟨132919589295974946682394077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177226119061299928909858769 132919589295974946682394077)
    ·
      refine ⟨49844845985990605005897779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132919589295974946682394077 49844845985990605005897779)
      ·
        refine ⟨74767268978985907508846669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49844845985990605005897779 74767268978985907508846669)
        ·
          refine ⟨28037725867119715315817501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74767268978985907508846669 28037725867119715315817501)
          ·
            refine ⟨10514147200169893243431563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28037725867119715315817501 10514147200169893243431563)
            ·
              refine ⟨15771220800254839865147345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10514147200169893243431563 15771220800254839865147345)
              ·
                refine ⟨11828415600191129898860509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15771220800254839865147345 11828415600191129898860509)
                ·
                  refine ⟨4435655850071673712072691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11828415600191129898860509 4435655850071673712072691)
                  ·
                    refine ⟨6653483775107510568109037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4435655850071673712072691 6653483775107510568109037)
                    ·
                      refine ⟨2495056415665316463040889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6653483775107510568109037 2495056415665316463040889)
                      ·
                        rfl

theorem cell23_4859105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_4859105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859105 prefixEnd_4859105 := by exact prefixLift 4859105
  have htrace : WordTrace (prefixWord ++ tailWord_4859105) baseStart_4859105 baseEnd_4859105 := by
    simpa [prefixWord, tailWord_4859105, baseEnd_4859105] using wordTrace_append hprefix tailTrace_4859105
  have hstable : (prefixWord ++ tailWord_4859105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859105).length < 2 ^ (prefixWord ++ tailWord_4859105).sum := by decide
  have hdescent : baseEnd_4859105 < baseStart_4859105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859115 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 2, 3, 2]
def baseStart_4859115 : Nat := 118140960795 + 4859115 * 2 ^ 59
def prefixEnd_4859115 : Nat := 4983230072969 + 3 ^ 40 * 4859115 * 2
def baseEnd_4859115 : Nat := 2495061550471861423915843

theorem tailTrace_4859115 : CollatzResearch.WordTrace tailWord_4859115 prefixEnd_4859115 2495061550471861423915843 := by
  unfold tailWord_4859115
  simp only [CollatzResearch.WordTrace]
  refine ⟨177226483791263700617722799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118150989194175800411815199 177226483791263700617722799)
  ·
    refine ⟨265839725686895550926584199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177226483791263700617722799 265839725686895550926584199)
    ·
      refine ⟨398759588530343326389876299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265839725686895550926584199 398759588530343326389876299)
      ·
        refine ⟨598139382795514989584814449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398759588530343326389876299 598139382795514989584814449)
        ·
          refine ⟨448604537096636242188610837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 598139382795514989584814449 448604537096636242188610837)
          ·
            refine ⟨21028337676404823852591133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 448604537096636242188610837 21028337676404823852591133)
            ·
              refine ⟨7885626628651808944721675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21028337676404823852591133 7885626628651808944721675)
              ·
                refine ⟨11828439942977713417082513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7885626628651808944721675 11828439942977713417082513)
                ·
                  refine ⟨8871329957233285062811885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11828439942977713417082513 8871329957233285062811885)
                  ·
                    refine ⟨3326748733962481898554457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8871329957233285062811885 3326748733962481898554457)
                    ·
                      refine ⟨2495061550471861423915843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3326748733962481898554457 2495061550471861423915843)
                      ·
                        rfl

theorem cell23_4859115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 3, 2].length) (baseStart_4859115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859115 prefixEnd_4859115 := by exact prefixLift 4859115
  have htrace : WordTrace (prefixWord ++ tailWord_4859115) baseStart_4859115 baseEnd_4859115 := by
    simpa [prefixWord, tailWord_4859115, baseEnd_4859115] using wordTrace_append hprefix tailTrace_4859115
  have hstable : (prefixWord ++ tailWord_4859115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859115).length < 2 ^ (prefixWord ++ tailWord_4859115).sum := by decide
  have hdescent : baseEnd_4859115 < baseStart_4859115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859141 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_4859141 : Nat := 118140960795 + 4859141 * 2 ^ 59
def prefixEnd_4859141 : Nat := 4983230072969 + 3 ^ 40 * 4859141 * 2
def baseEnd_4859141 : Nat := 2495074900968878322190723

theorem tailTrace_4859141 : CollatzResearch.WordTrace tailWord_4859141 prefixEnd_4859141 2495074900968878322190723 := by
  unfold tailWord_4859141
  simp only [CollatzResearch.WordTrace]
  refine ⟨177227432089169507058169277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118151621392779671372112851 177227432089169507058169277)
  ·
    refine ⟨66460287033438565146813479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177227432089169507058169277 66460287033438565146813479)
    ·
      refine ⟨99690430550157847720220219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66460287033438565146813479 99690430550157847720220219)
      ·
        refine ⟨149535645825236771580330329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99690430550157847720220219 149535645825236771580330329)
        ·
          refine ⟨112151734368927578685247747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149535645825236771580330329 112151734368927578685247747)
          ·
            refine ⟨168227601553391368027871621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112151734368927578685247747 168227601553391368027871621)
            ·
              refine ⟨31542675291260881505225929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168227601553391368027871621 31542675291260881505225929)
              ·
                refine ⟨23657006468445661128919447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31542675291260881505225929 23657006468445661128919447)
                ·
                  refine ⟨35485509702668491693379171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23657006468445661128919447 35485509702668491693379171)
                  ·
                    refine ⟨53228264554002737540068757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35485509702668491693379171 53228264554002737540068757)
                    ·
                      refine ⟨2495074900968878322190723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53228264554002737540068757 2495074900968878322190723)
                      ·
                        rfl

theorem cell23_4859141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_4859141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859141 prefixEnd_4859141 := by exact prefixLift 4859141
  have htrace : WordTrace (prefixWord ++ tailWord_4859141) baseStart_4859141 baseEnd_4859141 := by
    simpa [prefixWord, tailWord_4859141, baseEnd_4859141] using wordTrace_append hprefix tailTrace_4859141
  have hstable : (prefixWord ++ tailWord_4859141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859141).length < 2 ^ (prefixWord ++ tailWord_4859141).sum := by decide
  have hdescent : baseEnd_4859141 < baseStart_4859141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859148 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_4859148 : Nat := 118140960795 + 4859148 * 2 ^ 59
def prefixEnd_4859148 : Nat := 4983230072969 + 3 ^ 40 * 4859148 * 2
def baseEnd_4859148 : Nat := 2495078495333459794803191

theorem tailTrace_4859148 : CollatzResearch.WordTrace tailWord_4859148 prefixEnd_4859148 2495078495333459794803191 := by
  unfold tailWord_4859148
  simp only [CollatzResearch.WordTrace]
  refine ⟨88613843700072073626837049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118151791600096098169116065 88613843700072073626837049)
  ·
    refine ⟨66460382775054055220127787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88613843700072073626837049 66460382775054055220127787)
    ·
      refine ⟨99690574162581082830191681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66460382775054055220127787 99690574162581082830191681)
      ·
        refine ⟨74767930621935812122643761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99690574162581082830191681 74767930621935812122643761)
        ·
          refine ⟨56075947966451859091982821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74767930621935812122643761 56075947966451859091982821)
          ·
            refine ⟨10514240243709723579746779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56075947966451859091982821 10514240243709723579746779)
            ·
              refine ⟨15771360365564585369620169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10514240243709723579746779 15771360365564585369620169)
              ·
                refine ⟨11828520274173439027215127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15771360365564585369620169 11828520274173439027215127)
                ·
                  refine ⟨17742780411260158540822691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11828520274173439027215127 17742780411260158540822691)
                  ·
                    refine ⟨26614170616890237811234037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17742780411260158540822691 26614170616890237811234037)
                    ·
                      refine ⟨2495078495333459794803191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26614170616890237811234037 2495078495333459794803191)
                      ·
                        rfl

theorem cell23_4859148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_4859148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859148 prefixEnd_4859148 := by exact prefixLift 4859148
  have htrace : WordTrace (prefixWord ++ tailWord_4859148) baseStart_4859148 baseEnd_4859148 := by
    simpa [prefixWord, tailWord_4859148, baseEnd_4859148] using wordTrace_append hprefix tailTrace_4859148
  have hstable : (prefixWord ++ tailWord_4859148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859148).length < 2 ^ (prefixWord ++ tailWord_4859148).sum := by decide
  have hdescent : baseEnd_4859148 < baseStart_4859148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859162 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2]
def baseStart_4859162 : Nat := 118140960795 + 4859162 * 2 ^ 59
def prefixEnd_4859162 : Nat := 4983230072969 + 3 ^ 40 * 4859162 * 2
def baseEnd_4859162 : Nat := 2495085684062622740028127

theorem tailTrace_4859162 : CollatzResearch.WordTrace tailWord_4859162 prefixEnd_4859162 2495085684062622740028127 := by
  unfold tailWord_4859162
  simp only [CollatzResearch.WordTrace]
  refine ⟨44307049505523356911170935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118152132014728951763122493 44307049505523356911170935)
  ·
    refine ⟨66460574258285035366756403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44307049505523356911170935 66460574258285035366756403)
    ·
      refine ⟨99690861387427553050134605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66460574258285035366756403 99690861387427553050134605)
      ·
        refine ⟨37384073020285332393800477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99690861387427553050134605 37384073020285332393800477)
        ·
          refine ⟨14019027382606999647675179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37384073020285332393800477 14019027382606999647675179)
          ·
            refine ⟨21028541073910499471512769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14019027382606999647675179 21028541073910499471512769)
            ·
              refine ⟨15771405805432874603634577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21028541073910499471512769 15771405805432874603634577)
              ·
                refine ⟨11828554354074655952725933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15771405805432874603634577 11828554354074655952725933)
                ·
                  refine ⟨4435707882777995982272225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11828554354074655952725933 4435707882777995982272225)
                  ·
                    refine ⟨3326780912083496986704169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4435707882777995982272225 3326780912083496986704169)
                    ·
                      refine ⟨2495085684062622740028127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3326780912083496986704169 2495085684062622740028127)
                      ·
                        rfl

theorem cell23_4859162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_4859162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859162 prefixEnd_4859162 := by exact prefixLift 4859162
  have htrace : WordTrace (prefixWord ++ tailWord_4859162) baseStart_4859162 baseEnd_4859162 := by
    simpa [prefixWord, tailWord_4859162, baseEnd_4859162] using wordTrace_append hprefix tailTrace_4859162
  have hstable : (prefixWord ++ tailWord_4859162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859162).length < 2 ^ (prefixWord ++ tailWord_4859162).sum := by decide
  have hdescent : baseEnd_4859162 < baseStart_4859162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859168 : List Nat := [2, 1, 1, 5, 3, 1, 1, 9]
def baseStart_4859168 : Nat := 118140960795 + 4859168 * 2 ^ 59
def prefixEnd_4859168 : Nat := 4983230072969 + 3 ^ 40 * 4859168 * 2
def baseEnd_4859168 : Nat := 92410694998020359872337

theorem tailTrace_4859168 : CollatzResearch.WordTrace tailWord_4859168 prefixEnd_4859168 92410694998020359872337 := by
  unfold tailWord_4859168
  simp only [CollatzResearch.WordTrace]
  refine ⟨88614208430035845334701079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118152277906714460446268105 88614208430035845334701079)
  ·
    refine ⟨132921312645053768002051619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88614208430035845334701079 132921312645053768002051619)
    ·
      refine ⟨199381968967580652003077429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132921312645053768002051619 199381968967580652003077429)
      ·
        refine ⟨18692059590710686125288509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 199381968967580652003077429 18692059590710686125288509)
        ·
          refine ⟨7009522346516507296983191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18692059590710686125288509 7009522346516507296983191)
          ·
            refine ⟨10514283519774760945474787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7009522346516507296983191 10514283519774760945474787)
            ·
              refine ⟨15771425279662141418212181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10514283519774760945474787 15771425279662141418212181)
              ·
                refine ⟨92410694998020359872337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15771425279662141418212181 92410694998020359872337)
                ·
                  rfl

theorem cell23_4859168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 9].length) (baseStart_4859168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859168 prefixEnd_4859168 := by exact prefixLift 4859168
  have htrace : WordTrace (prefixWord ++ tailWord_4859168) baseStart_4859168 baseEnd_4859168 := by
    simpa [prefixWord, tailWord_4859168, baseEnd_4859168] using wordTrace_append hprefix tailTrace_4859168
  have hstable : (prefixWord ++ tailWord_4859168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859168).length < 2 ^ (prefixWord ++ tailWord_4859168).sum := by decide
  have hdescent : baseEnd_4859168 < baseStart_4859168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859196 : List Nat := [2, 2, 2, 2, 1, 4, 3, 2, 1, 2, 2]
def baseStart_4859196 : Nat := 118140960795 + 4859196 * 2 ^ 59
def prefixEnd_4859196 : Nat := 4983230072969 + 3 ^ 40 * 4859196 * 2
def baseEnd_4859196 : Nat := 2495103142404875607002971

theorem tailTrace_4859196 : CollatzResearch.WordTrace tailWord_4859196 prefixEnd_4859196 2495103142404875607002971 := by
  unfold tailWord_4859196
  simp only [CollatzResearch.WordTrace]
  refine ⟨88614719051985125725710721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118152958735980167634280961 88614719051985125725710721)
  ·
    refine ⟨66461039288988844294283041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88614719051985125725710721 66461039288988844294283041)
    ·
      refine ⟨49845779466741633220712281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66461039288988844294283041 49845779466741633220712281)
      ·
        refine ⟨37384334600056224915534211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49845779466741633220712281 37384334600056224915534211)
        ·
          refine ⟨56076501900084337373301317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37384334600056224915534211 56076501900084337373301317)
          ·
            refine ⟨10514344106265813257493997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56076501900084337373301317 10514344106265813257493997)
            ·
              refine ⟨3942879039849679971560249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10514344106265813257493997 3942879039849679971560249)
              ·
                refine ⟨2957159279887259978670187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3942879039849679971560249 2957159279887259978670187)
                ·
                  refine ⟨4435738919830889968005281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957159279887259978670187 4435738919830889968005281)
                  ·
                    refine ⟨3326804189873167476003961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4435738919830889968005281 3326804189873167476003961)
                    ·
                      refine ⟨2495103142404875607002971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3326804189873167476003961 2495103142404875607002971)
                      ·
                        rfl

theorem cell23_4859196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_4859196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859196 prefixEnd_4859196 := by exact prefixLift 4859196
  have htrace : WordTrace (prefixWord ++ tailWord_4859196) baseStart_4859196 baseEnd_4859196 := by
    simpa [prefixWord, tailWord_4859196, baseEnd_4859196] using wordTrace_append hprefix tailTrace_4859196
  have hstable : (prefixWord ++ tailWord_4859196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859196).length < 2 ^ (prefixWord ++ tailWord_4859196).sum := by decide
  have hdescent : baseEnd_4859196 < baseStart_4859196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859198 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_4859198 : Nat := 118140960795 + 4859198 * 2 ^ 59
def prefixEnd_4859198 : Nat := 4983230072969 + 3 ^ 40 * 4859198 * 2
def baseEnd_4859198 : Nat := 831701389788728199725987

theorem tailTrace_4859198 : CollatzResearch.WordTrace tailWord_4859198 prefixEnd_4859198 831701389788728199725987 := by
  unfold tailWord_4859198
  simp only [CollatzResearch.WordTrace]
  refine ⟨22153688881245375724124281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118153007366642003861996165 22153688881245375724124281)
  ·
    refine ⟨16615266660934031793093211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22153688881245375724124281 16615266660934031793093211)
    ·
      refine ⟨24922899991401047689639817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16615266660934031793093211 24922899991401047689639817)
      ·
        refine ⟨18692174993550785767229863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24922899991401047689639817 18692174993550785767229863)
        ·
          refine ⟨28038262490326178650844795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18692174993550785767229863 28038262490326178650844795)
          ·
            refine ⟨42057393735489267976267193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28038262490326178650844795 42057393735489267976267193)
            ·
              refine ⟨31543045301616950982200395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42057393735489267976267193 31543045301616950982200395)
              ·
                refine ⟨47314567952425426473300593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31543045301616950982200395 47314567952425426473300593)
                ·
                  refine ⟨35485925964319069854975445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47314567952425426473300593 35485925964319069854975445)
                  ·
                    refine ⟨831701389788728199725987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35485925964319069854975445 831701389788728199725987)
                    ·
                      rfl

theorem cell23_4859198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_4859198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859198 prefixEnd_4859198 := by exact prefixLift 4859198
  have htrace : WordTrace (prefixWord ++ tailWord_4859198) baseStart_4859198 baseEnd_4859198 := by
    simpa [prefixWord, tailWord_4859198, baseEnd_4859198] using wordTrace_append hprefix tailTrace_4859198
  have hstable : (prefixWord ++ tailWord_4859198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859198).length < 2 ^ (prefixWord ++ tailWord_4859198).sum := by decide
  have hdescent : baseEnd_4859198 < baseStart_4859198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859206 : List Nat := [6, 1, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_4859206 : Nat := 118140960795 + 4859206 * 2 ^ 59
def prefixEnd_4859206 : Nat := 4983230072969 + 3 ^ 40 * 4859206 * 2
def baseEnd_4859206 : Nat := 831702759070473522625975

theorem tailTrace_4859206 : CollatzResearch.WordTrace tailWord_4859206 prefixEnd_4859206 831702759070473522625975 := by
  unfold tailWord_4859206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5538431338560438223727671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118153201889289348772856981 5538431338560438223727671)
  ·
    refine ⟨8307647007840657335591507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5538431338560438223727671 8307647007840657335591507)
    ·
      refine ⟨12461470511760986003387261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8307647007840657335591507 12461470511760986003387261)
      ·
        refine ⟨4673051441910369751270223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12461470511760986003387261 4673051441910369751270223)
        ·
          refine ⟨7009577162865554626905335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4673051441910369751270223 7009577162865554626905335)
          ·
            refine ⟨10514365744298331940358003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7009577162865554626905335 10514365744298331940358003)
            ·
              refine ⟨15771548616447497910537005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10514365744298331940358003 15771548616447497910537005)
              ·
                refine ⟨5914330731167811716451377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15771548616447497910537005 5914330731167811716451377)
                ·
                  refine ⟨4435748048375858787338533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5914330731167811716451377 4435748048375858787338533)
                  ·
                    refine ⟨831702759070473522625975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4435748048375858787338533 831702759070473522625975)
                    ·
                      rfl

theorem cell23_4859206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_4859206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859206 prefixEnd_4859206 := by exact prefixLift 4859206
  have htrace : WordTrace (prefixWord ++ tailWord_4859206) baseStart_4859206 baseEnd_4859206 := by
    simpa [prefixWord, tailWord_4859206, baseEnd_4859206] using wordTrace_append hprefix tailTrace_4859206
  have hstable : (prefixWord ++ tailWord_4859206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859206).length < 2 ^ (prefixWord ++ tailWord_4859206).sum := by decide
  have hdescent : baseEnd_4859206 < baseStart_4859206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859211 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 6, 6]
def baseStart_4859211 : Nat := 118140960795 + 4859211 * 2 ^ 59
def prefixEnd_4859211 : Nat := 4983230072969 + 3 ^ 40 * 4859211 * 2
def baseEnd_4859211 : Nat := 831703614871564349438467

theorem tailTrace_4859211 : CollatzResearch.WordTrace tailWord_4859211 prefixEnd_4859211 831703614871564349438467 := by
  unfold tailWord_4859211
  simp only [CollatzResearch.WordTrace]
  refine ⟨177229985198915909013217487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118153323465943939342144991 177229985198915909013217487)
  ·
    refine ⟨265844977798373863519826231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177229985198915909013217487 265844977798373863519826231)
    ·
      refine ⟨398767466697560795279739347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265844977798373863519826231 398767466697560795279739347)
      ·
        refine ⟨598151200046341192919609021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398767466697560795279739347 598151200046341192919609021)
        ·
          refine ⟨224306700017377947344853383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 598151200046341192919609021 224306700017377947344853383)
          ·
            refine ⟨336460050026066921017280075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224306700017377947344853383 336460050026066921017280075)
            ·
              refine ⟨504690075039100381525920113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336460050026066921017280075 504690075039100381525920113)
              ·
                refine ⟨378517556279325286144440085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504690075039100381525920113 378517556279325286144440085)
                ·
                  refine ⟨17743010450593372788020629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 378517556279325286144440085 17743010450593372788020629)
                  ·
                    refine ⟨831703614871564349438467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17743010450593372788020629 831703614871564349438467)
                    ·
                      rfl

theorem cell23_4859211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 6].length) (baseStart_4859211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859211 prefixEnd_4859211 := by exact prefixLift 4859211
  have htrace : WordTrace (prefixWord ++ tailWord_4859211) baseStart_4859211 baseEnd_4859211 := by
    simpa [prefixWord, tailWord_4859211, baseEnd_4859211] using wordTrace_append hprefix tailTrace_4859211
  have hstable : (prefixWord ++ tailWord_4859211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859211).length < 2 ^ (prefixWord ++ tailWord_4859211).sum := by decide
  have hdescent : baseEnd_4859211 < baseStart_4859211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859212 : List Nat := [2, 2, 1, 3, 2, 3, 1, 3, 2, 1, 3]
def baseStart_4859212 : Nat := 118140960795 + 4859212 * 2 ^ 59
def prefixEnd_4859212 : Nat := 4983230072969 + 3 ^ 40 * 4859212 * 2
def baseEnd_4859212 : Nat := 2495111358095347544402897

theorem tailTrace_4859212 : CollatzResearch.WordTrace tailWord_4859212 prefixEnd_4859212 2495111358095347544402897 := by
  unfold tailWord_4859212
  simp only [CollatzResearch.WordTrace]
  refine ⟨88615010835956143092001945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118153347781274857456002593 88615010835956143092001945)
  ·
    refine ⟨66461258126967107319001459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88615010835956143092001945 66461258126967107319001459)
    ·
      refine ⟨99691887190450660978502189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66461258126967107319001459 99691887190450660978502189)
      ·
        refine ⟨37384457696418997866938321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99691887190450660978502189 37384457696418997866938321)
        ·
          refine ⟨28038343272314248400203741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37384457696418997866938321 28038343272314248400203741)
          ·
            refine ⟨10514378727117843150076403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28038343272314248400203741 10514378727117843150076403)
            ·
              refine ⟨15771568090676764725114605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10514378727117843150076403 15771568090676764725114605)
              ·
                refine ⟨5914338034003786771917977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15771568090676764725114605 5914338034003786771917977)
                ·
                  refine ⟨4435753525502840078938483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5914338034003786771917977 4435753525502840078938483)
                  ·
                    refine ⟨6653630288254260118407725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4435753525502840078938483 6653630288254260118407725)
                    ·
                      refine ⟨2495111358095347544402897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6653630288254260118407725 2495111358095347544402897)
                      ·
                        rfl

theorem cell23_4859212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_4859212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859212 prefixEnd_4859212 := by exact prefixLift 4859212
  have htrace : WordTrace (prefixWord ++ tailWord_4859212) baseStart_4859212 baseEnd_4859212 := by
    simpa [prefixWord, tailWord_4859212, baseEnd_4859212] using wordTrace_append hprefix tailTrace_4859212
  have hstable : (prefixWord ++ tailWord_4859212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859212).length < 2 ^ (prefixWord ++ tailWord_4859212).sum := by decide
  have hdescent : baseEnd_4859212 < baseStart_4859212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859235 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 3, 4, 2]
def baseStart_4859235 : Nat := 118140960795 + 4859235 * 2 ^ 59
def prefixEnd_4859235 : Nat := 4983230072969 + 3 ^ 40 * 4859235 * 2
def baseEnd_4859235 : Nat := 2495123168150400954415291

theorem tailTrace_4859235 : CollatzResearch.WordTrace tailWord_4859235 prefixEnd_4859235 2495123168150400954415291 := by
  unfold tailWord_4859235
  simp only [CollatzResearch.WordTrace]
  refine ⟨177230860550828961112091159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118153907033885974074727439 177230860550828961112091159)
  ·
    refine ⟨265846290826243441668136739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177230860550828961112091159 265846290826243441668136739)
    ·
      refine ⟨398769436239365162502205109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265846290826243441668136739 398769436239365162502205109)
      ·
        refine ⟨37384634647440483984581729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 398769436239365162502205109 37384634647440483984581729)
        ·
          refine ⟨28038475985580362988436297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37384634647440483984581729 28038475985580362988436297)
          ·
            refine ⟨21028856989185272241327223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28038475985580362988436297 21028856989185272241327223)
            ·
              refine ⟨31543285483777908361990835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21028856989185272241327223 31543285483777908361990835)
              ·
                refine ⟨47314928225666862542986253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31543285483777908361990835 47314928225666862542986253)
                ·
                  refine ⟨17743098084625073453619845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47314928225666862542986253 17743098084625073453619845)
                  ·
                    refine ⟨3326830890867201272553721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17743098084625073453619845 3326830890867201272553721)
                    ·
                      refine ⟨2495123168150400954415291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3326830890867201272553721 2495123168150400954415291)
                      ·
                        rfl

theorem cell23_4859235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_4859235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859235 prefixEnd_4859235 := by exact prefixLift 4859235
  have htrace : WordTrace (prefixWord ++ tailWord_4859235) baseStart_4859235 baseEnd_4859235 := by
    simpa [prefixWord, tailWord_4859235, baseEnd_4859235] using wordTrace_append hprefix tailTrace_4859235
  have hstable : (prefixWord ++ tailWord_4859235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859235).length < 2 ^ (prefixWord ++ tailWord_4859235).sum := by decide
  have hdescent : baseEnd_4859235 < baseStart_4859235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859241 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 11]
def baseStart_4859241 : Nat := 118140960795 + 4859241 * 2 ^ 59
def prefixEnd_4859241 : Nat := 4983230072969 + 3 ^ 40 * 4859241 * 2
def baseEnd_4859241 : Nat := 277236249892703103437807

theorem tailTrace_4859241 : CollatzResearch.WordTrace tailWord_4859241 prefixEnd_4859241 277236249892703103437807 := by
  unfold tailWord_4859241
  simp only [CollatzResearch.WordTrace]
  refine ⟨177231079388807224136809577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118154052925871482757873051 177231079388807224136809577)
  ·
    refine ⟨132923309541605418102607183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177231079388807224136809577 132923309541605418102607183)
    ·
      refine ⟨199384964312408127153910775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132923309541605418102607183 199384964312408127153910775)
      ·
        refine ⟨299077446468612190730866163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199384964312408127153910775 299077446468612190730866163)
        ·
          refine ⟨448616169702918286096299245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299077446468612190730866163 448616169702918286096299245)
          ·
            refine ⟨168231063638594357286112217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 448616169702918286096299245 168231063638594357286112217)
            ·
              refine ⟨126173297728945767964584163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168231063638594357286112217 126173297728945767964584163)
              ·
                refine ⟨189259946593418651946876245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126173297728945767964584163 189259946593418651946876245)
                ·
                  refine ⟨277236249892703103437807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 189259946593418651946876245 277236249892703103437807)
                  ·
                    rfl

theorem cell23_4859241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 11].length) (baseStart_4859241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859241 prefixEnd_4859241 := by exact prefixLift 4859241
  have htrace : WordTrace (prefixWord ++ tailWord_4859241) baseStart_4859241 baseEnd_4859241 := by
    simpa [prefixWord, tailWord_4859241, baseEnd_4859241] using wordTrace_append hprefix tailTrace_4859241
  have hstable : (prefixWord ++ tailWord_4859241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859241).length < 2 ^ (prefixWord ++ tailWord_4859241).sum := by decide
  have hdescent : baseEnd_4859241 < baseStart_4859241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859246 : List Nat := [4, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_4859246 : Nat := 118140960795 + 4859246 * 2 ^ 59
def prefixEnd_4859246 : Nat := 4983230072969 + 3 ^ 40 * 4859246 * 2
def baseEnd_4859246 : Nat := 2495128816437600411377741

theorem tailTrace_4859246 : CollatzResearch.WordTrace tailWord_4859246 prefixEnd_4859246 2495128816437600411377741 := by
  unfold tailWord_4859246
  simp only [CollatzResearch.WordTrace]
  refine ⟨22153907719223638748842699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118154174502526073327161061 22153907719223638748842699)
  ·
    refine ⟨33230861578835458123264049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22153907719223638748842699 33230861578835458123264049)
    ·
      refine ⟨24923146184126593592448037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33230861578835458123264049 24923146184126593592448037)
      ·
        refine ⟨4673089909523736298584007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24923146184126593592448037 4673089909523736298584007)
        ·
          refine ⟨7009634864285604447876011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4673089909523736298584007 7009634864285604447876011)
          ·
            refine ⟨10514452296428406671814017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7009634864285604447876011 10514452296428406671814017)
            ·
              refine ⟨7885839222321305003860513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10514452296428406671814017 7885839222321305003860513)
              ·
                refine ⟨5914379416740978752895385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7885839222321305003860513 5914379416740978752895385)
                ·
                  refine ⟨4435784562555734064671539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5914379416740978752895385 4435784562555734064671539)
                  ·
                    refine ⟨6653676843833601097007309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4435784562555734064671539 6653676843833601097007309)
                    ·
                      refine ⟨2495128816437600411377741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6653676843833601097007309 2495128816437600411377741)
                      ·
                        rfl

theorem cell23_4859246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_4859246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859246 prefixEnd_4859246 := by exact prefixLift 4859246
  have htrace : WordTrace (prefixWord ++ tailWord_4859246) baseStart_4859246 baseEnd_4859246 := by
    simpa [prefixWord, tailWord_4859246, baseEnd_4859246] using wordTrace_append hprefix tailTrace_4859246
  have hstable : (prefixWord ++ tailWord_4859246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859246).length < 2 ^ (prefixWord ++ tailWord_4859246).sum := by decide
  have hdescent : baseEnd_4859246 < baseStart_4859246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859248 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 4]
def baseStart_4859248 : Nat := 118140960795 + 4859248 * 2 ^ 59
def prefixEnd_4859248 : Nat := 4983230072969 + 3 ^ 40 * 4859248 * 2
def baseEnd_4859248 : Nat := 2495129843398909403552731

theorem tailTrace_4859248 : CollatzResearch.WordTrace tailWord_4859248 prefixEnd_4859248 2495129843398909403552731 := by
  unfold tailWord_4859248
  simp only [CollatzResearch.WordTrace]
  refine ⟨88615667349890932166157199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118154223133187909554876265 88615667349890932166157199)
  ·
    refine ⟨132923501024836398249235799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88615667349890932166157199 132923501024836398249235799)
    ·
      refine ⟨199385251537254597373853699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132923501024836398249235799 199385251537254597373853699)
      ·
        refine ⟨299077877305881896060780549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199385251537254597373853699 299077877305881896060780549)
        ·
          refine ⟨56077101994852855511396353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 299077877305881896060780549 56077101994852855511396353)
          ·
            refine ⟨42057826496139641633547265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56077101994852855511396353 42057826496139641633547265)
            ·
              refine ⟨31543369872104731225160449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42057826496139641633547265 31543369872104731225160449)
              ·
                refine ⟨23657527404078548418870337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31543369872104731225160449 23657527404078548418870337)
                ·
                  refine ⟨17743145553058911314152753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23657527404078548418870337 17743145553058911314152753)
                  ·
                    refine ⟨13307359164794183485614565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17743145553058911314152753 13307359164794183485614565)
                    ·
                      refine ⟨2495129843398909403552731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13307359164794183485614565 2495129843398909403552731)
                      ·
                        rfl

theorem cell23_4859248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_4859248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859248 prefixEnd_4859248 := by exact prefixLift 4859248
  have htrace : WordTrace (prefixWord ++ tailWord_4859248) baseStart_4859248 baseEnd_4859248 := by
    simpa [prefixWord, tailWord_4859248, baseEnd_4859248] using wordTrace_append hprefix tailTrace_4859248
  have hstable : (prefixWord ++ tailWord_4859248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859248).length < 2 ^ (prefixWord ++ tailWord_4859248).sum := by decide
  have hdescent : baseEnd_4859248 < baseStart_4859248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859335 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 3, 4]
def baseStart_4859335 : Nat := 118140960795 + 4859335 * 2 ^ 59
def prefixEnd_4859335 : Nat := 4983230072969 + 3 ^ 40 * 4859335 * 2
def baseEnd_4859335 : Nat := 831724838738616854388277

theorem tailTrace_4859335 : CollatzResearch.WordTrace tailWord_4859335 prefixEnd_4859335 831724838738616854388277 := by
  unfold tailWord_4859335
  simp only [CollatzResearch.WordTrace]
  refine ⟨177234507850466678190731459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118156338566977785460487639 177234507850466678190731459)
  ·
    refine ⟨265851761775700017286097189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177234507850466678190731459 265851761775700017286097189)
    ·
      refine ⟨49847205332943753241143223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265851761775700017286097189 49847205332943753241143223)
      ·
        refine ⟨74770807999415629861714835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49847205332943753241143223 74770807999415629861714835)
        ·
          refine ⟨112156211999123444792572253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74770807999415629861714835 112156211999123444792572253)
          ·
            refine ⟨42058579499671291797214595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112156211999123444792572253 42058579499671291797214595)
            ·
              refine ⟨63087869249506937695821893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42058579499671291797214595 63087869249506937695821893)
              ·
                refine ⟨11828975484282550817966605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63087869249506937695821893 11828975484282550817966605)
                ·
                  refine ⟨4435865806605956556737477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11828975484282550817966605 4435865806605956556737477)
                  ·
                    refine ⟨831724838738616854388277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4435865806605956556737477 831724838738616854388277)
                    ·
                      rfl

theorem cell23_4859335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_4859335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859335 prefixEnd_4859335 := by exact prefixLift 4859335
  have htrace : WordTrace (prefixWord ++ tailWord_4859335) baseStart_4859335 baseEnd_4859335 := by
    simpa [prefixWord, tailWord_4859335, baseEnd_4859335] using wordTrace_append hprefix tailTrace_4859335
  have hstable : (prefixWord ++ tailWord_4859335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859335).length < 2 ^ (prefixWord ++ tailWord_4859335).sum := by decide
  have hdescent : baseEnd_4859335 < baseStart_4859335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859365 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 8]
def baseStart_4859365 : Nat := 118140960795 + 4859365 * 2 ^ 59
def prefixEnd_4859365 : Nat := 4983230072969 + 3 ^ 40 * 4859365 * 2
def baseEnd_4859365 : Nat := 277243324515053938421077

theorem tailTrace_4859365 : CollatzResearch.WordTrace tailWord_4859365 prefixEnd_4859365 277243324515053938421077 := by
  unfold tailWord_4859365
  simp only [CollatzResearch.WordTrace]
  refine ⟨177235602040357993314323549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118157068026905328876215699 177235602040357993314323549)
  ·
    refine ⟨66463350765134247492871331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177235602040357993314323549 66463350765134247492871331)
    ·
      refine ⟨99695026147701371239306997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66463350765134247492871331 99695026147701371239306997)
      ·
        refine ⟨9346408701347003553685031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99695026147701371239306997 9346408701347003553685031)
        ·
          refine ⟨14019613052020505330527547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9346408701347003553685031 14019613052020505330527547)
          ·
            refine ⟨21029419578030757995791321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14019613052020505330527547 21029419578030757995791321)
            ·
              refine ⟨15772064683523068496843491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21029419578030757995791321 15772064683523068496843491)
              ·
                refine ⟨23658097025284602745265237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15772064683523068496843491 23658097025284602745265237)
                ·
                  refine ⟨277243324515053938421077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23658097025284602745265237 277243324515053938421077)
                  ·
                    rfl

theorem cell23_4859365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_4859365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859365 prefixEnd_4859365 := by exact prefixLift 4859365
  have htrace : WordTrace (prefixWord ++ tailWord_4859365) baseStart_4859365 baseEnd_4859365 := by
    simpa [prefixWord, tailWord_4859365, baseEnd_4859365] using wordTrace_append hprefix tailTrace_4859365
  have hstable : (prefixWord ++ tailWord_4859365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859365).length < 2 ^ (prefixWord ++ tailWord_4859365).sum := by decide
  have hdescent : baseEnd_4859365 < baseStart_4859365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859382 : List Nat := [5, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_4859382 : Nat := 118140960795 + 4859382 * 2 ^ 59
def prefixEnd_4859382 : Nat := 4983230072969 + 3 ^ 40 * 4859382 * 2
def baseEnd_4859382 : Nat := 277244294422956875475235

theorem tailTrace_4859382 : CollatzResearch.WordTrace tailWord_4859382 prefixEnd_4859382 277244294422956875475235 := by
  unfold tailWord_4859382
  simp only [CollatzResearch.WordTrace]
  refine ⟨11077263880081025326105775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118157481387530936811794933 11077263880081025326105775)
  ·
    refine ⟨16615895820121537989158663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11077263880081025326105775 16615895820121537989158663)
    ·
      refine ⟨24923843730182306983737995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16615895820121537989158663 24923843730182306983737995)
      ·
        refine ⟨37385765595273460475606993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24923843730182306983737995 37385765595273460475606993)
        ·
          refine ⟨28039324196455095356705245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37385765595273460475606993 28039324196455095356705245)
          ·
            refine ⟨10514746573670660758764467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28039324196455095356705245 10514746573670660758764467)
            ·
              refine ⟨15772119860505991138146701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10514746573670660758764467 15772119860505991138146701)
              ·
                refine ⟨5914544947689746676805013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15772119860505991138146701 5914544947689746676805013)
                ·
                  refine ⟨277244294422956875475235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5914544947689746676805013 277244294422956875475235)
                  ·
                    rfl

theorem cell23_4859382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_4859382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859382 prefixEnd_4859382 := by exact prefixLift 4859382
  have htrace : WordTrace (prefixWord ++ tailWord_4859382) baseStart_4859382 baseEnd_4859382 := by
    simpa [prefixWord, tailWord_4859382, baseEnd_4859382] using wordTrace_append hprefix tailTrace_4859382
  have hstable : (prefixWord ++ tailWord_4859382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859382).length < 2 ^ (prefixWord ++ tailWord_4859382).sum := by decide
  have hdescent : baseEnd_4859382 < baseStart_4859382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859395 : List Nat := [1, 1, 1, 3, 2, 1, 2, 6, 1, 5]
def baseStart_4859395 : Nat := 118140960795 + 4859395 * 2 ^ 59
def prefixEnd_4859395 : Nat := 4983230072969 + 3 ^ 40 * 4859395 * 2
def baseEnd_4859395 : Nat := 831735108351706776138185

theorem tailTrace_4859395 : CollatzResearch.WordTrace tailWord_4859395 prefixEnd_4859395 831735108351706776138185 := by
  unfold tailWord_4859395
  simp only [CollatzResearch.WordTrace]
  refine ⟨177236696230249308437915639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118157797486832872291943759 177236696230249308437915639)
  ·
    refine ⟨265855044345373962656873459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177236696230249308437915639 265855044345373962656873459)
    ·
      refine ⟨398782566518060943985310189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265855044345373962656873459 398782566518060943985310189)
      ·
        refine ⟨149543462444272853994491321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 398782566518060943985310189 149543462444272853994491321)
        ·
          refine ⟨112157596833204640495868491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149543462444272853994491321 112157596833204640495868491)
          ·
            refine ⟨168236395249806960743802737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112157596833204640495868491 168236395249806960743802737)
            ·
              refine ⟨126177296437355220557852053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168236395249806960743802737 126177296437355220557852053)
              ·
                refine ⟨5914560770501025963649315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126177296437355220557852053 5914560770501025963649315)
                ·
                  refine ⟨8871841155751538945473973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5914560770501025963649315 8871841155751538945473973)
                  ·
                    refine ⟨831735108351706776138185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8871841155751538945473973 831735108351706776138185)
                    ·
                      rfl

theorem cell23_4859395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 5].length) (baseStart_4859395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859395 prefixEnd_4859395 := by exact prefixLift 4859395
  have htrace : WordTrace (prefixWord ++ tailWord_4859395) baseStart_4859395 baseEnd_4859395 := by
    simpa [prefixWord, tailWord_4859395, baseEnd_4859395] using wordTrace_append hprefix tailTrace_4859395
  have hstable : (prefixWord ++ tailWord_4859395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859395).length < 2 ^ (prefixWord ++ tailWord_4859395).sum := by decide
  have hdescent : baseEnd_4859395 < baseStart_4859395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859409 : List Nat := [1, 2, 2, 1, 1, 2, 4, 5, 1, 1, 3]
def baseStart_4859409 : Nat := 118140960795 + 4859409 * 2 ^ 59
def prefixEnd_4859409 : Nat := 4983230072969 + 3 ^ 40 * 4859409 * 2
def baseEnd_4859409 : Nat := 2495212513784283273639491

theorem tailTrace_4859409 : CollatzResearch.WordTrace tailWord_4859409 prefixEnd_4859409 2495212513784283273639491 := by
  unfold tailWord_4859409
  simp only [CollatzResearch.WordTrace]
  refine ⟨177237206852198588828925281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118158137901465725885950187 177237206852198588828925281)
  ·
    refine ⟨132927905139148941621693961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177237206852198588828925281 132927905139148941621693961)
    ·
      refine ⟨99695928854361706216270471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132927905139148941621693961 99695928854361706216270471)
      ·
        refine ⟨149543893281542559324405707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99695928854361706216270471 149543893281542559324405707)
        ·
          refine ⟨224315839922313838986608561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149543893281542559324405707 224315839922313838986608561)
          ·
            refine ⟨168236879941735379239956421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224315839922313838986608561 168236879941735379239956421)
            ·
              refine ⟨31544414989075383607491829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168236879941735379239956421 31544414989075383607491829)
              ·
                refine ⟨2957288905225817213202359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31544414989075383607491829 2957288905225817213202359)
                ·
                  refine ⟨4435933357838725819803539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957288905225817213202359 4435933357838725819803539)
                  ·
                    refine ⟨6653900036758088729705309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4435933357838725819803539 6653900036758088729705309)
                    ·
                      refine ⟨2495212513784283273639491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6653900036758088729705309 2495212513784283273639491)
                      ·
                        rfl

theorem cell23_4859409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 1, 1, 3].length) (baseStart_4859409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859409 prefixEnd_4859409 := by exact prefixLift 4859409
  have htrace : WordTrace (prefixWord ++ tailWord_4859409) baseStart_4859409 baseEnd_4859409 := by
    simpa [prefixWord, tailWord_4859409, baseEnd_4859409] using wordTrace_append hprefix tailTrace_4859409
  have hstable : (prefixWord ++ tailWord_4859409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859409).length < 2 ^ (prefixWord ++ tailWord_4859409).sum := by decide
  have hdescent : baseEnd_4859409 < baseStart_4859409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859449 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 5, 2, 2]
def baseStart_4859449 : Nat := 118140960795 + 4859449 * 2 ^ 59
def prefixEnd_4859449 : Nat := 4983230072969 + 3 ^ 40 * 4859449 * 2
def baseEnd_4859449 : Nat := 2495233053010463117139307

theorem tailTrace_4859449 : CollatzResearch.WordTrace tailWord_4859449 prefixEnd_4859449 2495233053010463117139307 := by
  unfold tailWord_4859449
  simp only [CollatzResearch.WordTrace]
  refine ⟨177238665772053675660381401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118159110514702450440254267 177238665772053675660381401)
  ·
    refine ⟨132928999329040256745286051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177238665772053675660381401 132928999329040256745286051)
    ·
      refine ⟨199393498993560385117929077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132928999329040256745286051 199393498993560385117929077)
      ·
        refine ⟨18693140530646286104805851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 199393498993560385117929077 18693140530646286104805851)
        ·
          refine ⟨28039710795969429157208777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18693140530646286104805851 28039710795969429157208777)
          ·
            refine ⟨21029783096977071867906583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28039710795969429157208777 21029783096977071867906583)
            ·
              refine ⟨31544674645465607801859875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21029783096977071867906583 31544674645465607801859875)
              ·
                refine ⟨47317011968198411702789813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31544674645465607801859875 47317011968198411702789813)
                ·
                  refine ⟨4435969872018601097136545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47317011968198411702789813 4435969872018601097136545)
                  ·
                    refine ⟨3326977404013950822852409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4435969872018601097136545 3326977404013950822852409)
                    ·
                      refine ⟨2495233053010463117139307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3326977404013950822852409 2495233053010463117139307)
                      ·
                        rfl

theorem cell23_4859449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_4859449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859449 prefixEnd_4859449 := by exact prefixLift 4859449
  have htrace : WordTrace (prefixWord ++ tailWord_4859449) baseStart_4859449 baseEnd_4859449 := by
    simpa [prefixWord, tailWord_4859449, baseEnd_4859449] using wordTrace_append hprefix tailTrace_4859449
  have hstable : (prefixWord ++ tailWord_4859449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859449).length < 2 ^ (prefixWord ++ tailWord_4859449).sum := by decide
  have hdescent : baseEnd_4859449 < baseStart_4859449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859453 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 2, 3, 2]
def baseStart_4859453 : Nat := 118140960795 + 4859453 * 2 ^ 59
def prefixEnd_4859453 : Nat := 4983230072969 + 3 ^ 40 * 4859453 * 2
def baseEnd_4859453 : Nat := 2495235106933081101489289

theorem tailTrace_4859453 : CollatzResearch.WordTrace tailWord_4859453 prefixEnd_4859453 2495235106933081101489289 := by
  unfold tailWord_4859453
  simp only [CollatzResearch.WordTrace]
  refine ⟨177238811664039184343527013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118159207776026122895684675 177238811664039184343527013)
  ·
    refine ⟨33232277187007347064411315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177238811664039184343527013 33232277187007347064411315)
    ·
      refine ⟨49848415780511020596616973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33232277187007347064411315 49848415780511020596616973)
      ·
        refine ⟨18693155917691632723731365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49848415780511020596616973 18693155917691632723731365)
        ·
          refine ⟨3504966734567181135699631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18693155917691632723731365 3504966734567181135699631)
          ·
            refine ⟨5257450101850771703549447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3504966734567181135699631 5257450101850771703549447)
            ·
              refine ⟨7886175152776157555324171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5257450101850771703549447 7886175152776157555324171)
              ·
                refine ⟨11829262729164236332986257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7886175152776157555324171 11829262729164236332986257)
                ·
                  refine ⟨8871947046873177249739693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11829262729164236332986257 8871947046873177249739693)
                  ·
                    refine ⟨3326980142577441468652385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8871947046873177249739693 3326980142577441468652385)
                    ·
                      refine ⟨2495235106933081101489289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3326980142577441468652385 2495235106933081101489289)
                      ·
                        rfl

theorem cell23_4859453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_4859453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859453 prefixEnd_4859453 := by exact prefixLift 4859453
  have htrace : WordTrace (prefixWord ++ tailWord_4859453) baseStart_4859453 baseEnd_4859453 := by
    simpa [prefixWord, tailWord_4859453, baseEnd_4859453] using wordTrace_append hprefix tailTrace_4859453
  have hstable : (prefixWord ++ tailWord_4859453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859453).length < 2 ^ (prefixWord ++ tailWord_4859453).sum := by decide
  have hdescent : baseEnd_4859453 < baseStart_4859453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859505 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_4859505 : Nat := 118140960795 + 4859505 * 2 ^ 59
def prefixEnd_4859505 : Nat := 4983230072969 + 3 ^ 40 * 4859505 * 2
def baseEnd_4859505 : Nat := 2495261807927114898039049

theorem tailTrace_4859505 : CollatzResearch.WordTrace tailWord_4859505 prefixEnd_4859505 2495261807927114898039049 := by
  unfold tailWord_4859505
  simp only [CollatzResearch.WordTrace]
  refine ⟨177240708259850797224419969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118160472173233864816279979 177240708259850797224419969)
  ·
    refine ⟨132930531194888097918314977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177240708259850797224419969 132930531194888097918314977)
    ·
      refine ⟨99697898396166073438736233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132930531194888097918314977 99697898396166073438736233)
      ·
        refine ⟨74773423797124555079052175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99697898396166073438736233 74773423797124555079052175)
        ·
          refine ⟨112160135695686832618578263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74773423797124555079052175 112160135695686832618578263)
          ·
            refine ⟨168240203543530248927867395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112160135695686832618578263 168240203543530248927867395)
            ·
              refine ⟨252360305315295373391801093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168240203543530248927867395 252360305315295373391801093)
              ·
                refine ⟨47317557246617882510962705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252360305315295373391801093 47317557246617882510962705)
                ·
                  refine ⟨35488167934963411883222029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47317557246617882510962705 35488167934963411883222029)
                  ·
                    refine ⟨13308062975611279456208261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35488167934963411883222029 13308062975611279456208261)
                    ·
                      refine ⟨2495261807927114898039049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13308062975611279456208261 2495261807927114898039049)
                      ·
                        rfl

theorem cell23_4859505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_4859505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859505 prefixEnd_4859505 := by exact prefixLift 4859505
  have htrace : WordTrace (prefixWord ++ tailWord_4859505) baseStart_4859505 baseEnd_4859505 := by
    simpa [prefixWord, tailWord_4859505, baseEnd_4859505] using wordTrace_append hprefix tailTrace_4859505
  have hstable : (prefixWord ++ tailWord_4859505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859505).length < 2 ^ (prefixWord ++ tailWord_4859505).sum := by decide
  have hdescent : baseEnd_4859505 < baseStart_4859505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859545 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 7]
def baseStart_4859545 : Nat := 118140960795 + 4859545 * 2 ^ 59
def prefixEnd_4859545 : Nat := 4983230072969 + 3 ^ 40 * 4859545 * 2
def baseEnd_4859545 : Nat := 277253594128143860170985

theorem tailTrace_4859545 : CollatzResearch.WordTrace tailWord_4859545 prefixEnd_4859545 277253594128143860170985 := by
  unfold tailWord_4859545
  simp only [CollatzResearch.WordTrace]
  refine ⟨177242167179705884055876089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118161444786470589370584059 177242167179705884055876089)
  ·
    refine ⟨132931625384779413041907067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177242167179705884055876089 132931625384779413041907067)
    ·
      refine ⟨199397438077169119562860601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132931625384779413041907067 199397438077169119562860601)
      ·
        refine ⟨149548078557876839672145451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199397438077169119562860601 149548078557876839672145451)
        ·
          refine ⟨224322117836815259508218177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149548078557876839672145451 224322117836815259508218177)
          ·
            refine ⟨168241588377611444631163633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224322117836815259508218177 168241588377611444631163633)
            ·
              refine ⟨126181191283208583473372725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168241588377611444631163633 126181191283208583473372725)
              ·
                refine ⟨11829486682800804700628693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126181191283208583473372725 11829486682800804700628693)
                ·
                  refine ⟨277253594128143860170985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11829486682800804700628693 277253594128143860170985)
                  ·
                    rfl

theorem cell23_4859545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 7].length) (baseStart_4859545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859545 prefixEnd_4859545 := by exact prefixLift 4859545
  have htrace : WordTrace (prefixWord ++ tailWord_4859545) baseStart_4859545 baseEnd_4859545 := by
    simpa [prefixWord, tailWord_4859545, baseEnd_4859545] using wordTrace_append hprefix tailTrace_4859545
  have hstable : (prefixWord ++ tailWord_4859545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859545).length < 2 ^ (prefixWord ++ tailWord_4859545).sum := by decide
  have hdescent : baseEnd_4859545 < baseStart_4859545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859550 : List Nat := [4, 3, 1, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_4859550 : Nat := 118140960795 + 4859550 * 2 ^ 59
def prefixEnd_4859550 : Nat := 4983230072969 + 3 ^ 40 * 4859550 * 2
def baseEnd_4859550 : Nat := 2495284914556567221976343

theorem tailTrace_4859550 : CollatzResearch.WordTrace tailWord_4859550 prefixEnd_4859550 2495284914556567221976343 := by
  unfold tailWord_4859550
  simp only [CollatzResearch.WordTrace]
  refine ⟨22155293693085971238726013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118161566363125179939872069 22155293693085971238726013)
  ·
    refine ⟨8308235134907239214522255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22155293693085971238726013 8308235134907239214522255)
    ·
      refine ⟨12462352702360858821783383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8308235134907239214522255 12462352702360858821783383)
      ·
        refine ⟨18693529053541288232675075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12462352702360858821783383 18693529053541288232675075)
        ·
          refine ⟨28040293580311932349012613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18693529053541288232675075 28040293580311932349012613)
          ·
            refine ⟨5257555046308487315439865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28040293580311932349012613 5257555046308487315439865)
            ·
              refine ⟨3943166284731365486579899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5257555046308487315439865 3943166284731365486579899)
              ·
                refine ⟨5914749427097048229869849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943166284731365486579899 5914749427097048229869849)
                ·
                  refine ⟨4436062070322786172402387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5914749427097048229869849 4436062070322786172402387)
                  ·
                    refine ⟨6654093105484179258603581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4436062070322786172402387 6654093105484179258603581)
                    ·
                      refine ⟨2495284914556567221976343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6654093105484179258603581 2495284914556567221976343)
                      ·
                        rfl

theorem cell23_4859550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_4859550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859550 prefixEnd_4859550 := by exact prefixLift 4859550
  have htrace : WordTrace (prefixWord ++ tailWord_4859550) baseStart_4859550 baseEnd_4859550 := by
    simpa [prefixWord, tailWord_4859550, baseEnd_4859550] using wordTrace_append hprefix tailTrace_4859550
  have hstable : (prefixWord ++ tailWord_4859550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859550).length < 2 ^ (prefixWord ++ tailWord_4859550).sum := by decide
  have hdescent : baseEnd_4859550 < baseStart_4859550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859560 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4859560 : Nat := 118140960795 + 4859560 * 2 ^ 59
def prefixEnd_4859560 : Nat := 4983230072969 + 3 ^ 40 * 4859560 * 2
def baseEnd_4859560 : Nat := 2495290049363112182851297

theorem tailTrace_4859560 : CollatzResearch.WordTrace tailWord_4859560 prefixEnd_4859560 2495290049363112182851297 := by
  unfold tailWord_4859560
  simp only [CollatzResearch.WordTrace]
  refine ⟨88621357137325770808836067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118161809516434361078448089 88621357137325770808836067)
  ·
    refine ⟨132932035705988656213254101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88621357137325770808836067 132932035705988656213254101)
    ·
      refine ⟨3115594586859109129998143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 132932035705988656213254101 3115594586859109129998143)
      ·
        refine ⟨4673391880288663694997215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3115594586859109129998143 4673391880288663694997215)
        ·
          refine ⟨7010087820432995542495823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4673391880288663694997215 7010087820432995542495823)
          ·
            refine ⟨10515131730649493313743735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7010087820432995542495823 10515131730649493313743735)
            ·
              refine ⟨15772697595974239970615603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10515131730649493313743735 15772697595974239970615603)
              ·
                refine ⟨23659046393961359955923405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15772697595974239970615603 23659046393961359955923405)
                ·
                  refine ⟨8872142397735509983471277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23659046393961359955923405 8872142397735509983471277)
                  ·
                    refine ⟨3327053399150816243801729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8872142397735509983471277 3327053399150816243801729)
                    ·
                      refine ⟨2495290049363112182851297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327053399150816243801729 2495290049363112182851297)
                      ·
                        rfl

theorem cell23_4859560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4859560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859560 prefixEnd_4859560 := by exact prefixLift 4859560
  have htrace : WordTrace (prefixWord ++ tailWord_4859560) baseStart_4859560 baseEnd_4859560 := by
    simpa [prefixWord, tailWord_4859560, baseEnd_4859560] using wordTrace_append hprefix tailTrace_4859560
  have hstable : (prefixWord ++ tailWord_4859560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859560).length < 2 ^ (prefixWord ++ tailWord_4859560).sum := by decide
  have hdescent : baseEnd_4859560 < baseStart_4859560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859592 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 2, 5]
def baseStart_4859592 : Nat := 118140960795 + 4859592 * 2 ^ 59
def prefixEnd_4859592 : Nat := 4983230072969 + 3 ^ 40 * 4859592 * 2
def baseEnd_4859592 : Nat := 831768826914685352550383

theorem tailTrace_4859592 : CollatzResearch.WordTrace tailWord_4859592 prefixEnd_4859592 831768826914685352550383 := by
  unfold tailWord_4859592
  simp only [CollatzResearch.WordTrace]
  refine ⟨88621940705267805541418515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118162587607023740721891353 88621940705267805541418515)
  ·
    refine ⟨132932911057901708312127773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88621940705267805541418515 132932911057901708312127773)
    ·
      refine ⟨49849841646713140617047915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132932911057901708312127773 49849841646713140617047915)
      ·
        refine ⟨74774762470069710925571873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49849841646713140617047915 74774762470069710925571873)
        ·
          refine ⟨56081071852552283194178905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74774762470069710925571873 56081071852552283194178905)
          ·
            refine ⟨42060803889414212395634179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56081071852552283194178905 42060803889414212395634179)
            ·
              refine ⟨63091205834121318593451269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42060803889414212395634179 63091205834121318593451269)
              ·
                refine ⟨11829601093897747236272113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63091205834121318593451269 11829601093897747236272113)
                ·
                  refine ⟨8872200820423310427204085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11829601093897747236272113 8872200820423310427204085)
                  ·
                    refine ⟨831768826914685352550383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8872200820423310427204085 831768826914685352550383)
                    ·
                      rfl

theorem cell23_4859592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_4859592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859592 prefixEnd_4859592 := by exact prefixLift 4859592
  have htrace : WordTrace (prefixWord ++ tailWord_4859592) baseStart_4859592 baseEnd_4859592 := by
    simpa [prefixWord, tailWord_4859592, baseEnd_4859592] using wordTrace_append hprefix tailTrace_4859592
  have hstable : (prefixWord ++ tailWord_4859592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859592).length < 2 ^ (prefixWord ++ tailWord_4859592).sum := by decide
  have hdescent : baseEnd_4859592 < baseStart_4859592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859596 : List Nat := [2, 2, 1, 5, 2, 1, 1, 4, 5]
def baseStart_4859596 : Nat := 118140960795 + 4859596 * 2 ^ 59
def prefixEnd_4859596 : Nat := 4983230072969 + 3 ^ 40 * 4859596 * 2
def baseEnd_4859596 : Nat := 277256503851852671333459

theorem tailTrace_4859596 : CollatzResearch.WordTrace tailWord_4859596 prefixEnd_4859596 277256503851852671333459 := by
  unfold tailWord_4859596
  simp only [CollatzResearch.WordTrace]
  refine ⟨88622013651260559882991321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118162684868347413177321761 88622013651260559882991321)
  ·
    refine ⟨66466510238445419912243491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88622013651260559882991321 66466510238445419912243491)
    ·
      refine ⟨99699765357668129868365237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66466510238445419912243491 99699765357668129868365237)
      ·
        refine ⟨9346853002281387175159241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99699765357668129868365237 9346853002281387175159241)
        ·
          refine ⟨7010139751711040381369431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9346853002281387175159241 7010139751711040381369431)
          ·
            refine ⟨10515209627566560572054147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7010139751711040381369431 10515209627566560572054147)
            ·
              refine ⟨15772814441349840858081221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10515209627566560572054147 15772814441349840858081221)
              ·
                refine ⟨2957402707753095160890229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15772814441349840858081221 2957402707753095160890229)
                ·
                  refine ⟨277256503851852671333459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2957402707753095160890229 277256503851852671333459)
                  ·
                    rfl

theorem cell23_4859596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 5].length) (baseStart_4859596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859596 prefixEnd_4859596 := by exact prefixLift 4859596
  have htrace : WordTrace (prefixWord ++ tailWord_4859596) baseStart_4859596 baseEnd_4859596 := by
    simpa [prefixWord, tailWord_4859596, baseEnd_4859596] using wordTrace_append hprefix tailTrace_4859596
  have hstable : (prefixWord ++ tailWord_4859596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859596).length < 2 ^ (prefixWord ++ tailWord_4859596).sum := by decide
  have hdescent : baseEnd_4859596 < baseStart_4859596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859629 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_4859629 : Nat := 118140960795 + 4859629 * 2 ^ 59
def prefixEnd_4859629 : Nat := 4983230072969 + 3 ^ 40 * 4859629 * 2
def baseEnd_4859629 : Nat := 2495325479528272412888479

theorem tailTrace_4859629 : CollatzResearch.WordTrace tailWord_4859629 prefixEnd_4859629 2495325479528272412888479 := by
  unfold tailWord_4859629
  simp only [CollatzResearch.WordTrace]
  refine ⟨177245230911401566401933941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118163487274267710934622627 177245230911401566401933941)
  ·
    refine ⟨16616740397943896850181307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177245230911401566401933941 16616740397943896850181307)
    ·
      refine ⟨24925110596915845275271961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16616740397943896850181307 24925110596915845275271961)
      ·
        refine ⟨18693832947686883956453971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24925110596915845275271961 18693832947686883956453971)
        ·
          refine ⟨28040749421530325934680957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18693832947686883956453971 28040749421530325934680957)
          ·
            refine ⟨10515281033073872225505359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28040749421530325934680957 10515281033073872225505359)
            ·
              refine ⟨15772921549610808338258039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10515281033073872225505359 15772921549610808338258039)
              ·
                refine ⟨23659382324416212507387059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15772921549610808338258039 23659382324416212507387059)
                ·
                  refine ⟨35489073486624318761080589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23659382324416212507387059 35489073486624318761080589)
                  ·
                    refine ⟨13308402557484119535405221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35489073486624318761080589 13308402557484119535405221)
                    ·
                      refine ⟨2495325479528272412888479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13308402557484119535405221 2495325479528272412888479)
                      ·
                        rfl

theorem cell23_4859629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_4859629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859629 prefixEnd_4859629 := by exact prefixLift 4859629
  have htrace : WordTrace (prefixWord ++ tailWord_4859629) baseStart_4859629 baseEnd_4859629 := by
    simpa [prefixWord, tailWord_4859629, baseEnd_4859629] using wordTrace_append hprefix tailTrace_4859629
  have hstable : (prefixWord ++ tailWord_4859629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859629).length < 2 ^ (prefixWord ++ tailWord_4859629).sum := by decide
  have hdescent : baseEnd_4859629 < baseStart_4859629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859649 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_4859649 : Nat := 118140960795 + 4859649 * 2 ^ 59
def prefixEnd_4859649 : Nat := 4983230072969 + 3 ^ 40 * 4859649 * 2
def baseEnd_4859649 : Nat := 2495335749141362334638387

theorem tailTrace_4859649 : CollatzResearch.WordTrace tailWord_4859649 prefixEnd_4859649 2495335749141362334638387 := by
  unfold tailWord_4859649
  simp only [CollatzResearch.WordTrace]
  refine ⟨177245960371329109817662001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118163973580886073211774667 177245960371329109817662001)
  ·
    refine ⟨132934470278496832363246501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177245960371329109817662001 132934470278496832363246501)
    ·
      refine ⟨24925213177218156068108719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132934470278496832363246501 24925213177218156068108719)
      ·
        refine ⟨37387819765827234102163079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24925213177218156068108719 37387819765827234102163079)
        ·
          refine ⟨56081729648740851153244619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37387819765827234102163079 56081729648740851153244619)
          ·
            refine ⟨84122594473111276729866929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56081729648740851153244619 84122594473111276729866929)
            ·
              refine ⟨63091945854833457547400197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84122594473111276729866929 63091945854833457547400197)
              ·
                refine ⟨11829739847781273290137537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63091945854833457547400197 11829739847781273290137537)
                ·
                  refine ⟨8872304885835954967603153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11829739847781273290137537 8872304885835954967603153)
                  ·
                    refine ⟨6654228664376966225702365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8872304885835954967603153 6654228664376966225702365)
                    ·
                      refine ⟨2495335749141362334638387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6654228664376966225702365 2495335749141362334638387)
                      ·
                        rfl

theorem cell23_4859649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_4859649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859649 prefixEnd_4859649 := by exact prefixLift 4859649
  have htrace : WordTrace (prefixWord ++ tailWord_4859649) baseStart_4859649 baseEnd_4859649 := by
    simpa [prefixWord, tailWord_4859649, baseEnd_4859649] using wordTrace_append hprefix tailTrace_4859649
  have hstable : (prefixWord ++ tailWord_4859649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859649).length < 2 ^ (prefixWord ++ tailWord_4859649).sum := by decide
  have hdescent : baseEnd_4859649 < baseStart_4859649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859656 : List Nat := [2, 1, 3, 2, 2, 1, 1, 6, 1, 4]
def baseStart_4859656 : Nat := 118140960795 + 4859656 * 2 ^ 59
def prefixEnd_4859656 : Nat := 4983230072969 + 3 ^ 40 * 4859656 * 2
def baseEnd_4859656 : Nat := 831779781168647935750285

theorem tailTrace_4859656 : CollatzResearch.WordTrace tailWord_4859656 prefixEnd_4859656 831779781168647935750285 := by
  unfold tailWord_4859656
  simp only [CollatzResearch.WordTrace]
  refine ⟨88623107841151875006583411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118164143788202500008777881 88623107841151875006583411)
  ·
    refine ⟨132934661761727812509875117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88623107841151875006583411 132934661761727812509875117)
    ·
      refine ⟨49850498160647929691203169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132934661761727812509875117 49850498160647929691203169)
      ·
        refine ⟨37387873620485947268402377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49850498160647929691203169 37387873620485947268402377)
        ·
          refine ⟨28040905215364460451301783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37387873620485947268402377 28040905215364460451301783)
          ·
            refine ⟨42061357823046690676952675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28040905215364460451301783 42061357823046690676952675)
            ·
              refine ⟨63092036734570036015429013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42061357823046690676952675 63092036734570036015429013)
              ·
                refine ⟨2957439221932970438223235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63092036734570036015429013 2957439221932970438223235)
                ·
                  refine ⟨4436158832899455657334853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957439221932970438223235 4436158832899455657334853)
                  ·
                    refine ⟨831779781168647935750285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4436158832899455657334853 831779781168647935750285)
                    ·
                      rfl

theorem cell23_4859656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_4859656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859656 prefixEnd_4859656 := by exact prefixLift 4859656
  have htrace : WordTrace (prefixWord ++ tailWord_4859656) baseStart_4859656 baseEnd_4859656 := by
    simpa [prefixWord, tailWord_4859656, baseEnd_4859656] using wordTrace_append hprefix tailTrace_4859656
  have hstable : (prefixWord ++ tailWord_4859656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859656).length < 2 ^ (prefixWord ++ tailWord_4859656).sum := by decide
  have hdescent : baseEnd_4859656 < baseStart_4859656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859666 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_4859666 : Nat := 118140960795 + 4859666 * 2 ^ 59
def prefixEnd_4859666 : Nat := 4983230072969 + 3 ^ 40 * 4859666 * 2
def baseEnd_4859666 : Nat := 2495344478312488768125809

theorem tailTrace_4859666 : CollatzResearch.WordTrace tailWord_4859666 prefixEnd_4859666 2495344478312488768125809 := by
  unfold tailWord_4859666
  simp only [CollatzResearch.WordTrace]
  refine ⟨44311645103066880430257713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118164386941511681147353901 44311645103066880430257713)
  ·
    refine ⟨33233733827300160322693285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44311645103066880430257713 33233733827300160322693285)
    ·
      refine ⟨6231325092618780060504991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33233733827300160322693285 6231325092618780060504991)
      ·
        refine ⟨9346987638928170090757487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6231325092618780060504991 9346987638928170090757487)
        ·
          refine ⟨14020481458392255136136231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9346987638928170090757487 14020481458392255136136231)
          ·
            refine ⟨21030722187588382704204347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14020481458392255136136231 21030722187588382704204347)
            ·
              refine ⟨31546083281382574056306521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21030722187588382704204347 31546083281382574056306521)
              ·
                refine ⟨23659562461036930542229891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31546083281382574056306521 23659562461036930542229891)
                ·
                  refine ⟨35489343691555395813344837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23659562461036930542229891 35489343691555395813344837)
                  ·
                    refine ⟨6654251942166636715002157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35489343691555395813344837 6654251942166636715002157)
                    ·
                      refine ⟨2495344478312488768125809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6654251942166636715002157 2495344478312488768125809)
                      ·
                        rfl

theorem cell23_4859666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_4859666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859666 prefixEnd_4859666 := by exact prefixLift 4859666
  have htrace : WordTrace (prefixWord ++ tailWord_4859666) baseStart_4859666 baseEnd_4859666 := by
    simpa [prefixWord, tailWord_4859666, baseEnd_4859666] using wordTrace_append hprefix tailTrace_4859666
  have hstable : (prefixWord ++ tailWord_4859666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859666).length < 2 ^ (prefixWord ++ tailWord_4859666).sum := by decide
  have hdescent : baseEnd_4859666 < baseStart_4859666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859706 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2]
def baseStart_4859706 : Nat := 118140960795 + 4859706 * 2 ^ 59
def prefixEnd_4859706 : Nat := 4983230072969 + 3 ^ 40 * 4859706 * 2
def baseEnd_4859706 : Nat := 2495365017538668611625625

theorem tailTrace_4859706 : CollatzResearch.WordTrace tailWord_4859706 prefixEnd_4859706 2495365017538668611625625 := by
  unfold tailWord_4859706
  simp only [CollatzResearch.WordTrace]
  refine ⟨44312009833030652138121743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118165359554748405701657981 44312009833030652138121743)
  ·
    refine ⟨66468014749545978207182615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44312009833030652138121743 66468014749545978207182615)
    ·
      refine ⟨99702022124318967310773923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66468014749545978207182615 99702022124318967310773923)
      ·
        refine ⟨149553033186478450966160885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99702022124318967310773923 149553033186478450966160885)
        ·
          refine ⟨14020596861232354778077583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149553033186478450966160885 14020596861232354778077583)
          ·
            refine ⟨21030895291848532167116375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14020596861232354778077583 21030895291848532167116375)
            ·
              refine ⟨31546342937772798250674563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21030895291848532167116375 31546342937772798250674563)
              ·
                refine ⟨47319514406659197376011845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31546342937772798250674563 47319514406659197376011845)
                ·
                  refine ⟨8872408951248599508002221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47319514406659197376011845 8872408951248599508002221)
                  ·
                    refine ⟨3327153356718224815500833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8872408951248599508002221 3327153356718224815500833)
                    ·
                      refine ⟨2495365017538668611625625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327153356718224815500833 2495365017538668611625625)
                      ·
                        rfl

theorem cell23_4859706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2].length) (baseStart_4859706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859706 prefixEnd_4859706 := by exact prefixLift 4859706
  have htrace : WordTrace (prefixWord ++ tailWord_4859706) baseStart_4859706 baseEnd_4859706 := by
    simpa [prefixWord, tailWord_4859706, baseEnd_4859706] using wordTrace_append hprefix tailTrace_4859706
  have hstable : (prefixWord ++ tailWord_4859706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859706).length < 2 ^ (prefixWord ++ tailWord_4859706).sum := by decide
  have hdescent : baseEnd_4859706 < baseStart_4859706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859740 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_4859740 : Nat := 118140960795 + 4859740 * 2 ^ 59
def prefixEnd_4859740 : Nat := 4983230072969 + 3 ^ 40 * 4859740 * 2
def baseEnd_4859740 : Nat := 2495382475880921478600469

theorem tailTrace_4859740 : CollatzResearch.WordTrace tailWord_4859740 prefixEnd_4859740 2495382475880921478600469 := by
  unfold tailWord_4859740
  simp only [CollatzResearch.WordTrace]
  refine ⟨88624639706999716179612337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118166186275999621572816449 88624639706999716179612337)
  ·
    refine ⟨66468479780249787134709253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88624639706999716179612337 66468479780249787134709253)
    ·
      refine ⟨12462839958796835087757985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66468479780249787134709253 12462839958796835087757985)
      ·
        refine ⟨9347129969097626315818489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12462839958796835087757985 9347129969097626315818489)
        ·
          refine ⟨7010347476823219736863867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9347129969097626315818489 7010347476823219736863867)
          ·
            refine ⟨10515521215234829605295801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7010347476823219736863867 10515521215234829605295801)
            ·
              refine ⟨7886640911426122203971851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10515521215234829605295801 7886640911426122203971851)
              ·
                refine ⟨11829961367139183305957777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7886640911426122203971851 11829961367139183305957777)
                ·
                  refine ⟨8872471025354387479468333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11829961367139183305957777 8872471025354387479468333)
                  ·
                    refine ⟨3327176634507895304800625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8872471025354387479468333 3327176634507895304800625)
                    ·
                      refine ⟨2495382475880921478600469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327176634507895304800625 2495382475880921478600469)
                      ·
                        rfl

theorem cell23_4859740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_4859740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859740 prefixEnd_4859740 := by exact prefixLift 4859740
  have htrace : WordTrace (prefixWord ++ tailWord_4859740) baseStart_4859740 baseEnd_4859740 := by
    simpa [prefixWord, tailWord_4859740, baseEnd_4859740] using wordTrace_append hprefix tailTrace_4859740
  have hstable : (prefixWord ++ tailWord_4859740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859740).length < 2 ^ (prefixWord ++ tailWord_4859740).sum := by decide
  have hdescent : baseEnd_4859740 < baseStart_4859740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859746 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_4859746 : Nat := 118140960795 + 4859746 * 2 ^ 59
def prefixEnd_4859746 : Nat := 4983230072969 + 3 ^ 40 * 4859746 * 2
def baseEnd_4859746 : Nat := 831795185588282818375147

theorem tailTrace_4859746 : CollatzResearch.WordTrace tailWord_4859746 prefixEnd_4859746 831795185588282818375147 := by
  unfold tailWord_4859746
  simp only [CollatzResearch.WordTrace]
  refine ⟨44312374562994423845985773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118166332167985130255962061 44312374562994423845985773)
  ·
    refine ⟨16617140461122908942244665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44312374562994423845985773 16617140461122908942244665)
    ·
      refine ⟨12462855345842181706683499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16617140461122908942244665 12462855345842181706683499)
      ·
        refine ⟨18694283018763272560025249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12462855345842181706683499 18694283018763272560025249)
        ·
          refine ⟨14020712264072454420018937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18694283018763272560025249 14020712264072454420018937)
          ·
            refine ⟨10515534198054340815014203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14020712264072454420018937 10515534198054340815014203)
            ·
              refine ⟨15773301297081511222521305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10515534198054340815014203 15773301297081511222521305)
              ·
                refine ⟨11829975972811133416890979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15773301297081511222521305 11829975972811133416890979)
                ·
                  refine ⟨17744963959216700125336469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11829975972811133416890979 17744963959216700125336469)
                  ·
                    refine ⟨831795185588282818375147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17744963959216700125336469 831795185588282818375147)
                    ·
                      rfl

theorem cell23_4859746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_4859746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859746 prefixEnd_4859746 := by exact prefixLift 4859746
  have htrace : WordTrace (prefixWord ++ tailWord_4859746) baseStart_4859746 baseEnd_4859746 := by
    simpa [prefixWord, tailWord_4859746, baseEnd_4859746] using wordTrace_append hprefix tailTrace_4859746
  have hstable : (prefixWord ++ tailWord_4859746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859746).length < 2 ^ (prefixWord ++ tailWord_4859746).sum := by decide
  have hdescent : baseEnd_4859746 < baseStart_4859746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859756 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 5]
def baseStart_4859756 : Nat := 118140960795 + 4859756 * 2 ^ 59
def prefixEnd_4859756 : Nat := 4983230072969 + 3 ^ 40 * 4859756 * 2
def baseEnd_4859756 : Nat := 2495390691571393416000395

theorem tailTrace_4859756 : CollatzResearch.WordTrace tailWord_4859756 prefixEnd_4859756 2495390691571393416000395 := by
  unfold tailWord_4859756
  simp only [CollatzResearch.WordTrace]
  refine ⟨88624931490970733545903561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118166575321294311394538081 88624931490970733545903561)
  ·
    refine ⟨66468698618228050159427671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88624931490970733545903561 66468698618228050159427671)
    ·
      refine ⟨99703047927342075239141507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66468698618228050159427671 99703047927342075239141507)
      ·
        refine ⟨149554571891013112858712261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99703047927342075239141507 149554571891013112858712261)
        ·
          refine ⟨28041482229564958661008549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149554571891013112858712261 28041482229564958661008549)
          ·
            refine ⟨5257777918043429748939103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28041482229564958661008549 5257777918043429748939103)
            ·
              refine ⟨7886666877065144623408655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5257777918043429748939103 7886666877065144623408655)
              ·
                refine ⟨11830000315597716935112983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7886666877065144623408655 11830000315597716935112983)
                ·
                  refine ⟨17745000473396575402669475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11830000315597716935112983 17745000473396575402669475)
                  ·
                    refine ⟨26617500710094863104004213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17745000473396575402669475 26617500710094863104004213)
                    ·
                      refine ⟨2495390691571393416000395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26617500710094863104004213 2495390691571393416000395)
                      ·
                        rfl

theorem cell23_4859756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_4859756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859756 prefixEnd_4859756 := by exact prefixLift 4859756
  have htrace : WordTrace (prefixWord ++ tailWord_4859756) baseStart_4859756 baseEnd_4859756 := by
    simpa [prefixWord, tailWord_4859756, baseEnd_4859756] using wordTrace_append hprefix tailTrace_4859756
  have hstable : (prefixWord ++ tailWord_4859756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859756).length < 2 ^ (prefixWord ++ tailWord_4859756).sum := by decide
  have hdescent : baseEnd_4859756 < baseStart_4859756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859769 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 3, 3, 3]
def baseStart_4859769 : Nat := 118140960795 + 4859769 * 2 ^ 59
def prefixEnd_4859769 : Nat := 4983230072969 + 3 ^ 40 * 4859769 * 2
def baseEnd_4859769 : Nat := 2495397366819901865137835

theorem tailTrace_4859769 : CollatzResearch.WordTrace tailWord_4859769 prefixEnd_4859769 2495397366819901865137835 := by
  unfold tailWord_4859769
  simp only [CollatzResearch.WordTrace]
  refine ⟨177250337130894370312030361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118166891420596246874686907 177250337130894370312030361)
  ·
    refine ⟨132937752848170777734022771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177250337130894370312030361 132937752848170777734022771)
    ·
      refine ⟨199406629272256166601034157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132937752848170777734022771 199406629272256166601034157)
      ·
        refine ⟨74777485977096062475387809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199406629272256166601034157 74777485977096062475387809)
        ·
          refine ⟨56083114482822046856540857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74777485977096062475387809 56083114482822046856540857)
          ·
            refine ⟨42062335862116535142405643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56083114482822046856540857 42062335862116535142405643)
            ·
              refine ⟨63093503793174802713608465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42062335862116535142405643 63093503793174802713608465)
              ·
                refine ⟨47320127844881102035206349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63093503793174802713608465 47320127844881102035206349)
                ·
                  refine ⟨17745047941830413263202381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47320127844881102035206349 17745047941830413263202381)
                  ·
                    refine ⟨6654392978186404973700893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17745047941830413263202381 6654392978186404973700893)
                    ·
                      refine ⟨2495397366819901865137835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6654392978186404973700893 2495397366819901865137835)
                      ·
                        rfl

theorem cell23_4859769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_4859769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859769 prefixEnd_4859769 := by exact prefixLift 4859769
  have htrace : WordTrace (prefixWord ++ tailWord_4859769) baseStart_4859769 baseEnd_4859769 := by
    simpa [prefixWord, tailWord_4859769, baseEnd_4859769] using wordTrace_append hprefix tailTrace_4859769
  have hstable : (prefixWord ++ tailWord_4859769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859769).length < 2 ^ (prefixWord ++ tailWord_4859769).sum := by decide
  have hdescent : baseEnd_4859769 < baseStart_4859769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859792 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 8]
def baseStart_4859792 : Nat := 118140960795 + 4859792 * 2 ^ 59
def prefixEnd_4859792 : Nat := 4983230072969 + 3 ^ 40 * 4859792 * 2
def baseEnd_4859792 : Nat := 2495409176874955275150229

theorem tailTrace_4859792 : CollatzResearch.WordTrace tailWord_4859792 prefixEnd_4859792 2495409176874955275150229 := by
  unfold tailWord_4859792
  simp only [CollatzResearch.WordTrace]
  refine ⟨88625588004905522620058815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118167450673207363493411753 88625588004905522620058815)
  ·
    refine ⟨132938382007358283930088223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88625588004905522620058815 132938382007358283930088223)
    ·
      refine ⟨199407573011037425895132335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132938382007358283930088223 199407573011037425895132335)
      ·
        refine ⟨299111359516556138842698503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199407573011037425895132335 299111359516556138842698503)
        ·
          refine ⟨448667039274834208264047755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299111359516556138842698503 448667039274834208264047755)
          ·
            refine ⟨673000558912251312396071633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448667039274834208264047755 673000558912251312396071633)
            ·
              refine ⟨504750419184188484297053725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 673000558912251312396071633 504750419184188484297053725)
              ·
                refine ⟨189281407194070681611395147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 504750419184188484297053725 189281407194070681611395147)
                ·
                  refine ⟨283922110791106022417092721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189281407194070681611395147 283922110791106022417092721)
                  ·
                    refine ⟨212941583093329516812819541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 283922110791106022417092721 212941583093329516812819541)
                    ·
                      refine ⟨2495409176874955275150229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 212941583093329516812819541 2495409176874955275150229)
                      ·
                        rfl

theorem cell23_4859792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_4859792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859792 prefixEnd_4859792 := by exact prefixLift 4859792
  have htrace : WordTrace (prefixWord ++ tailWord_4859792) baseStart_4859792 baseEnd_4859792 := by
    simpa [prefixWord, tailWord_4859792, baseEnd_4859792] using wordTrace_append hprefix tailTrace_4859792
  have hstable : (prefixWord ++ tailWord_4859792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859792).length < 2 ^ (prefixWord ++ tailWord_4859792).sum := by decide
  have hdescent : baseEnd_4859792 < baseStart_4859792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859807 : List Nat := [1, 1, 2, 5, 4, 1, 2, 1, 1, 2, 3]
def baseStart_4859807 : Nat := 118140960795 + 4859807 * 2 ^ 59
def prefixEnd_4859807 : Nat := 4983230072969 + 3 ^ 40 * 4859807 * 2
def baseEnd_4859807 : Nat := 2495416879084772716462661

theorem tailTrace_4859807 : CollatzResearch.WordTrace tailWord_4859807 prefixEnd_4859807 2495416879084772716462661 := by
  unfold tailWord_4859807
  simp only [CollatzResearch.WordTrace]
  refine ⟨177251723104756702801913675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118167815403171135201275783 177251723104756702801913675)
  ·
    refine ⟨265877584657135054202870513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177251723104756702801913675 265877584657135054202870513)
    ·
      refine ⟨199408188492851290652152885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265877584657135054202870513 199408188492851290652152885)
      ·
        refine ⟨18694517671204808498639333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 199408188492851290652152885 18694517671204808498639333)
        ·
          refine ⟨3505222063350901593494875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18694517671204808498639333 3505222063350901593494875)
          ·
            refine ⟨5257833095026352390242313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3505222063350901593494875 5257833095026352390242313)
            ·
              refine ⟨3943374821269764292681735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5257833095026352390242313 3943374821269764292681735)
              ·
                refine ⟨5915062231904646439022603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943374821269764292681735 5915062231904646439022603)
                ·
                  refine ⟨8872593347856969658533905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5915062231904646439022603 8872593347856969658533905)
                  ·
                    refine ⟨6654445010892727243900429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8872593347856969658533905 6654445010892727243900429)
                    ·
                      refine ⟨2495416879084772716462661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6654445010892727243900429 2495416879084772716462661)
                      ·
                        rfl

theorem cell23_4859807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_4859807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859807 prefixEnd_4859807 := by exact prefixLift 4859807
  have htrace : WordTrace (prefixWord ++ tailWord_4859807) baseStart_4859807 baseEnd_4859807 := by
    simpa [prefixWord, tailWord_4859807, baseEnd_4859807] using wordTrace_append hprefix tailTrace_4859807
  have hstable : (prefixWord ++ tailWord_4859807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859807).length < 2 ^ (prefixWord ++ tailWord_4859807).sum := by decide
  have hdescent : baseEnd_4859807 < baseStart_4859807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859826 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2]
def baseStart_4859826 : Nat := 118140960795 + 4859826 * 2 ^ 59
def prefixEnd_4859826 : Nat := 4983230072969 + 3 ^ 40 * 4859826 * 2
def baseEnd_4859826 : Nat := 2495426635217208142125073

theorem tailTrace_4859826 : CollatzResearch.WordTrace tailWord_4859826 prefixEnd_4859826 2495426635217208142125073 := by
  unfold tailWord_4859826
  simp only [CollatzResearch.WordTrace]
  refine ⟨44313104022921967261713833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118168277394458579364570221 44313104022921967261713833)
  ·
    refine ⟨33234828017191475446285375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44313104022921967261713833 33234828017191475446285375)
    ·
      refine ⟨49852242025787213169428063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33234828017191475446285375 49852242025787213169428063)
      ·
        refine ⟨74778363038680819754142095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49852242025787213169428063 74778363038680819754142095)
        ·
          refine ⟨112167544558021229631213143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74778363038680819754142095 112167544558021229631213143)
          ·
            refine ⟨168251316837031844446819715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112167544558021229631213143 168251316837031844446819715)
            ·
              refine ⟨252376975255547766670229573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168251316837031844446819715 252376975255547766670229573)
              ·
                refine ⟨47320682860415206250668045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252376975255547766670229573 47320682860415206250668045)
                ·
                  refine ⟨17745256072655702344000517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47320682860415206250668045 17745256072655702344000517)
                  ·
                    refine ⟨3327235513622944189500097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17745256072655702344000517 3327235513622944189500097)
                    ·
                      refine ⟨2495426635217208142125073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327235513622944189500097 2495426635217208142125073)
                      ·
                        rfl

theorem cell23_4859826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_4859826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859826 prefixEnd_4859826 := by exact prefixLift 4859826
  have htrace : WordTrace (prefixWord ++ tailWord_4859826) baseStart_4859826 baseEnd_4859826 := by
    simpa [prefixWord, tailWord_4859826, baseEnd_4859826] using wordTrace_append hprefix tailTrace_4859826
  have hstable : (prefixWord ++ tailWord_4859826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859826).length < 2 ^ (prefixWord ++ tailWord_4859826).sum := by decide
  have hdescent : baseEnd_4859826 < baseStart_4859826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859839 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 4]
def baseStart_4859839 : Nat := 118140960795 + 4859839 * 2 ^ 59
def prefixEnd_4859839 : Nat := 4983230072969 + 3 ^ 40 * 4859839 * 2
def baseEnd_4859839 : Nat := 2495433310465716591262513

theorem tailTrace_4859839 : CollatzResearch.WordTrace tailWord_4859839 prefixEnd_4859839 2495433310465716591262513 := by
  unfold tailWord_4859839
  simp only [CollatzResearch.WordTrace]
  refine ⟨177252890240640772267078571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118168593493760514844719047 177252890240640772267078571)
  ·
    refine ⟨265879335360961158400617857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177252890240640772267078571 265879335360961158400617857)
    ·
      refine ⟨199409501520720868800463393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265879335360961158400617857 199409501520720868800463393)
      ·
        refine ⟨149557126140540651600347545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199409501520720868800463393 149557126140540651600347545)
        ·
          refine ⟨112167844605405488700260659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149557126140540651600347545 112167844605405488700260659)
          ·
            refine ⟨168251766908108233050390989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112167844605405488700260659 168251766908108233050390989)
            ·
              refine ⟨63094412590540587393896621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168251766908108233050390989 63094412590540587393896621)
              ·
                refine ⟨23660404721452720272711233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63094412590540587393896621 23660404721452720272711233)
                ·
                  refine ⟨17745303541089540204533425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23660404721452720272711233 17745303541089540204533425)
                  ·
                    refine ⟨13308977655817155153400069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17745303541089540204533425 13308977655817155153400069)
                    ·
                      refine ⟨2495433310465716591262513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13308977655817155153400069 2495433310465716591262513)
                      ·
                        rfl

theorem cell23_4859839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_4859839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859839 prefixEnd_4859839 := by exact prefixLift 4859839
  have htrace : WordTrace (prefixWord ++ tailWord_4859839) baseStart_4859839 baseEnd_4859839 := by
    simpa [prefixWord, tailWord_4859839, baseEnd_4859839] using wordTrace_append hprefix tailTrace_4859839
  have hstable : (prefixWord ++ tailWord_4859839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859839).length < 2 ^ (prefixWord ++ tailWord_4859839).sum := by decide
  have hdescent : baseEnd_4859839 < baseStart_4859839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859899 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 4]
def baseStart_4859899 : Nat := 118140960795 + 4859899 * 2 ^ 59
def prefixEnd_4859899 : Nat := 4983230072969 + 3 ^ 40 * 4859899 * 2
def baseEnd_4859899 : Nat := 2495464119304986356512237

theorem tailTrace_4859899 : CollatzResearch.WordTrace tailWord_4859899 prefixEnd_4859899 2495464119304986356512237 := by
  unfold tailWord_4859899
  simp only [CollatzResearch.WordTrace]
  refine ⟨177255078620423402514262751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118170052413615601676175167 177255078620423402514262751)
  ·
    refine ⟨265882617930635103771394127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177255078620423402514262751 265882617930635103771394127)
    ·
      refine ⟨398823926895952655657091191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265882617930635103771394127 398823926895952655657091191)
      ·
        refine ⟨598235890343928983485636787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398823926895952655657091191 598235890343928983485636787)
        ·
          refine ⟨897353835515893475228455181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598235890343928983485636787 897353835515893475228455181)
          ·
            refine ⟨336507688318460053210670693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 897353835515893475228455181 336507688318460053210670693)
            ·
              refine ⟨63095191559711259977000755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 336507688318460053210670693 63095191559711259977000755)
              ·
                refine ⟨94642787339566889965501133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63095191559711259977000755 94642787339566889965501133)
                ·
                  refine ⟨35491045252337583737062925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94642787339566889965501133 35491045252337583737062925)
                  ·
                    refine ⟨13309141969626593901398597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35491045252337583737062925 13309141969626593901398597)
                    ·
                      refine ⟨2495464119304986356512237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13309141969626593901398597 2495464119304986356512237)
                      ·
                        rfl

theorem cell23_4859899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 4].length) (baseStart_4859899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859899 prefixEnd_4859899 := by exact prefixLift 4859899
  have htrace : WordTrace (prefixWord ++ tailWord_4859899) baseStart_4859899 baseEnd_4859899 := by
    simpa [prefixWord, tailWord_4859899, baseEnd_4859899] using wordTrace_append hprefix tailTrace_4859899
  have hstable : (prefixWord ++ tailWord_4859899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859899).length < 2 ^ (prefixWord ++ tailWord_4859899).sum := by decide
  have hdescent : baseEnd_4859899 < baseStart_4859899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859929 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 6]
def baseStart_4859929 : Nat := 118140960795 + 4859929 * 2 ^ 59
def prefixEnd_4859929 : Nat := 4983230072969 + 3 ^ 40 * 4859929 * 2
def baseEnd_4859929 : Nat := 2495479523724621239137099

theorem tailTrace_4859929 : CollatzResearch.WordTrace tailWord_4859929 prefixEnd_4859929 2495479523724621239137099 := by
  unfold tailWord_4859929
  simp only [CollatzResearch.WordTrace]
  refine ⟨177256172810314717637854841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118170781873543145091903227 177256172810314717637854841)
  ·
    refine ⟨132942129607736038228391131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177256172810314717637854841 132942129607736038228391131)
    ·
      refine ⟨199413194411604057342586697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132942129607736038228391131 199413194411604057342586697)
      ·
        refine ⟨149559895808703043006940023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199413194411604057342586697 149559895808703043006940023)
        ·
          refine ⟨224339843713054564510410035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149559895808703043006940023 224339843713054564510410035)
          ·
            refine ⟨336509765569581846765615053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224339843713054564510410035 336509765569581846765615053)
            ·
              refine ⟨126191162088593192537105645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 336509765569581846765615053 126191162088593192537105645)
              ·
                refine ⟨47321685783222447201414617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126191162088593192537105645 47321685783222447201414617)
                ·
                  refine ⟨35491264337416835401060963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47321685783222447201414617 35491264337416835401060963)
                  ·
                    refine ⟨53236896506125253101591445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35491264337416835401060963 53236896506125253101591445)
                    ·
                      refine ⟨2495479523724621239137099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53236896506125253101591445 2495479523724621239137099)
                      ·
                        rfl

theorem cell23_4859929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_4859929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859929 prefixEnd_4859929 := by exact prefixLift 4859929
  have htrace : WordTrace (prefixWord ++ tailWord_4859929) baseStart_4859929 baseEnd_4859929 := by
    simpa [prefixWord, tailWord_4859929, baseEnd_4859929] using wordTrace_append hprefix tailTrace_4859929
  have hstable : (prefixWord ++ tailWord_4859929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859929).length < 2 ^ (prefixWord ++ tailWord_4859929).sum := by decide
  have hdescent : baseEnd_4859929 < baseStart_4859929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859933 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_4859933 : Nat := 118140960795 + 4859933 * 2 ^ 59
def prefixEnd_4859933 : Nat := 4983230072969 + 3 ^ 40 * 4859933 * 2
def baseEnd_4859933 : Nat := 2495481577647239223487081

theorem tailTrace_4859933 : CollatzResearch.WordTrace tailWord_4859933 prefixEnd_4859933 2495481577647239223487081 := by
  unfold tailWord_4859933
  simp only [CollatzResearch.WordTrace]
  refine ⟨177256318702300226321000453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118170879134866817547333635 177256318702300226321000453)
  ·
    refine ⟨33235559756681292435187585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177256318702300226321000453 33235559756681292435187585)
    ·
      refine ⟨24926669817510969326390689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33235559756681292435187585 24926669817510969326390689)
      ·
        refine ⟨18695002363133226994793017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24926669817510969326390689 18695002363133226994793017)
        ·
          refine ⟨14021251772349920246094763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18695002363133226994793017 14021251772349920246094763)
          ·
            refine ⟨21031877658524880369142145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14021251772349920246094763 21031877658524880369142145)
            ·
              refine ⟨15773908243893660276856609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21031877658524880369142145 15773908243893660276856609)
              ·
                refine ⟨11830431182920245207642457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15773908243893660276856609 11830431182920245207642457)
                ·
                  refine ⟨8872823387190183905731843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11830431182920245207642457 8872823387190183905731843)
                  ·
                    refine ⟨13309235080785275858597765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8872823387190183905731843 13309235080785275858597765)
                    ·
                      refine ⟨2495481577647239223487081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13309235080785275858597765 2495481577647239223487081)
                      ·
                        rfl

theorem cell23_4859933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_4859933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859933 prefixEnd_4859933 := by exact prefixLift 4859933
  have htrace : WordTrace (prefixWord ++ tailWord_4859933) baseStart_4859933 baseEnd_4859933 := by
    simpa [prefixWord, tailWord_4859933, baseEnd_4859933] using wordTrace_append hprefix tailTrace_4859933
  have hstable : (prefixWord ++ tailWord_4859933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859933).length < 2 ^ (prefixWord ++ tailWord_4859933).sum := by decide
  have hdescent : baseEnd_4859933 < baseStart_4859933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859950 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_4859950 : Nat := 118140960795 + 4859950 * 2 ^ 59
def prefixEnd_4859950 : Nat := 4983230072969 + 3 ^ 40 * 4859950 * 2
def baseEnd_4859950 : Nat := 2495490306818365656974503

theorem tailTrace_4859950 : CollatzResearch.WordTrace tailWord_4859950 prefixEnd_4859950 2495490306818365656974503 := by
  unfold tailWord_4859950
  simp only [CollatzResearch.WordTrace]
  refine ⟨22157117342904829778046163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118171292495492425482912869 22157117342904829778046163)
  ·
    refine ⟨33235676014357244667069245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22157117342904829778046163 33235676014357244667069245)
    ·
      refine ⟨12463378505383966750150967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33235676014357244667069245 12463378505383966750150967)
      ·
        refine ⟨18695067758075950125226451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12463378505383966750150967 18695067758075950125226451)
        ·
          refine ⟨28042601637113925187839677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18695067758075950125226451 28042601637113925187839677)
          ·
            refine ⟨10515975613917721945439879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28042601637113925187839677 10515975613917721945439879)
            ·
              refine ⟨15773963420876582918159819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10515975613917721945439879 15773963420876582918159819)
              ·
                refine ⟨23660945131314874377239729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15773963420876582918159819 23660945131314874377239729)
                ·
                  refine ⟨17745708848486155782929797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23660945131314874377239729 17745708848486155782929797)
                  ·
                    refine ⟨3327320409091154209299337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17745708848486155782929797 3327320409091154209299337)
                    ·
                      refine ⟨2495490306818365656974503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327320409091154209299337 2495490306818365656974503)
                      ·
                        rfl

theorem cell23_4859950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_4859950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859950 prefixEnd_4859950 := by exact prefixLift 4859950
  have htrace : WordTrace (prefixWord ++ tailWord_4859950) baseStart_4859950 baseEnd_4859950 := by
    simpa [prefixWord, tailWord_4859950, baseEnd_4859950] using wordTrace_append hprefix tailTrace_4859950
  have hstable : (prefixWord ++ tailWord_4859950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859950).length < 2 ^ (prefixWord ++ tailWord_4859950).sum := by decide
  have hdescent : baseEnd_4859950 < baseStart_4859950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859979 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 7]
def baseStart_4859979 : Nat := 118140960795 + 4859979 * 2 ^ 59
def prefixEnd_4859979 : Nat := 4983230072969 + 3 ^ 40 * 4859979 * 2
def baseEnd_4859979 : Nat := 2495505197757346043511869

theorem tailTrace_4859979 : CollatzResearch.WordTrace tailWord_4859979 prefixEnd_4859979 2495505197757346043511869 := by
  unfold tailWord_4859979
  simp only [CollatzResearch.WordTrace]
  refine ⟨177257996460133576177174991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118171997640089050784783327 177257996460133576177174991)
  ·
    refine ⟨265886994690200364265762487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177257996460133576177174991 265886994690200364265762487)
    ·
      refine ⟨398830492035300546398643731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265886994690200364265762487 398830492035300546398643731)
      ·
        refine ⟨598245738052950819597965597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398830492035300546398643731 598245738052950819597965597)
        ·
          refine ⟨224342151769856557349237099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 598245738052950819597965597 224342151769856557349237099)
          ·
            refine ⟨336513227654784836023855649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224342151769856557349237099 336513227654784836023855649)
            ·
              refine ⟨252384920741088627017891737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336513227654784836023855649 252384920741088627017891737)
              ·
                refine ⟨189288690555816470263418803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252384920741088627017891737 189288690555816470263418803)
                ·
                  refine ⟨283933035833724705395128205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189288690555816470263418803 283933035833724705395128205)
                  ·
                    refine ⟨106474888437646764523173077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 283933035833724705395128205 106474888437646764523173077)
                    ·
                      refine ⟨2495505197757346043511869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106474888437646764523173077 2495505197757346043511869)
                      ·
                        rfl

theorem cell23_4859979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_4859979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859979 prefixEnd_4859979 := by exact prefixLift 4859979
  have htrace : WordTrace (prefixWord ++ tailWord_4859979) baseStart_4859979 baseEnd_4859979 := by
    simpa [prefixWord, tailWord_4859979, baseEnd_4859979] using wordTrace_append hprefix tailTrace_4859979
  have hstable : (prefixWord ++ tailWord_4859979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859979).length < 2 ^ (prefixWord ++ tailWord_4859979).sum := by decide
  have hdescent : baseEnd_4859979 < baseStart_4859979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859990 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_4859990 : Nat := 118140960795 + 4859990 * 2 ^ 59
def prefixEnd_4859990 : Nat := 4983230072969 + 3 ^ 40 * 4859990 * 2
def baseEnd_4859990 : Nat := 277278982893838388941591

theorem tailTrace_4859990 : CollatzResearch.WordTrace tailWord_4859990 prefixEnd_4859990 277278982893838388941591 := by
  unfold tailWord_4859990
  simp only [CollatzResearch.WordTrace]
  refine ⟨11078649853943357815989089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118172265108729150037216949 11078649853943357815989089)
  ·
    refine ⟨8308987390457518361991817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11078649853943357815989089 8308987390457518361991817)
    ·
      refine ⟨6231740542843138771493863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8308987390457518361991817 6231740542843138771493863)
      ·
        refine ⟨9347610814264708157240795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6231740542843138771493863 9347610814264708157240795)
        ·
          refine ⟨14021416221397062235861193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9347610814264708157240795 14021416221397062235861193)
          ·
            refine ⟨10516062166047796676895895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14021416221397062235861193 10516062166047796676895895)
            ·
              refine ⟨15774093249071695015343843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10516062166047796676895895 15774093249071695015343843)
              ·
                refine ⟨23661139873607542523015765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15774093249071695015343843 23661139873607542523015765)
                ·
                  refine ⟨277278982893838388941591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23661139873607542523015765 277278982893838388941591)
                  ·
                    rfl

theorem cell23_4859990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_4859990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859990 prefixEnd_4859990 := by exact prefixLift 4859990
  have htrace : WordTrace (prefixWord ++ tailWord_4859990) baseStart_4859990 baseEnd_4859990 := by
    simpa [prefixWord, tailWord_4859990, baseEnd_4859990] using wordTrace_append hprefix tailTrace_4859990
  have hstable : (prefixWord ++ tailWord_4859990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859990).length < 2 ^ (prefixWord ++ tailWord_4859990).sum := by decide
  have hdescent : baseEnd_4859990 < baseStart_4859990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4859993 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 4, 3, 2]
def baseStart_4859993 : Nat := 118140960795 + 4859993 * 2 ^ 59
def prefixEnd_4859993 : Nat := 4983230072969 + 3 ^ 40 * 4859993 * 2
def baseEnd_4859993 : Nat := 2495512386486508988736805

theorem tailTrace_4859993 : CollatzResearch.WordTrace tailWord_4859993 prefixEnd_4859993 2495512386486508988736805 := by
  unfold tailWord_4859993
  simp only [CollatzResearch.WordTrace]
  refine ⟨177258507082082856568184633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118172338054721904378789755 177258507082082856568184633)
  ·
    refine ⟨132943880311562142426138475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177258507082082856568184633 132943880311562142426138475)
    ·
      refine ⟨199415820467343213639207713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132943880311562142426138475 199415820467343213639207713)
      ·
        refine ⟨149561865350507410229405785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199415820467343213639207713 149561865350507410229405785)
        ·
          refine ⟨112171399012880557672054339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149561865350507410229405785 112171399012880557672054339)
          ·
            refine ⟨168257098519320836508081509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112171399012880557672054339 168257098519320836508081509)
            ·
              refine ⟨31548205972372656845265283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168257098519320836508081509 31548205972372656845265283)
              ·
                refine ⟨47322308958558985267897925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31548205972372656845265283 47322308958558985267897925)
                ·
                  refine ⟨8872932929729809737730861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47322308958558985267897925 8872932929729809737730861)
                  ·
                    refine ⟨3327349848648678651649073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8872932929729809737730861 3327349848648678651649073)
                    ·
                      refine ⟨2495512386486508988736805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327349848648678651649073 2495512386486508988736805)
                      ·
                        rfl

theorem cell23_4859993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 3, 2].length) (baseStart_4859993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4859993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4859993 prefixEnd_4859993 := by exact prefixLift 4859993
  have htrace : WordTrace (prefixWord ++ tailWord_4859993) baseStart_4859993 baseEnd_4859993 := by
    simpa [prefixWord, tailWord_4859993, baseEnd_4859993] using wordTrace_append hprefix tailTrace_4859993
  have hstable : (prefixWord ++ tailWord_4859993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4859993).length < 2 ^ (prefixWord ++ tailWord_4859993).sum := by decide
  have hdescent : baseEnd_4859993 < baseStart_4859993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4859993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860000 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 3, 1, 3]
def baseStart_4860000 : Nat := 118140960795 + 4860000 * 2 ^ 59
def prefixEnd_4860000 : Nat := 4983230072969 + 3 ^ 40 * 4860000 * 2
def baseEnd_4860000 : Nat := 2495515980851090461349273

theorem tailTrace_4860000 : CollatzResearch.WordTrace tailWord_4860000 prefixEnd_4860000 2495515980851090461349273 := by
  unfold tailWord_4860000
  simp only [CollatzResearch.WordTrace]
  refine ⟨88629381196528748381844727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118172508262038331175792969 88629381196528748381844727)
  ·
    refine ⟨132944071794793122572767091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88629381196528748381844727 132944071794793122572767091)
    ·
      refine ⟨199416107692189683859150637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132944071794793122572767091 199416107692189683859150637)
      ·
        refine ⟨74781040384571131447181489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199416107692189683859150637 74781040384571131447181489)
        ·
          refine ⟨56085780288428348585386117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74781040384571131447181489 56085780288428348585386117)
          ·
            refine ⟨10516083804080315359759897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56085780288428348585386117 10516083804080315359759897)
            ·
              refine ⟨7887062853060236519819923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10516083804080315359759897 7887062853060236519819923)
              ·
                refine ⟨11830594279590354779729885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7887062853060236519819923 11830594279590354779729885)
                ·
                  refine ⟨4436472854846383042398707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11830594279590354779729885 4436472854846383042398707)
                  ·
                    refine ⟨6654709282269574563598061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4436472854846383042398707 6654709282269574563598061)
                    ·
                      refine ⟨2495515980851090461349273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6654709282269574563598061 2495515980851090461349273)
                      ·
                        rfl

theorem cell23_4860000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_4860000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860000 prefixEnd_4860000 := by exact prefixLift 4860000
  have htrace : WordTrace (prefixWord ++ tailWord_4860000) baseStart_4860000 baseEnd_4860000 := by
    simpa [prefixWord, tailWord_4860000, baseEnd_4860000] using wordTrace_append hprefix tailTrace_4860000
  have hstable : (prefixWord ++ tailWord_4860000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860000).length < 2 ^ (prefixWord ++ tailWord_4860000).sum := by decide
  have hdescent : baseEnd_4860000 < baseStart_4860000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860023 : List Nat := [1, 1, 3, 1, 1, 5, 1, 4, 1, 1, 4]
def baseStart_4860023 : Nat := 118140960795 + 4860023 * 2 ^ 59
def prefixEnd_4860023 : Nat := 4983230072969 + 3 ^ 40 * 4860023 * 2
def baseEnd_4860023 : Nat := 2495527790906143871361667

theorem tailTrace_4860023 : CollatzResearch.WordTrace tailWord_4860023 prefixEnd_4860023 2495527790906143871361667 := by
  unfold tailWord_4860023
  simp only [CollatzResearch.WordTrace]
  refine ⟨177259601271974171691776723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118173067514649447794517815 177259601271974171691776723)
  ·
    refine ⟨265889401907961257537665085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177259601271974171691776723 265889401907961257537665085)
    ·
      refine ⟨99708525715485471576624407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265889401907961257537665085 99708525715485471576624407)
      ·
        refine ⟨149562788573228207364936611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99708525715485471576624407 149562788573228207364936611)
        ·
          refine ⟨224344182859842311047404917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149562788573228207364936611 224344182859842311047404917)
          ·
            refine ⟨21032267143110216660694211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 224344182859842311047404917 21032267143110216660694211)
            ·
              refine ⟨31548400714665324991041317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21032267143110216660694211 31548400714665324991041317)
              ·
                refine ⟨5915325133999748435820247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31548400714665324991041317 5915325133999748435820247)
                ·
                  refine ⟨8872987700999622653730371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5915325133999748435820247 8872987700999622653730371)
                  ·
                    refine ⟨13309481551499433980595557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8872987700999622653730371 13309481551499433980595557)
                    ·
                      refine ⟨2495527790906143871361667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13309481551499433980595557 2495527790906143871361667)
                      ·
                        rfl

theorem cell23_4860023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_4860023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860023 prefixEnd_4860023 := by exact prefixLift 4860023
  have htrace : WordTrace (prefixWord ++ tailWord_4860023) baseStart_4860023 baseEnd_4860023 := by
    simpa [prefixWord, tailWord_4860023, baseEnd_4860023] using wordTrace_append hprefix tailTrace_4860023
  have hstable : (prefixWord ++ tailWord_4860023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860023).length < 2 ^ (prefixWord ++ tailWord_4860023).sum := by decide
  have hdescent : baseEnd_4860023 < baseStart_4860023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860026 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3]
def baseStart_4860026 : Nat := 118140960795 + 4860026 * 2 ^ 59
def prefixEnd_4860026 : Nat := 4983230072969 + 3 ^ 40 * 4860026 * 2
def baseEnd_4860026 : Nat := 2495529331348107359624153

theorem tailTrace_4860026 : CollatzResearch.WordTrace tailWord_4860026 prefixEnd_4860026 2495529331348107359624153 := by
  unfold tailWord_4860026
  simp only [CollatzResearch.WordTrace]
  refine ⟨44314927672740825801033983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118173140460642202136090621 44314927672740825801033983)
  ·
    refine ⟨66472391509111238701550975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44314927672740825801033983 66472391509111238701550975)
    ·
      refine ⟨99708587263666858052326463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66472391509111238701550975 99708587263666858052326463)
      ·
        refine ⟨149562880895500287078489695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99708587263666858052326463 149562880895500287078489695)
        ·
          refine ⟨224344321343250430617734543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149562880895500287078489695 224344321343250430617734543)
          ·
            refine ⟨336516482014875645926601815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224344321343250430617734543 336516482014875645926601815)
            ·
              refine ⟨504774723022313468889902723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336516482014875645926601815 504774723022313468889902723)
              ·
                refine ⟨757162084533470203334854085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504774723022313468889902723 757162084533470203334854085)
                ·
                  refine ⟨141967890850025663125285141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 757162084533470203334854085 141967890850025663125285141)
                  ·
                    refine ⟨6654744883594952958997741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 141967890850025663125285141 6654744883594952958997741)
                    ·
                      refine ⟨2495529331348107359624153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6654744883594952958997741 2495529331348107359624153)
                      ·
                        rfl

theorem cell23_4860026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_4860026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860026 prefixEnd_4860026 := by exact prefixLift 4860026
  have htrace : WordTrace (prefixWord ++ tailWord_4860026) baseStart_4860026 baseEnd_4860026 := by
    simpa [prefixWord, tailWord_4860026, baseEnd_4860026] using wordTrace_append hprefix tailTrace_4860026
  have hstable : (prefixWord ++ tailWord_4860026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860026).length < 2 ^ (prefixWord ++ tailWord_4860026).sum := by decide
  have hdescent : baseEnd_4860026 < baseStart_4860026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860040 : List Nat := [2, 1, 3, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4860040 : Nat := 118140960795 + 4860040 * 2 ^ 59
def prefixEnd_4860040 : Nat := 4983230072969 + 3 ^ 40 * 4860040 * 2
def baseEnd_4860040 : Nat := 2495536520077270304849089

theorem tailTrace_4860040 : CollatzResearch.WordTrace tailWord_4860040 prefixEnd_4860040 2495536520077270304849089 := by
  unfold tailWord_4860040
  simp only [CollatzResearch.WordTrace]
  refine ⟨88630110656456291797572787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118173480875275055730097049 88630110656456291797572787)
  ·
    refine ⟨132945165984684437696359181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88630110656456291797572787 132945165984684437696359181)
    ·
      refine ⟨49854437244256664136134693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132945165984684437696359181 49854437244256664136134693)
      ·
        refine ⟨9347706983298124525525255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49854437244256664136134693 9347706983298124525525255)
        ·
          refine ⟨14021560474947186788287883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9347706983298124525525255 14021560474947186788287883)
          ·
            refine ⟨21032340712420780182431825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14021560474947186788287883 21032340712420780182431825)
            ·
              refine ⟨15774255534315585136823869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21032340712420780182431825 15774255534315585136823869)
              ·
                refine ⟨5915345825368344426308951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15774255534315585136823869 5915345825368344426308951)
                ·
                  refine ⟨8873018738052516639463427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5915345825368344426308951 8873018738052516639463427)
                  ·
                    refine ⟨13309528107078774959195141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8873018738052516639463427 13309528107078774959195141)
                    ·
                      refine ⟨2495536520077270304849089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13309528107078774959195141 2495536520077270304849089)
                      ·
                        rfl

theorem cell23_4860040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4860040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860040 prefixEnd_4860040 := by exact prefixLift 4860040
  have htrace : WordTrace (prefixWord ++ tailWord_4860040) baseStart_4860040 baseEnd_4860040 := by
    simpa [prefixWord, tailWord_4860040, baseEnd_4860040] using wordTrace_append hprefix tailTrace_4860040
  have hstable : (prefixWord ++ tailWord_4860040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860040).length < 2 ^ (prefixWord ++ tailWord_4860040).sum := by decide
  have hdescent : baseEnd_4860040 < baseStart_4860040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860050 : List Nat := [3, 2, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_4860050 : Nat := 118140960795 + 4860050 * 2 ^ 59
def prefixEnd_4860050 : Nat := 4983230072969 + 3 ^ 40 * 4860050 * 2
def baseEnd_4860050 : Nat := 831847218294605088574681

theorem tailTrace_4860050 : CollatzResearch.WordTrace tailWord_4860050 prefixEnd_4860050 831847218294605088574681 := by
  unfold tailWord_4860050
  simp only [CollatzResearch.WordTrace]
  refine ⟨44315146510719088825752401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118173724028584236868673069 44315146510719088825752401)
  ·
    refine ⟨33236359883039316619314301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44315146510719088825752401 33236359883039316619314301)
    ·
      refine ⟨12463634956139743732242863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33236359883039316619314301 12463634956139743732242863)
      ·
        refine ⟨18695452434209615598364295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12463634956139743732242863 18695452434209615598364295)
        ·
          refine ⟨28043178651314423397546443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18695452434209615598364295 28043178651314423397546443)
          ·
            refine ⟨42064767976971635096319665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28043178651314423397546443 42064767976971635096319665)
            ·
              refine ⟨31548575982728726322239749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42064767976971635096319665 31548575982728726322239749)
              ·
                refine ⟨5915357996761636185419953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31548575982728726322239749 5915357996761636185419953)
                ·
                  refine ⟨4436518497571227139064965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5915357996761636185419953 4436518497571227139064965)
                  ·
                    refine ⟨831847218294605088574681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4436518497571227139064965 831847218294605088574681)
                    ·
                      rfl

theorem cell23_4860050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_4860050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860050 prefixEnd_4860050 := by exact prefixLift 4860050
  have htrace : WordTrace (prefixWord ++ tailWord_4860050) baseStart_4860050 baseEnd_4860050 := by
    simpa [prefixWord, tailWord_4860050, baseEnd_4860050] using wordTrace_append hprefix tailTrace_4860050
  have hstable : (prefixWord ++ tailWord_4860050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860050).length < 2 ^ (prefixWord ++ tailWord_4860050).sum := by decide
  have hdescent : baseEnd_4860050 < baseStart_4860050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860057 : List Nat := [1, 2, 1, 2, 1, 2, 1, 8, 1, 2, 2]
def baseStart_4860057 : Nat := 118140960795 + 4860057 * 2 ^ 59
def prefixEnd_4860057 : Nat := 4983230072969 + 3 ^ 40 * 4860057 * 2
def baseEnd_4860057 : Nat := 2495545249248396738336511

theorem tailTrace_4860057 : CollatzResearch.WordTrace tailWord_4860057 prefixEnd_4860057 2495545249248396738336511 := by
  unfold tailWord_4860057
  simp only [CollatzResearch.WordTrace]
  refine ⟨177260841353850995498514425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118173894235900663665676283 177260841353850995498514425)
  ·
    refine ⟨132945631015388246623885819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177260841353850995498514425 132945631015388246623885819)
    ·
      refine ⟨199418446523082369935828729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132945631015388246623885819 199418446523082369935828729)
      ·
        refine ⟨149563834892311777451871547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199418446523082369935828729 149563834892311777451871547)
        ·
          refine ⟨224345752338467666177807321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149563834892311777451871547 224345752338467666177807321)
          ·
            refine ⟨168259314253850749633355491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224345752338467666177807321 168259314253850749633355491)
            ·
              refine ⟨252388971380776124450033237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168259314253850749633355491 252388971380776124450033237)
              ·
                refine ⟨2957683258368470208398827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 252388971380776124450033237 2957683258368470208398827)
                ·
                  refine ⟨4436524887552705312598241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957683258368470208398827 4436524887552705312598241)
                  ·
                    refine ⟨3327393665664528984448681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4436524887552705312598241 3327393665664528984448681)
                    ·
                      refine ⟨2495545249248396738336511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327393665664528984448681 2495545249248396738336511)
                      ·
                        rfl

theorem cell23_4860057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 1, 2, 2].length) (baseStart_4860057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860057 prefixEnd_4860057 := by exact prefixLift 4860057
  have htrace : WordTrace (prefixWord ++ tailWord_4860057) baseStart_4860057 baseEnd_4860057 := by
    simpa [prefixWord, tailWord_4860057, baseEnd_4860057] using wordTrace_append hprefix tailTrace_4860057
  have hstable : (prefixWord ++ tailWord_4860057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860057).length < 2 ^ (prefixWord ++ tailWord_4860057).sum := by decide
  have hdescent : baseEnd_4860057 < baseStart_4860057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860063 : List Nat := [1, 1, 2, 6, 1, 2, 2, 8]
def baseStart_4860063 : Nat := 118140960795 + 4860063 * 2 ^ 59
def prefixEnd_4860063 : Nat := 4983230072969 + 3 ^ 40 * 4860063 * 2
def baseEnd_4860063 : Nat := 92427715930826804254129

theorem tailTrace_4860063 : CollatzResearch.WordTrace tailWord_4860063 prefixEnd_4860063 92427715930826804254129 := by
  unfold tailWord_4860063
  simp only [CollatzResearch.WordTrace]
  refine ⟨177261060191829258523232843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118174040127886172348821895 177261060191829258523232843)
  ·
    refine ⟨265891590287743887784849265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177261060191829258523232843 265891590287743887784849265)
    ·
      refine ⟨199418692715807915838636949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265891590287743887784849265 199418692715807915838636949)
      ·
        refine ⟨9347751221053496054936107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 199418692715807915838636949 9347751221053496054936107)
        ·
          refine ⟨14021626831580244082404161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9347751221053496054936107 14021626831580244082404161)
          ·
            refine ⟨10516220123685183061803121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14021626831580244082404161 10516220123685183061803121)
            ·
              refine ⟨7887165092763887296352341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10516220123685183061803121 7887165092763887296352341)
              ·
                refine ⟨92427715930826804254129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7887165092763887296352341 92427715930826804254129)
                ·
                  rfl

theorem cell23_4860063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 8].length) (baseStart_4860063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860063 prefixEnd_4860063 := by exact prefixLift 4860063
  have htrace : WordTrace (prefixWord ++ tailWord_4860063) baseStart_4860063 baseEnd_4860063 := by
    simpa [prefixWord, tailWord_4860063, baseEnd_4860063] using wordTrace_append hprefix tailTrace_4860063
  have hstable : (prefixWord ++ tailWord_4860063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860063).length < 2 ^ (prefixWord ++ tailWord_4860063).sum := by decide
  have hdescent : baseEnd_4860063 < baseStart_4860063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860074 : List Nat := [3, 1, 5, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_4860074 : Nat := 118140960795 + 4860074 * 2 ^ 59
def prefixEnd_4860074 : Nat := 4983230072969 + 3 ^ 40 * 4860074 * 2
def baseEnd_4860074 : Nat := 2495553978419523171823933

theorem tailTrace_4860074 : CollatzResearch.WordTrace tailWord_4860074 prefixEnd_4860074 2495553978419523171823933 := by
  unfold tailWord_4860074
  simp only [CollatzResearch.WordTrace]
  refine ⟨44315365348697351850470819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118174307596526271601255517 44315365348697351850470819)
  ·
    refine ⟨66473048023046027775706229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44315365348697351850470819 66473048023046027775706229)
    ·
      refine ⟨6231848252160565103972459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66473048023046027775706229 6231848252160565103972459)
      ·
        refine ⟨9347772378240847655958689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6231848252160565103972459 9347772378240847655958689)
        ·
          refine ⟨7010829283680635741969017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9347772378240847655958689 7010829283680635741969017)
          ·
            refine ⟨5258121962760476806476763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7010829283680635741969017 5258121962760476806476763)
            ·
              refine ⟨7887182944140715209715145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5258121962760476806476763 7887182944140715209715145)
              ·
                refine ⟨5915387208105536407286359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7887182944140715209715145 5915387208105536407286359)
                ·
                  refine ⟨8873080812158304610929539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5915387208105536407286359 8873080812158304610929539)
                  ·
                    refine ⟨13309621218237456916394309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8873080812158304610929539 13309621218237456916394309)
                    ·
                      refine ⟨2495553978419523171823933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13309621218237456916394309 2495553978419523171823933)
                      ·
                        rfl

theorem cell23_4860074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_4860074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860074 prefixEnd_4860074 := by exact prefixLift 4860074
  have htrace : WordTrace (prefixWord ++ tailWord_4860074) baseStart_4860074 baseEnd_4860074 := by
    simpa [prefixWord, tailWord_4860074, baseEnd_4860074] using wordTrace_append hprefix tailTrace_4860074
  have hstable : (prefixWord ++ tailWord_4860074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860074).length < 2 ^ (prefixWord ++ tailWord_4860074).sum := by decide
  have hdescent : baseEnd_4860074 < baseStart_4860074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860077 : List Nat := [1, 5, 2, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_4860077 : Nat := 118140960795 + 4860077 * 2 ^ 59
def prefixEnd_4860077 : Nat := 4983230072969 + 3 ^ 40 * 4860077 * 2
def baseEnd_4860077 : Nat := 2495555518861486660086419

theorem tailTrace_4860077 : CollatzResearch.WordTrace tailWord_4860077 prefixEnd_4860077 2495555518861486660086419 := by
  unfold tailWord_4860077
  simp only [CollatzResearch.WordTrace]
  refine ⟨177261570813778538914242485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118174380542519025942828323 177261570813778538914242485)
  ·
    refine ⟨16618272263791738023210233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177261570813778538914242485 16618272263791738023210233)
    ·
      refine ⟨12463704197843803517407675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16618272263791738023210233 12463704197843803517407675)
      ·
        refine ⟨18695556296765705276111513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12463704197843803517407675 18695556296765705276111513)
        ·
          refine ⟨14021667222574278957083635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18695556296765705276111513 14021667222574278957083635)
          ·
            refine ⟨21032500833861418435625453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14021667222574278957083635 21032500833861418435625453)
            ·
              refine ⟨7887187812698031913359545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21032500833861418435625453 7887187812698031913359545)
              ·
                refine ⟨5915390859523523935019659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7887187812698031913359545 5915390859523523935019659)
                ·
                  refine ⟨8873086289285285902529489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5915390859523523935019659 8873086289285285902529489)
                  ·
                    refine ⟨6654814716963964426897117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8873086289285285902529489 6654814716963964426897117)
                    ·
                      refine ⟨2495555518861486660086419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6654814716963964426897117 2495555518861486660086419)
                      ·
                        rfl

theorem cell23_4860077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_4860077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860077 prefixEnd_4860077 := by exact prefixLift 4860077
  have htrace : WordTrace (prefixWord ++ tailWord_4860077) baseStart_4860077 baseEnd_4860077 := by
    simpa [prefixWord, tailWord_4860077, baseEnd_4860077] using wordTrace_append hprefix tailTrace_4860077
  have hstable : (prefixWord ++ tailWord_4860077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860077).length < 2 ^ (prefixWord ++ tailWord_4860077).sum := by decide
  have hdescent : baseEnd_4860077 < baseStart_4860077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860084 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_4860084 : Nat := 118140960795 + 4860084 * 2 ^ 59
def prefixEnd_4860084 : Nat := 4983230072969 + 3 ^ 40 * 4860084 * 2
def baseEnd_4860084 : Nat := 831853037742022710899629

theorem tailTrace_4860084 : CollatzResearch.WordTrace tailWord_4860084 prefixEnd_4860084 831853037742022710899629 := by
  unfold tailWord_4860084
  simp only [CollatzResearch.WordTrace]
  refine ⟨88630913062376589554873653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118174550749835452739831537 88630913062376589554873653)
  ·
    refine ⟨8309148099597805270769405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88630913062376589554873653 8309148099597805270769405)
    ·
      refine ⟨3115930537349176976538527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8309148099597805270769405 3115930537349176976538527)
      ·
        refine ⟨4673895806023765464807791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3115930537349176976538527 4673895806023765464807791)
        ·
          refine ⟨7010843709035648197211687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4673895806023765464807791 7010843709035648197211687)
          ·
            refine ⟨10516265563553472295817531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7010843709035648197211687 10516265563553472295817531)
            ·
              refine ⟨15774398345330208443726297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10516265563553472295817531 15774398345330208443726297)
              ·
                refine ⟨11830798758997656332794723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15774398345330208443726297 11830798758997656332794723)
                ·
                  refine ⟨17746198138496484499192085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11830798758997656332794723 17746198138496484499192085)
                  ·
                    refine ⟨831853037742022710899629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17746198138496484499192085 831853037742022710899629)
                    ·
                      rfl

theorem cell23_4860084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_4860084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860084 prefixEnd_4860084 := by exact prefixLift 4860084
  have htrace : WordTrace (prefixWord ++ tailWord_4860084) baseStart_4860084 baseEnd_4860084 := by
    simpa [prefixWord, tailWord_4860084, baseEnd_4860084] using wordTrace_append hprefix tailTrace_4860084
  have hstable : (prefixWord ++ tailWord_4860084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860084).length < 2 ^ (prefixWord ++ tailWord_4860084).sum := by decide
  have hdescent : baseEnd_4860084 < baseStart_4860084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860094 : List Nat := [4, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_4860094 : Nat := 118140960795 + 4860094 * 2 ^ 59
def prefixEnd_4860094 : Nat := 4983230072969 + 3 ^ 40 * 4860094 * 2
def baseEnd_4860094 : Nat := 2495564248032613093573841

theorem tailTrace_4860094 : CollatzResearch.WordTrace tailWord_4860094 prefixEnd_4860094 2495564248032613093573841 := by
  unfold tailWord_4860094
  simp only [CollatzResearch.WordTrace]
  refine ⟨22157773856839618852201417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118174793903144633878407557 22157773856839618852201417)
  ·
    refine ⟨16618330392629714139151063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22157773856839618852201417 16618330392629714139151063)
    ·
      refine ⟨24927495588944571208726595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16618330392629714139151063 24927495588944571208726595)
      ·
        refine ⟨37391243383416856813089893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24927495588944571208726595 37391243383416856813089893)
        ·
          refine ⟨7010858134390660652454355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37391243383416856813089893 7010858134390660652454355)
          ·
            refine ⟨10516287201585990978681533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7010858134390660652454355 10516287201585990978681533)
            ·
              refine ⟨3943607700594746617005575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10516287201585990978681533 3943607700594746617005575)
              ·
                refine ⟨5915411550892119925508363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943607700594746617005575 5915411550892119925508363)
                ·
                  refine ⟨8873117326338179888262545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5915411550892119925508363 8873117326338179888262545)
                  ·
                    refine ⟨6654837994753634916196909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8873117326338179888262545 6654837994753634916196909)
                    ·
                      refine ⟨2495564248032613093573841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6654837994753634916196909 2495564248032613093573841)
                      ·
                        rfl

theorem cell23_4860094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_4860094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860094 prefixEnd_4860094 := by exact prefixLift 4860094
  have htrace : WordTrace (prefixWord ++ tailWord_4860094) baseStart_4860094 baseEnd_4860094 := by
    simpa [prefixWord, tailWord_4860094, baseEnd_4860094] using wordTrace_append hprefix tailTrace_4860094
  have hstable : (prefixWord ++ tailWord_4860094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860094).length < 2 ^ (prefixWord ++ tailWord_4860094).sum := by decide
  have hdescent : baseEnd_4860094 < baseStart_4860094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860124 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_4860124 : Nat := 118140960795 + 4860124 * 2 ^ 59
def prefixEnd_4860124 : Nat := 4983230072969 + 3 ^ 40 * 4860124 * 2
def baseEnd_4860124 : Nat := 2495579652452247976198703

theorem tailTrace_4860124 : CollatzResearch.WordTrace tailWord_4860124 prefixEnd_4860124 2495579652452247976198703 := by
  unfold tailWord_4860124
  simp only [CollatzResearch.WordTrace]
  refine ⟨88631642522304132970601713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118175523363072177294135617 88631642522304132970601713)
  ·
    refine ⟨66473731891728099727951285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88631642522304132970601713 66473731891728099727951285)
    ·
      refine ⟨6231912364849509349495433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66473731891728099727951285 6231912364849509349495433)
      ·
        refine ⟨4673934273637132012121575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6231912364849509349495433 4673934273637132012121575)
        ·
          refine ⟨7010901410455698018182363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4673934273637132012121575 7010901410455698018182363)
          ·
            refine ⟨10516352115683547027273545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7010901410455698018182363 10516352115683547027273545)
            ·
              refine ⟨7887264086762660270455159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10516352115683547027273545 7887264086762660270455159)
              ·
                refine ⟨11830896130143990405682739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7887264086762660270455159 11830896130143990405682739)
                ·
                  refine ⟨17746344195215985608524109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11830896130143990405682739 17746344195215985608524109)
                  ·
                    refine ⟨6654879073205994603196541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17746344195215985608524109 6654879073205994603196541)
                    ·
                      refine ⟨2495579652452247976198703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6654879073205994603196541 2495579652452247976198703)
                      ·
                        rfl

theorem cell23_4860124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_4860124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860124 prefixEnd_4860124 := by exact prefixLift 4860124
  have htrace : WordTrace (prefixWord ++ tailWord_4860124) baseStart_4860124 baseEnd_4860124 := by
    simpa [prefixWord, tailWord_4860124, baseEnd_4860124] using wordTrace_append hprefix tailTrace_4860124
  have hstable : (prefixWord ++ tailWord_4860124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860124).length < 2 ^ (prefixWord ++ tailWord_4860124).sum := by decide
  have hdescent : baseEnd_4860124 < baseStart_4860124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860163 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 3]
def baseStart_4860163 : Nat := 118140960795 + 4860163 * 2 ^ 59
def prefixEnd_4860163 : Nat := 4983230072969 + 3 ^ 40 * 4860163 * 2
def baseEnd_4860163 : Nat := 2495599678197773323611023

theorem tailTrace_4860163 : CollatzResearch.WordTrace tailWord_4860163 prefixEnd_4860163 2495599678197773323611023 := by
  unfold tailWord_4860163
  simp only [CollatzResearch.WordTrace]
  refine ⟨177264707491466975601873143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118176471660977983734582095 177264707491466975601873143)
  ·
    refine ⟨265897061237200463402809715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177264707491466975601873143 265897061237200463402809715)
    ·
      refine ⟨398845591855800695104214573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265897061237200463402809715 398845591855800695104214573)
      ·
        refine ⟨149567096945925260664080465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 398845591855800695104214573 149567096945925260664080465)
        ·
          refine ⟨112175322709443945498060349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149567096945925260664080465 112175322709443945498060349)
          ·
            refine ⟨42065746016041479561772631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112175322709443945498060349 42065746016041479561772631)
            ·
              refine ⟨63098619024062219342658947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42065746016041479561772631 63098619024062219342658947)
              ·
                refine ⟨94647928536093329013988421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63098619024062219342658947 94647928536093329013988421)
                ·
                  refine ⟨17746486600517499190122829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94647928536093329013988421 17746486600517499190122829)
                  ·
                    refine ⟨6654932475194062196296061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17746486600517499190122829 6654932475194062196296061)
                    ·
                      refine ⟨2495599678197773323611023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6654932475194062196296061 2495599678197773323611023)
                      ·
                        rfl

theorem cell23_4860163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_4860163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860163 prefixEnd_4860163 := by exact prefixLift 4860163
  have htrace : WordTrace (prefixWord ++ tailWord_4860163) baseStart_4860163 baseEnd_4860163 := by
    simpa [prefixWord, tailWord_4860163, baseEnd_4860163] using wordTrace_append hprefix tailTrace_4860163
  have hstable : (prefixWord ++ tailWord_4860163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860163).length < 2 ^ (prefixWord ++ tailWord_4860163).sum := by decide
  have hdescent : baseEnd_4860163 < baseStart_4860163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860164 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_4860164 : Nat := 118140960795 + 4860164 * 2 ^ 59
def prefixEnd_4860164 : Nat := 4983230072969 + 3 ^ 40 * 4860164 * 2
def baseEnd_4860164 : Nat := 2495600191678427819698519

theorem tailTrace_4860164 : CollatzResearch.WordTrace tailWord_4860164 prefixEnd_4860164 2495600191678427819698519 := by
  unfold tailWord_4860164
  simp only [CollatzResearch.WordTrace]
  refine ⟨88632371982231676386329773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118176495976308901848439697 88632371982231676386329773)
  ·
    refine ⟨33237139493336878644873665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88632371982231676386329773 33237139493336878644873665)
    ·
      refine ⟨24927854620002658983655249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33237139493336878644873665 24927854620002658983655249)
      ·
        refine ⟨18695890965001994237741437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24927854620002658983655249 18695890965001994237741437)
        ·
          refine ⟨7010959111875747839153039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18695890965001994237741437 7010959111875747839153039)
          ·
            refine ⟨10516438667813621758729559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7010959111875747839153039 10516438667813621758729559)
            ·
              refine ⟨15774658001720432638094339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10516438667813621758729559 15774658001720432638094339)
              ·
                refine ⟨23661987002580648957141509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15774658001720432638094339 23661987002580648957141509)
                ·
                  refine ⟨4436622562983871679464033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23661987002580648957141509 4436622562983871679464033)
                  ·
                    refine ⟨3327466922237903759598025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4436622562983871679464033 3327466922237903759598025)
                    ·
                      refine ⟨2495600191678427819698519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327466922237903759598025 2495600191678427819698519)
                      ·
                        rfl

theorem cell23_4860164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_4860164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860164 prefixEnd_4860164 := by exact prefixLift 4860164
  have htrace : WordTrace (prefixWord ++ tailWord_4860164) baseStart_4860164 baseEnd_4860164 := by
    simpa [prefixWord, tailWord_4860164, baseEnd_4860164] using wordTrace_append hprefix tailTrace_4860164
  have hstable : (prefixWord ++ tailWord_4860164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860164).length < 2 ^ (prefixWord ++ tailWord_4860164).sum := by decide
  have hdescent : baseEnd_4860164 < baseStart_4860164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860170 : List Nat := [3, 1, 2, 2, 1, 1, 4, 4, 5]
def baseStart_4860170 : Nat := 118140960795 + 4860170 * 2 ^ 59
def prefixEnd_4860170 : Nat := 4983230072969 + 3 ^ 40 * 4860170 * 2
def baseEnd_4860170 : Nat := 277289252506928310691499

theorem tailTrace_4860170 : CollatzResearch.WordTrace tailWord_4860170 prefixEnd_4860170 277289252506928310691499 := by
  unfold tailWord_4860170
  simp only [CollatzResearch.WordTrace]
  refine ⟨44316240700610403949344491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118176641868294410531585309 44316240700610403949344491)
  ·
    refine ⟨66474361050915605924016737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44316240700610403949344491 66474361050915605924016737)
    ·
      refine ⟨49855770788186704443012553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66474361050915605924016737 49855770788186704443012553)
      ·
        refine ⟨37391828091140028332259415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49855770788186704443012553 37391828091140028332259415)
        ·
          refine ⟨56087742136710042498389123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37391828091140028332259415 56087742136710042498389123)
          ·
            refine ⟨84131613205065063747583685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56087742136710042498389123 84131613205065063747583685)
            ·
              refine ⟨15774677475949699452671941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84131613205065063747583685 15774677475949699452671941)
              ·
                refine ⟨2957752026740568647375989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15774677475949699452671941 2957752026740568647375989)
                ·
                  refine ⟨277289252506928310691499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2957752026740568647375989 277289252506928310691499)
                  ·
                    rfl

theorem cell23_4860170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_4860170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860170 prefixEnd_4860170 := by exact prefixLift 4860170
  have htrace : WordTrace (prefixWord ++ tailWord_4860170) baseStart_4860170 baseEnd_4860170 := by
    simpa [prefixWord, tailWord_4860170, baseEnd_4860170] using wordTrace_append hprefix tailTrace_4860170
  have hstable : (prefixWord ++ tailWord_4860170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860170).length < 2 ^ (prefixWord ++ tailWord_4860170).sum := by decide
  have hdescent : baseEnd_4860170 < baseStart_4860170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860183 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 1, 7]
def baseStart_4860183 : Nat := 118140960795 + 4860183 * 2 ^ 59
def prefixEnd_4860183 : Nat := 4983230072969 + 3 ^ 40 * 4860183 * 2
def baseEnd_4860183 : Nat := 831869982603621081786977

theorem tailTrace_4860183 : CollatzResearch.WordTrace tailWord_4860183 prefixEnd_4860183 831869982603621081786977 := by
  unfold tailWord_4860183
  simp only [CollatzResearch.WordTrace]
  refine ⟨177265436951394519017601203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118176957967596346011734135 177265436951394519017601203)
  ·
    refine ⟨265898155427091778526401805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177265436951394519017601203 265898155427091778526401805)
    ·
      refine ⟨99711808285159416947400677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265898155427091778526401805 99711808285159416947400677)
      ·
        refine ⟨18695964053467390677637627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99711808285159416947400677 18695964053467390677637627)
        ·
          refine ⟨28043946080201086016456441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18695964053467390677637627 28043946080201086016456441)
          ·
            refine ⟨21032959560150814512342331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28043946080201086016456441 21032959560150814512342331)
            ·
              refine ⟨31549439340226221768513497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21032959560150814512342331 31549439340226221768513497)
              ·
                refine ⟨23662079505169666326385123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31549439340226221768513497 23662079505169666326385123)
                ·
                  refine ⟨35493119257754499489577685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23662079505169666326385123 35493119257754499489577685)
                  ·
                    refine ⟨831869982603621081786977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35493119257754499489577685 831869982603621081786977)
                    ·
                      rfl

theorem cell23_4860183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_4860183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860183 prefixEnd_4860183 := by exact prefixLift 4860183
  have htrace : WordTrace (prefixWord ++ tailWord_4860183) baseStart_4860183 baseEnd_4860183 := by
    simpa [prefixWord, tailWord_4860183, baseEnd_4860183] using wordTrace_append hprefix tailTrace_4860183
  have hstable : (prefixWord ++ tailWord_4860183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860183).length < 2 ^ (prefixWord ++ tailWord_4860183).sum := by decide
  have hdescent : baseEnd_4860183 < baseStart_4860183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860220 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_4860220 : Nat := 118140960795 + 4860220 * 2 ^ 59
def prefixEnd_4860220 : Nat := 4983230072969 + 3 ^ 40 * 4860220 * 2
def baseEnd_4860220 : Nat := 2495628946595079600598261

theorem tailTrace_4860220 : CollatzResearch.WordTrace tailWord_4860220 prefixEnd_4860220 2495628946595079600598261 := by
  unfold tailWord_4860220
  simp only [CollatzResearch.WordTrace]
  refine ⟨88633393226130237168349057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118177857634840316224465409 88633393226130237168349057)
  ·
    refine ⟨66475044919597677876261793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88633393226130237168349057 66475044919597677876261793)
    ·
      refine ⟨49856283689698258407196345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66475044919597677876261793 49856283689698258407196345)
      ·
        refine ⟨37392212767273693805397259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49856283689698258407196345 37392212767273693805397259)
        ·
          refine ⟨56088319150910540708095889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37392212767273693805397259 56088319150910540708095889)
          ·
            refine ⟨42066239363182905531071917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56088319150910540708095889 42066239363182905531071917)
            ·
              refine ⟨15774839761193589574151969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42066239363182905531071917 15774839761193589574151969)
              ·
                refine ⟨11831129820895192180613977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15774839761193589574151969 11831129820895192180613977)
                ·
                  refine ⟨8873347365671394135460483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11831129820895192180613977 8873347365671394135460483)
                  ·
                    refine ⟨13310021048507091203190725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8873347365671394135460483 13310021048507091203190725)
                    ·
                      refine ⟨2495628946595079600598261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13310021048507091203190725 2495628946595079600598261)
                      ·
                        rfl

theorem cell23_4860220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_4860220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860220 prefixEnd_4860220 := by exact prefixLift 4860220
  have htrace : WordTrace (prefixWord ++ tailWord_4860220) baseStart_4860220 baseEnd_4860220 := by
    simpa [prefixWord, tailWord_4860220, baseEnd_4860220] using wordTrace_append hprefix tailTrace_4860220
  have hstable : (prefixWord ++ tailWord_4860220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860220).length < 2 ^ (prefixWord ++ tailWord_4860220).sum := by decide
  have hdescent : baseEnd_4860220 < baseStart_4860220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860277 : List Nat := [1, 3, 4, 1, 2, 2, 2, 2, 6]
def baseStart_4860277 : Nat := 118140960795 + 4860277 * 2 ^ 59
def prefixEnd_4860277 : Nat := 4983230072969 + 3 ^ 40 * 4860277 * 2
def baseEnd_4860277 : Nat := 277295357221376208620611

theorem tailTrace_4860277 : CollatzResearch.WordTrace tailWord_4860277 prefixEnd_4860277 277295357221376208620611 := by
  unfold tailWord_4860277
  simp only [CollatzResearch.WordTrace]
  refine ⟨177268865413053973071523085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118179243608702648714348723 177268865413053973071523085)
  ·
    refine ⟨66475824529895239901821157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177268865413053973071523085 66475824529895239901821157)
    ·
      refine ⟨12464217099355357481591467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66475824529895239901821157 12464217099355357481591467)
      ·
        refine ⟨18696325649033036222387201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12464217099355357481591467 18696325649033036222387201)
        ·
          refine ⟨14022244236774777166790401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18696325649033036222387201 14022244236774777166790401)
          ·
            refine ⟨10516683177581082875092801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14022244236774777166790401 10516683177581082875092801)
            ·
              refine ⟨7887512383185812156319601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10516683177581082875092801 7887512383185812156319601)
              ·
                refine ⟨5915634287389359117239701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7887512383185812156319601 5915634287389359117239701)
                ·
                  refine ⟨277295357221376208620611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5915634287389359117239701 277295357221376208620611)
                  ·
                    rfl

theorem cell23_4860277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_4860277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860277 prefixEnd_4860277 := by exact prefixLift 4860277
  have htrace : WordTrace (prefixWord ++ tailWord_4860277) baseStart_4860277 baseEnd_4860277 := by
    simpa [prefixWord, tailWord_4860277, baseEnd_4860277] using wordTrace_append hprefix tailTrace_4860277
  have hstable : (prefixWord ++ tailWord_4860277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860277).length < 2 ^ (prefixWord ++ tailWord_4860277).sum := by decide
  have hdescent : baseEnd_4860277 < baseStart_4860277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860314 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2]
def baseStart_4860314 : Nat := 118140960795 + 4860314 * 2 ^ 59
def prefixEnd_4860314 : Nat := 4983230072969 + 3 ^ 40 * 4860314 * 2
def baseEnd_4860314 : Nat := 2495677213776602232822829

theorem tailTrace_4860314 : CollatzResearch.WordTrace tailWord_4860314 prefixEnd_4860314 2495677213776602232822829 := by
  unfold tailWord_4860314
  simp only [CollatzResearch.WordTrace]
  refine ⟨44317553728479982097654999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118180143275946618927079997 44317553728479982097654999)
  ·
    refine ⟨66476330592719973146482499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44317553728479982097654999 66476330592719973146482499)
    ·
      refine ⟨99714495889079959719723749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66476330592719973146482499 99714495889079959719723749)
      ·
        refine ⟨18696467979202492447448203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99714495889079959719723749 18696467979202492447448203)
        ·
          refine ⟨28044701968803738671172305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18696467979202492447448203 28044701968803738671172305)
          ·
            refine ⟨21033526476602804003379229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28044701968803738671172305 21033526476602804003379229)
            ·
              refine ⟨7887572428726051501267211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21033526476602804003379229 7887572428726051501267211)
              ·
                refine ⟨11831358643089077251900817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7887572428726051501267211 11831358643089077251900817)
                ·
                  refine ⟨8873518982316807938925613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11831358643089077251900817 8873518982316807938925613)
                  ·
                    refine ⟨3327569618368802977097105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8873518982316807938925613 3327569618368802977097105)
                    ·
                      refine ⟨2495677213776602232822829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327569618368802977097105 2495677213776602232822829)
                      ·
                        rfl

theorem cell23_4860314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_4860314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860314 prefixEnd_4860314 := by exact prefixLift 4860314
  have htrace : WordTrace (prefixWord ++ tailWord_4860314) baseStart_4860314 baseEnd_4860314 := by
    simpa [prefixWord, tailWord_4860314, baseEnd_4860314] using wordTrace_append hprefix tailTrace_4860314
  have hstable : (prefixWord ++ tailWord_4860314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860314).length < 2 ^ (prefixWord ++ tailWord_4860314).sum := by decide
  have hdescent : baseEnd_4860314 < baseStart_4860314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860320 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 1, 6]
def baseStart_4860320 : Nat := 118140960795 + 4860320 * 2 ^ 59
def prefixEnd_4860320 : Nat := 4983230072969 + 3 ^ 40 * 4860320 * 2
def baseEnd_4860320 : Nat := 831893431553509736449267

theorem tailTrace_4860320 : CollatzResearch.WordTrace tailWord_4860320 prefixEnd_4860320 831893431553509736449267 := by
  unfold tailWord_4860320
  simp only [CollatzResearch.WordTrace]
  refine ⟨88635216875949095707669207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118180289167932127610225609 88635216875949095707669207)
  ·
    refine ⟨132952825313923643561503811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88635216875949095707669207 132952825313923643561503811)
    ·
      refine ⟨199429237970885465342255717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132952825313923643561503811 199429237970885465342255717)
      ·
        refine ⟨37392982119541024751672947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199429237970885465342255717 37392982119541024751672947)
        ·
          refine ⟨56089473179311537127509421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37392982119541024751672947 56089473179311537127509421)
          ·
            refine ⟨21033552442241826422816033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56089473179311537127509421 21033552442241826422816033)
            ·
              refine ⟨15775164331681369817112025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21033552442241826422816033 15775164331681369817112025)
              ·
                refine ⟨11831373248761027362834019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15775164331681369817112025 11831373248761027362834019)
                ·
                  refine ⟨17747059873141541044251029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11831373248761027362834019 17747059873141541044251029)
                  ·
                    refine ⟨831893431553509736449267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17747059873141541044251029 831893431553509736449267)
                    ·
                      rfl

theorem cell23_4860320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 6].length) (baseStart_4860320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860320 prefixEnd_4860320 := by exact prefixLift 4860320
  have htrace : WordTrace (prefixWord ++ tailWord_4860320) baseStart_4860320 baseEnd_4860320 := by
    simpa [prefixWord, tailWord_4860320, baseEnd_4860320] using wordTrace_append hprefix tailTrace_4860320
  have hstable : (prefixWord ++ tailWord_4860320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860320).length < 2 ^ (prefixWord ++ tailWord_4860320).sum := by decide
  have hdescent : baseEnd_4860320 < baseStart_4860320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860337 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 4, 4]
def baseStart_4860337 : Nat := 118140960795 + 4860337 * 2 ^ 59
def prefixEnd_4860337 : Nat := 4983230072969 + 3 ^ 40 * 4860337 * 2
def baseEnd_4860337 : Nat := 831896341277218547611741

theorem tailTrace_4860337 : CollatzResearch.WordTrace tailWord_4860337 prefixEnd_4860337 831896341277218547611741 := by
  unfold tailWord_4860337
  simp only [CollatzResearch.WordTrace]
  refine ⟨177271053792836603318707265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118180702528557735545804843 177271053792836603318707265)
  ·
    refine ⟨132953290344627452489030449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177271053792836603318707265 132953290344627452489030449)
    ·
      refine ⟨99714967758470589366772837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132953290344627452489030449 99714967758470589366772837)
      ·
        refine ⟨18696556454713235506269907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99714967758470589366772837 18696556454713235506269907)
        ·
          refine ⟨28044834682069853259404861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18696556454713235506269907 28044834682069853259404861)
          ·
            refine ⟨10516813005776194972276823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28044834682069853259404861 10516813005776194972276823)
            ·
              refine ⟨15775219508664292458415235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10516813005776194972276823 15775219508664292458415235)
              ·
                refine ⟨23662829262996438687622853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15775219508664292458415235 23662829262996438687622853)
                ·
                  refine ⟨4436780486811832253929285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23662829262996438687622853 4436780486811832253929285)
                  ·
                    refine ⟨831896341277218547611741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4436780486811832253929285 831896341277218547611741)
                    ·
                      rfl

theorem cell23_4860337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_4860337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860337 prefixEnd_4860337 := by exact prefixLift 4860337
  have htrace : WordTrace (prefixWord ++ tailWord_4860337) baseStart_4860337 baseEnd_4860337 := by
    simpa [prefixWord, tailWord_4860337, baseEnd_4860337] using wordTrace_append hprefix tailTrace_4860337
  have hstable : (prefixWord ++ tailWord_4860337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860337).length < 2 ^ (prefixWord ++ tailWord_4860337).sum := by decide
  have hdescent : baseEnd_4860337 < baseStart_4860337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860377 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 6, 1, 3]
def baseStart_4860377 : Nat := 118140960795 + 4860377 * 2 ^ 59
def prefixEnd_4860377 : Nat := 4983230072969 + 3 ^ 40 * 4860377 * 2
def baseEnd_4860377 : Nat := 2495709563057835486335039

theorem tailTrace_4860377 : CollatzResearch.WordTrace tailWord_4860377 prefixEnd_4860377 2495709563057835486335039 := by
  unfold tailWord_4860377
  simp only [CollatzResearch.WordTrace]
  refine ⟨177272512712691690150163385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118181675141794460100108923 177272512712691690150163385)
  ·
    refine ⟨132954384534518767612622539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177272512712691690150163385 132954384534518767612622539)
    ·
      refine ⟨199431576801778151418933809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132954384534518767612622539 199431576801778151418933809)
      ·
        refine ⟨149573682601333613564200357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199431576801778151418933809 149573682601333613564200357)
        ·
          refine ⟨28045065487750052543287567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149573682601333613564200357 28045065487750052543287567)
          ·
            refine ⟨42067598231625078814931351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28045065487750052543287567 42067598231625078814931351)
            ·
              refine ⟨63101397347437618222397027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42067598231625078814931351 63101397347437618222397027)
              ·
                refine ⟨94652096021156427333595541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63101397347437618222397027 94652096021156427333595541)
                ·
                  refine ⟨4436817000991707531262291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94652096021156427333595541 4436817000991707531262291)
                  ·
                    refine ⟨6655225501487561296893437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4436817000991707531262291 6655225501487561296893437)
                    ·
                      refine ⟨2495709563057835486335039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6655225501487561296893437 2495709563057835486335039)
                      ·
                        rfl

theorem cell23_4860377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_4860377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860377 prefixEnd_4860377 := by exact prefixLift 4860377
  have htrace : WordTrace (prefixWord ++ tailWord_4860377) baseStart_4860377 baseEnd_4860377 := by
    simpa [prefixWord, tailWord_4860377, baseEnd_4860377] using wordTrace_append hprefix tailTrace_4860377
  have hstable : (prefixWord ++ tailWord_4860377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860377).length < 2 ^ (prefixWord ++ tailWord_4860377).sum := by decide
  have hdescent : baseEnd_4860377 < baseStart_4860377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860394 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_4860394 : Nat := 118140960795 + 4860394 * 2 ^ 59
def prefixEnd_4860394 : Nat := 4983230072969 + 3 ^ 40 * 4860394 * 2
def baseEnd_4860394 : Nat := 2495718292228961919822461

theorem tailTrace_4860394 : CollatzResearch.WordTrace tailWord_4860394 prefixEnd_4860394 2495718292228961919822461 := by
  unfold tailWord_4860394
  simp only [CollatzResearch.WordTrace]
  refine ⟨44318283188407525513383059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118182088502420068035688157 44318283188407525513383059)
  ·
    refine ⟨66477424782611288270074589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44318283188407525513383059 66477424782611288270074589)
    ·
      refine ⟨24929034293479233101277971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66477424782611288270074589 24929034293479233101277971)
      ·
        refine ⟨37393551440218849651916957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24929034293479233101277971 37393551440218849651916957)
        ·
          refine ⟨14022581790082068619468859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37393551440218849651916957 14022581790082068619468859)
          ·
            refine ⟨21033872685123102929203289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14022581790082068619468859 21033872685123102929203289)
            ·
              refine ⟨15775404513842327196902467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21033872685123102929203289 15775404513842327196902467)
              ·
                refine ⟨23663106770763490795353701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15775404513842327196902467 23663106770763490795353701)
                ·
                  refine ⟨4436832519518154524128819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23663106770763490795353701 4436832519518154524128819)
                  ·
                    refine ⟨6655248779277231786193229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4436832519518154524128819 6655248779277231786193229)
                    ·
                      refine ⟨2495718292228961919822461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6655248779277231786193229 2495718292228961919822461)
                      ·
                        rfl

theorem cell23_4860394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_4860394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860394 prefixEnd_4860394 := by exact prefixLift 4860394
  have htrace : WordTrace (prefixWord ++ tailWord_4860394) baseStart_4860394 baseEnd_4860394 := by
    simpa [prefixWord, tailWord_4860394, baseEnd_4860394] using wordTrace_append hprefix tailTrace_4860394
  have hstable : (prefixWord ++ tailWord_4860394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860394).length < 2 ^ (prefixWord ++ tailWord_4860394).sum := by decide
  have hdescent : baseEnd_4860394 < baseStart_4860394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860400 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 4]
def baseStart_4860400 : Nat := 118140960795 + 4860400 * 2 ^ 59
def prefixEnd_4860400 : Nat := 4983230072969 + 3 ^ 40 * 4860400 * 2
def baseEnd_4860400 : Nat := 2495721373112888896347433

theorem tailTrace_4860400 : CollatzResearch.WordTrace tailWord_4860400 prefixEnd_4860400 2495721373112888896347433 := by
  unfold tailWord_4860400
  simp only [CollatzResearch.WordTrace]
  refine ⟨88636675795804182539125327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118182234394405576718833769 88636675795804182539125327)
  ·
    refine ⟨132955013693706273808687991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88636675795804182539125327 132955013693706273808687991)
    ·
      refine ⟨199432520540559410713031987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132955013693706273808687991 199432520540559410713031987)
      ·
        refine ⟨299148780810839116069547981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199432520540559410713031987 299148780810839116069547981)
        ·
          refine ⟨112180792804064668526080493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299148780810839116069547981 112180792804064668526080493)
          ·
            refine ⟨42067797301524250697280185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112180792804064668526080493 42067797301524250697280185)
            ·
              refine ⟨31550847976143188022960139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42067797301524250697280185 31550847976143188022960139)
              ·
                refine ⟨47326271964214782034440209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31550847976143188022960139 47326271964214782034440209)
                ·
                  refine ⟨35494703973161086525830157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47326271964214782034440209 35494703973161086525830157)
                  ·
                    refine ⟨13310513989935407447186309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35494703973161086525830157 13310513989935407447186309)
                    ·
                      refine ⟨2495721373112888896347433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13310513989935407447186309 2495721373112888896347433)
                      ·
                        rfl

theorem cell23_4860400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_4860400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860400 prefixEnd_4860400 := by exact prefixLift 4860400
  have htrace : WordTrace (prefixWord ++ tailWord_4860400) baseStart_4860400 baseEnd_4860400 := by
    simpa [prefixWord, tailWord_4860400, baseEnd_4860400] using wordTrace_append hprefix tailTrace_4860400
  have hstable : (prefixWord ++ tailWord_4860400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860400).length < 2 ^ (prefixWord ++ tailWord_4860400).sum := by decide
  have hdescent : baseEnd_4860400 < baseStart_4860400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860405 : List Nat := [1, 3, 5, 1, 3, 1, 2, 1, 2, 4]
def baseStart_4860405 : Nat := 118140960795 + 4860405 * 2 ^ 59
def prefixEnd_4860405 : Nat := 4983230072969 + 3 ^ 40 * 4860405 * 2
def baseEnd_4860405 : Nat := 831907980172053792261637

theorem tailTrace_4860405 : CollatzResearch.WordTrace tailWord_4860405 prefixEnd_4860405 831907980172053792261637 := by
  unfold tailWord_4860405
  simp only [CollatzResearch.WordTrace]
  refine ⟨177273533956590250932182669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118182355971060167288121779 177273533956590250932182669)
  ·
    refine ⟨66477575233721344099568501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177273533956590250932182669 66477575233721344099568501)
    ·
      refine ⟨6232272678161376009334547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66477575233721344099568501 6232272678161376009334547)
      ·
        refine ⟨9348409017242064014001821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6232272678161376009334547 9348409017242064014001821)
        ·
          refine ⟨3505653381465774005250683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9348409017242064014001821 3505653381465774005250683)
          ·
            refine ⟨5258480072198661007876025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3505653381465774005250683 5258480072198661007876025)
            ·
              refine ⟨3943860054148995755907019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5258480072198661007876025 3943860054148995755907019)
              ·
                refine ⟨5915790081223493633860529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943860054148995755907019 5915790081223493633860529)
                ·
                  refine ⟨4436842560917620225395397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5915790081223493633860529 4436842560917620225395397)
                  ·
                    refine ⟨831907980172053792261637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4436842560917620225395397 831907980172053792261637)
                    ·
                      rfl

theorem cell23_4860405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_4860405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860405 prefixEnd_4860405 := by exact prefixLift 4860405
  have htrace : WordTrace (prefixWord ++ tailWord_4860405) baseStart_4860405 baseEnd_4860405 := by
    simpa [prefixWord, tailWord_4860405, baseEnd_4860405] using wordTrace_append hprefix tailTrace_4860405
  have hstable : (prefixWord ++ tailWord_4860405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860405).length < 2 ^ (prefixWord ++ tailWord_4860405).sum := by decide
  have hdescent : baseEnd_4860405 < baseStart_4860405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860451 : List Nat := [1, 1, 1, 4, 4, 1, 1, 4, 2, 2, 2]
def baseStart_4860451 : Nat := 118140960795 + 4860451 * 2 ^ 59
def prefixEnd_4860451 : Nat := 4983230072969 + 3 ^ 40 * 4860451 * 2
def baseEnd_4860451 : Nat := 2495747560626268196809699

theorem tailTrace_4860451 : CollatzResearch.WordTrace tailWord_4860451 prefixEnd_4860451 2495747560626268196809699 := by
  unfold tailWord_4860451
  simp only [CollatzResearch.WordTrace]
  refine ⟨177275211714423600788357207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118183474476282400525571471 177275211714423600788357207)
  ·
    refine ⟨265912817571635401182535811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177275211714423600788357207 265912817571635401182535811)
    ·
      refine ⟨398869226357453101773803717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265912817571635401182535811 398869226357453101773803717)
      ·
        refine ⟨74787979942022456582588197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 398869226357453101773803717 74787979942022456582588197)
        ·
          refine ⟨14022746239129210609235287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74787979942022456582588197 14022746239129210609235287)
          ·
            refine ⟨21034119358693815913852931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14022746239129210609235287 21034119358693815913852931)
            ·
              refine ⟨31551179038040723870779397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21034119358693815913852931 31551179038040723870779397)
              ·
                refine ⟨5915846069632635725771137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31551179038040723870779397 5915846069632635725771137)
                ·
                  refine ⟨4436884552224476794328353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5915846069632635725771137 4436884552224476794328353)
                  ·
                    refine ⟨3327663414168357595746265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4436884552224476794328353 3327663414168357595746265)
                    ·
                      refine ⟨2495747560626268196809699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327663414168357595746265 2495747560626268196809699)
                      ·
                        rfl

theorem cell23_4860451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_4860451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860451 prefixEnd_4860451 := by exact prefixLift 4860451
  have htrace : WordTrace (prefixWord ++ tailWord_4860451) baseStart_4860451 baseEnd_4860451 := by
    simpa [prefixWord, tailWord_4860451, baseEnd_4860451] using wordTrace_append hprefix tailTrace_4860451
  have hstable : (prefixWord ++ tailWord_4860451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860451).length < 2 ^ (prefixWord ++ tailWord_4860451).sum := by decide
  have hdescent : baseEnd_4860451 < baseStart_4860451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860467 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 3]
def baseStart_4860467 : Nat := 118140960795 + 4860467 * 2 ^ 59
def prefixEnd_4860467 : Nat := 4983230072969 + 3 ^ 40 * 4860467 * 2
def baseEnd_4860467 : Nat := 2495755776316740134209625

theorem tailTrace_4860467 : CollatzResearch.WordTrace tailWord_4860467 prefixEnd_4860467 2495755776316740134209625 := by
  unfold tailWord_4860467
  simp only [CollatzResearch.WordTrace]
  refine ⟨177275795282365635520939655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118183863521577090347293103 177275795282365635520939655)
  ·
    refine ⟨265913692923548453281409483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177275795282365635520939655 265913692923548453281409483)
    ·
      refine ⟨398870539385322679922114225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265913692923548453281409483 398870539385322679922114225)
      ·
        refine ⟨299152904538992009941585669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398870539385322679922114225 299152904538992009941585669)
        ·
          refine ⟨56091169601061001864047313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 299152904538992009941585669 56091169601061001864047313)
          ·
            refine ⟨42068377200795751398035485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56091169601061001864047313 42068377200795751398035485)
            ·
              refine ⟨15775641450298406774263307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42068377200795751398035485 15775641450298406774263307)
              ·
                refine ⟨23663462175447610161394961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15775641450298406774263307 23663462175447610161394961)
                ·
                  refine ⟨17747596631585707621046221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23663462175447610161394961 17747596631585707621046221)
                  ·
                    refine ⟨6655348736844640357892333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17747596631585707621046221 6655348736844640357892333)
                    ·
                      refine ⟨2495755776316740134209625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6655348736844640357892333 2495755776316740134209625)
                      ·
                        rfl

theorem cell23_4860467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 3].length) (baseStart_4860467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860467 prefixEnd_4860467 := by exact prefixLift 4860467
  have htrace : WordTrace (prefixWord ++ tailWord_4860467) baseStart_4860467 baseEnd_4860467 := by
    simpa [prefixWord, tailWord_4860467, baseEnd_4860467] using wordTrace_append hprefix tailTrace_4860467
  have hstable : (prefixWord ++ tailWord_4860467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860467).length < 2 ^ (prefixWord ++ tailWord_4860467).sum := by decide
  have hdescent : baseEnd_4860467 < baseStart_4860467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860480 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 7]
def baseStart_4860480 : Nat := 118140960795 + 4860480 * 2 ^ 59
def prefixEnd_4860480 : Nat := 4983230072969 + 3 ^ 40 * 4860480 * 2
def baseEnd_4860480 : Nat := 2495762451565248583347065

theorem tailTrace_4860480 : CollatzResearch.WordTrace tailWord_4860480 prefixEnd_4860480 2495762451565248583347065 := by
  unfold tailWord_4860480
  simp only [CollatzResearch.WordTrace]
  refine ⟨88638134715659269370581447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118184179620879025827441929 88638134715659269370581447)
  ·
    refine ⟨132957202073488904055872171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88638134715659269370581447 132957202073488904055872171)
    ·
      refine ⟨199435803110233356083808257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132957202073488904055872171 199435803110233356083808257)
      ·
        refine ⟨149576852332675017062856193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199435803110233356083808257 149576852332675017062856193)
        ·
          refine ⟨112182639249506262797142145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149576852332675017062856193 112182639249506262797142145)
          ·
            refine ⟨84136979437129697097856609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112182639249506262797142145 84136979437129697097856609)
            ·
              refine ⟨63102734577847272823392457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84136979437129697097856609 63102734577847272823392457)
              ·
                refine ⟨47327050933385454617544343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63102734577847272823392457 47327050933385454617544343)
                ·
                  refine ⟨70990576400078181926316515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47327050933385454617544343 70990576400078181926316515)
                  ·
                    refine ⟨106485864600117272889474773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70990576400078181926316515 106485864600117272889474773)
                    ·
                      refine ⟨2495762451565248583347065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106485864600117272889474773 2495762451565248583347065)
                      ·
                        rfl

theorem cell23_4860480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_4860480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860480 prefixEnd_4860480 := by exact prefixLift 4860480
  have htrace : WordTrace (prefixWord ++ tailWord_4860480) baseStart_4860480 baseEnd_4860480 := by
    simpa [prefixWord, tailWord_4860480, baseEnd_4860480] using wordTrace_append hprefix tailTrace_4860480
  have hstable : (prefixWord ++ tailWord_4860480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860480).length < 2 ^ (prefixWord ++ tailWord_4860480).sum := by decide
  have hdescent : baseEnd_4860480 < baseStart_4860480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860487 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 1, 7]
def baseStart_4860487 : Nat := 118140960795 + 4860487 * 2 ^ 59
def prefixEnd_4860487 : Nat := 4983230072969 + 3 ^ 40 * 4860487 * 2
def baseEnd_4860487 : Nat := 831922015309943351986511

theorem tailTrace_4860487 : CollatzResearch.WordTrace tailWord_4860487 prefixEnd_4860487 831922015309943351986511 := by
  unfold tailWord_4860487
  simp only [CollatzResearch.WordTrace]
  refine ⟨177276524742293178936667715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118184349828195452624445143 177276524742293178936667715)
  ·
    refine ⟨265914787113439768405001573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177276524742293178936667715 265914787113439768405001573)
    ·
      refine ⟨49859022583769956575937795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265914787113439768405001573 49859022583769956575937795)
      ·
        refine ⟨74788533875654934863906693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49859022583769956575937795 74788533875654934863906693)
        ·
          refine ⟨14022850101685300286982505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74788533875654934863906693 14022850101685300286982505)
          ·
            refine ⟨10517137576263975215236879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14022850101685300286982505 10517137576263975215236879)
            ·
              refine ⟨15775706364395962822855319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10517137576263975215236879 15775706364395962822855319)
              ·
                refine ⟨23663559546593944234282979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15775706364395962822855319 23663559546593944234282979)
                ·
                  refine ⟨35495339319890916351424469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23663559546593944234282979 35495339319890916351424469)
                  ·
                    refine ⟨831922015309943351986511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35495339319890916351424469 831922015309943351986511)
                    ·
                      rfl

theorem cell23_4860487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_4860487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860487 prefixEnd_4860487 := by exact prefixLift 4860487
  have htrace : WordTrace (prefixWord ++ tailWord_4860487) baseStart_4860487 baseEnd_4860487 := by
    simpa [prefixWord, tailWord_4860487, baseEnd_4860487] using wordTrace_append hprefix tailTrace_4860487
  have hstable : (prefixWord ++ tailWord_4860487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860487).length < 2 ^ (prefixWord ++ tailWord_4860487).sum := by decide
  have hdescent : baseEnd_4860487 < baseStart_4860487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860507 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 12, 2]
def baseStart_4860507 : Nat := 118140960795 + 4860507 * 2 ^ 59
def prefixEnd_4860507 : Nat := 4983230072969 + 3 ^ 40 * 4860507 * 2
def baseEnd_4860507 : Nat := 2495776315542919977709441

theorem tailTrace_4860507 : CollatzResearch.WordTrace tailWord_4860507 prefixEnd_4860507 2495776315542919977709441 := by
  unfold tailWord_4860507
  simp only [CollatzResearch.WordTrace]
  refine ⟨177277254202220722352395775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118184836134813814901597183 177277254202220722352395775)
  ·
    refine ⟨265915881303331083528593663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177277254202220722352395775 265915881303331083528593663)
    ·
      refine ⟨398873821954996625292890495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265915881303331083528593663 398873821954996625292890495)
      ·
        refine ⟨598310732932494937939335743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398873821954996625292890495 598310732932494937939335743)
        ·
          refine ⟨897466099398742406909003615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598310732932494937939335743 897466099398742406909003615)
          ·
            refine ⟨1346199149098113610363505423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897466099398742406909003615 1346199149098113610363505423)
            ·
              refine ⟨2019298723647170415545258135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346199149098113610363505423 2019298723647170415545258135)
              ·
                refine ⟨3028948085470755623317887203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2019298723647170415545258135 3028948085470755623317887203)
                ·
                  refine ⟨4543422128206133434976830805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3028948085470755623317887203 4543422128206133434976830805)
                  ·
                    refine ⟨3327701754057226636945921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 4543422128206133434976830805 3327701754057226636945921)
                    ·
                      refine ⟨2495776315542919977709441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327701754057226636945921 2495776315542919977709441)
                      ·
                        rfl

theorem cell23_4860507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12, 2].length) (baseStart_4860507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860507 prefixEnd_4860507 := by exact prefixLift 4860507
  have htrace : WordTrace (prefixWord ++ tailWord_4860507) baseStart_4860507 baseEnd_4860507 := by
    simpa [prefixWord, tailWord_4860507, baseEnd_4860507] using wordTrace_append hprefix tailTrace_4860507
  have hstable : (prefixWord ++ tailWord_4860507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860507).length < 2 ^ (prefixWord ++ tailWord_4860507).sum := by decide
  have hdescent : baseEnd_4860507 < baseStart_4860507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860524 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 2, 4, 2]
def baseStart_4860524 : Nat := 118140960795 + 4860524 * 2 ^ 59
def prefixEnd_4860524 : Nat := 4983230072969 + 3 ^ 40 * 4860524 * 2
def baseEnd_4860524 : Nat := 2495785044714046411196863

theorem tailTrace_4860524 : CollatzResearch.WordTrace tailWord_4860524 prefixEnd_4860524 2495785044714046411196863 := by
  unfold tailWord_4860524
  simp only [CollatzResearch.WordTrace]
  refine ⟨88638937121579567127882313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118185249495439422837176417 88638937121579567127882313)
  ·
    refine ⟨66479202841184675345911735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88638937121579567127882313 66479202841184675345911735)
    ·
      refine ⟨99718804261777013018867603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66479202841184675345911735 99718804261777013018867603)
      ·
        refine ⟨149578206392665519528301405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99718804261777013018867603 149578206392665519528301405)
        ·
          refine ⟨56091827397249569823113027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149578206392665519528301405 56091827397249569823113027)
          ·
            refine ⟨84137741095874354734669541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56091827397249569823113027 84137741095874354734669541)
            ·
              refine ⟨15775826455476441512750539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84137741095874354734669541 15775826455476441512750539)
              ·
                refine ⟨23663739683214662269125809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15775826455476441512750539 23663739683214662269125809)
                ·
                  refine ⟨17747804762410996701844357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23663739683214662269125809 17747804762410996701844357)
                  ·
                    refine ⟨3327713392952061881595817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17747804762410996701844357 3327713392952061881595817)
                    ·
                      refine ⟨2495785044714046411196863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327713392952061881595817 2495785044714046411196863)
                      ·
                        rfl

theorem cell23_4860524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 4, 2].length) (baseStart_4860524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860524 prefixEnd_4860524 := by exact prefixLift 4860524
  have htrace : WordTrace (prefixWord ++ tailWord_4860524) baseStart_4860524 baseEnd_4860524 := by
    simpa [prefixWord, tailWord_4860524, baseEnd_4860524] using wordTrace_append hprefix tailTrace_4860524
  have hstable : (prefixWord ++ tailWord_4860524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860524).length < 2 ^ (prefixWord ++ tailWord_4860524).sum := by decide
  have hdescent : baseEnd_4860524 < baseStart_4860524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860527 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 3]
def baseStart_4860527 : Nat := 118140960795 + 4860527 * 2 ^ 59
def prefixEnd_4860527 : Nat := 4983230072969 + 3 ^ 40 * 4860527 * 2
def baseEnd_4860527 : Nat := 2495786585156009899459349

theorem tailTrace_4860527 : CollatzResearch.WordTrace tailWord_4860527 prefixEnd_4860527 2495786585156009899459349 := by
  unfold tailWord_4860527
  simp only [CollatzResearch.WordTrace]
  refine ⟨177277983662148265768123835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118185322441432177178749223 177277983662148265768123835)
  ·
    refine ⟨265916975493222398652185753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177277983662148265768123835 265916975493222398652185753)
    ·
      refine ⟨199437731619916798989139315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265916975493222398652185753 199437731619916798989139315)
      ·
        refine ⟨299156597429875198483708973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199437731619916798989139315 299156597429875198483708973)
        ·
          refine ⟨112183724036203199431390865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299156597429875198483708973 112183724036203199431390865)
          ·
            refine ⟨84137793027152399573543149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112183724036203199431390865 84137793027152399573543149)
            ·
              refine ⟨31551672385182149840078681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84137793027152399573543149 31551672385182149840078681)
              ·
                refine ⟨23663754288886612380059011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31551672385182149840078681 23663754288886612380059011)
                ·
                  refine ⟨35495631433329918570088517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23663754288886612380059011 35495631433329918570088517)
                  ·
                    refine ⟨6655430893749359731891597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35495631433329918570088517 6655430893749359731891597)
                    ·
                      refine ⟨2495786585156009899459349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6655430893749359731891597 2495786585156009899459349)
                      ·
                        rfl

theorem cell23_4860527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 3].length) (baseStart_4860527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860527 prefixEnd_4860527 := by exact prefixLift 4860527
  have htrace : WordTrace (prefixWord ++ tailWord_4860527) baseStart_4860527 baseEnd_4860527 := by
    simpa [prefixWord, tailWord_4860527, baseEnd_4860527] using wordTrace_append hprefix tailTrace_4860527
  have hstable : (prefixWord ++ tailWord_4860527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860527).length < 2 ^ (prefixWord ++ tailWord_4860527).sum := by decide
  have hdescent : baseEnd_4860527 < baseStart_4860527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860564 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 8]
def baseStart_4860564 : Nat := 118140960795 + 4860564 * 2 ^ 59
def prefixEnd_4860564 : Nat := 4983230072969 + 3 ^ 40 * 4860564 * 2
def baseEnd_4860564 : Nat := 277311731548914028299631

theorem tailTrace_4860564 : CollatzResearch.WordTrace tailWord_4860564 prefixEnd_4860564 277311731548914028299631 := by
  unfold tailWord_4860564
  simp only [CollatzResearch.WordTrace]
  refine ⟨88639666581507110543610373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118186222108676147391480497 88639666581507110543610373)
  ·
    refine ⟨16619937484032583226926945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88639666581507110543610373 16619937484032583226926945)
    ·
      refine ⟨12464953113024437420195209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16619937484032583226926945 12464953113024437420195209)
      ·
        refine ⟨9348714834768328065146407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12464953113024437420195209 9348714834768328065146407)
        ·
          refine ⟨14023072252152492097719611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9348714834768328065146407 14023072252152492097719611)
          ·
            refine ⟨21034608378228738146579417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14023072252152492097719611 21034608378228738146579417)
            ·
              refine ⟨15775956283671553609934563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21034608378228738146579417 15775956283671553609934563)
              ·
                refine ⟨23663934425507330414901845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15775956283671553609934563 23663934425507330414901845)
                ·
                  refine ⟨277311731548914028299631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23663934425507330414901845 277311731548914028299631)
                  ·
                    rfl

theorem cell23_4860564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_4860564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860564 prefixEnd_4860564 := by exact prefixLift 4860564
  have htrace : WordTrace (prefixWord ++ tailWord_4860564) baseStart_4860564 baseEnd_4860564 := by
    simpa [prefixWord, tailWord_4860564, baseEnd_4860564] using wordTrace_append hprefix tailTrace_4860564
  have hstable : (prefixWord ++ tailWord_4860564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860564).length < 2 ^ (prefixWord ++ tailWord_4860564).sum := by decide
  have hdescent : baseEnd_4860564 < baseStart_4860564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860568 : List Nat := [2, 1, 2, 4, 1, 1, 5, 2, 1, 4]
def baseStart_4860568 : Nat := 118140960795 + 4860568 * 2 ^ 59
def prefixEnd_4860568 : Nat := 4983230072969 + 3 ^ 40 * 4860568 * 2
def baseEnd_4860568 : Nat := 831935879287614746348887

theorem tailTrace_4860568 : CollatzResearch.WordTrace tailWord_4860568 prefixEnd_4860568 831935879287614746348887 := by
  unfold tailWord_4860568
  simp only [CollatzResearch.WordTrace]
  refine ⟨88639739527499864885183179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118186319369999819846910905 88639739527499864885183179)
  ·
    refine ⟨132959609291249797327774769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88639739527499864885183179 132959609291249797327774769)
    ·
      refine ⟨99719706968437347995831077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132959609291249797327774769 99719706968437347995831077)
      ·
        refine ⟨18697445056582002749218327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99719706968437347995831077 18697445056582002749218327)
        ·
          refine ⟨28046167584873004123827491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18697445056582002749218327 28046167584873004123827491)
          ·
            refine ⟨42069251377309506185741237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28046167584873004123827491 42069251377309506185741237)
            ·
              refine ⟨3943992316622766204913241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42069251377309506185741237 3943992316622766204913241)
              ·
                refine ⟨2957994237467074653684931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3943992316622766204913241 2957994237467074653684931)
                ·
                  refine ⟨4436991356200611980527397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957994237467074653684931 4436991356200611980527397)
                  ·
                    refine ⟨831935879287614746348887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4436991356200611980527397 831935879287614746348887)
                    ·
                      rfl

theorem cell23_4860568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_4860568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860568 prefixEnd_4860568 := by exact prefixLift 4860568
  have htrace : WordTrace (prefixWord ++ tailWord_4860568) baseStart_4860568 baseEnd_4860568 := by
    simpa [prefixWord, tailWord_4860568, baseEnd_4860568] using wordTrace_append hprefix tailTrace_4860568
  have hstable : (prefixWord ++ tailWord_4860568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860568).length < 2 ^ (prefixWord ++ tailWord_4860568).sum := by decide
  have hdescent : baseEnd_4860568 < baseStart_4860568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860607 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 3, 6]
def baseStart_4860607 : Nat := 118140960795 + 4860607 * 2 ^ 59
def prefixEnd_4860607 : Nat := 4983230072969 + 3 ^ 40 * 4860607 * 2
def baseEnd_4860607 : Nat := 831942554536123195486327

theorem tailTrace_4860607 : CollatzResearch.WordTrace tailWord_4860607 prefixEnd_4860607 831942554536123195486327 := by
  unfold tailWord_4860607
  simp only [CollatzResearch.WordTrace]
  refine ⟨177280901501858439431036075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118187267667905626287357383 177280901501858439431036075)
  ·
    refine ⟨265921352252787659146554113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177280901501858439431036075 265921352252787659146554113)
    ·
      refine ⟨199441014189590744359915585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265921352252787659146554113 199441014189590744359915585)
      ·
        refine ⟨149580760642193058269936689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199441014189590744359915585 149580760642193058269936689)
        ·
          refine ⟨112185570481644793702452517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149580760642193058269936689 112185570481644793702452517)
          ·
            refine ⟨21034794465308398819209847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112185570481644793702452517 21034794465308398819209847)
            ·
              refine ⟨31552191697962598228814771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21034794465308398819209847 31552191697962598228814771)
              ·
                refine ⟨47328287546943897343222157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31552191697962598228814771 47328287546943897343222157)
                ·
                  refine ⟨17748107830103961503708309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47328287546943897343222157 17748107830103961503708309)
                  ·
                    refine ⟨831942554536123195486327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17748107830103961503708309 831942554536123195486327)
                    ·
                      rfl

theorem cell23_4860607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_4860607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860607 prefixEnd_4860607 := by exact prefixLift 4860607
  have htrace : WordTrace (prefixWord ++ tailWord_4860607) baseStart_4860607 baseEnd_4860607 := by
    simpa [prefixWord, tailWord_4860607, baseEnd_4860607] using wordTrace_append hprefix tailTrace_4860607
  have hstable : (prefixWord ++ tailWord_4860607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860607).length < 2 ^ (prefixWord ++ tailWord_4860607).sum := by decide
  have hdescent : baseEnd_4860607 < baseStart_4860607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860634 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3]
def baseStart_4860634 : Nat := 118140960795 + 4860634 * 2 ^ 59
def prefixEnd_4860634 : Nat := 4983230072969 + 3 ^ 40 * 4860634 * 2
def baseEnd_4860634 : Nat := 2495841527586040980821357

theorem tailTrace_4860634 : CollatzResearch.WordTrace tailWord_4860634 prefixEnd_4860634 2495841527586040980821357 := by
  unfold tailWord_4860634
  simp only [CollatzResearch.WordTrace]
  refine ⟨44320471568190155760567239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118187924181840415361512637 44320471568190155760567239)
  ·
    refine ⟨66480707352285233640850859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44320471568190155760567239 66480707352285233640850859)
    ·
      refine ⟨99721061028427850461276289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66480707352285233640850859 99721061028427850461276289)
      ·
        refine ⟨74790795771320887845957217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99721061028427850461276289 74790795771320887845957217)
        ·
          refine ⟨56093096828490665884467913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74790795771320887845957217 56093096828490665884467913)
          ·
            refine ⟨42069822621367999413350935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56093096828490665884467913 42069822621367999413350935)
            ·
              refine ⟨63104733932051999120026403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42069822621367999413350935 63104733932051999120026403)
              ·
                refine ⟨94657100898077998680039605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63104733932051999120026403 94657100898077998680039605)
                ·
                  refine ⟨8874103209194812376253713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94657100898077998680039605 8874103209194812376253713)
                  ·
                    refine ⟨6655577406896109282190285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8874103209194812376253713 6655577406896109282190285)
                    ·
                      refine ⟨2495841527586040980821357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6655577406896109282190285 2495841527586040980821357)
                      ·
                        rfl

theorem cell23_4860634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_4860634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860634 prefixEnd_4860634 := by exact prefixLift 4860634
  have htrace : WordTrace (prefixWord ++ tailWord_4860634) baseStart_4860634 baseEnd_4860634 := by
    simpa [prefixWord, tailWord_4860634, baseEnd_4860634] using wordTrace_append hprefix tailTrace_4860634
  have hstable : (prefixWord ++ tailWord_4860634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860634).length < 2 ^ (prefixWord ++ tailWord_4860634).sum := by decide
  have hdescent : baseEnd_4860634 < baseStart_4860634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860641 : List Nat := [1, 2, 3, 1, 4, 1, 2, 3, 2, 4]
def baseStart_4860641 : Nat := 118140960795 + 4860641 * 2 ^ 59
def prefixEnd_4860641 : Nat := 4983230072969 + 3 ^ 40 * 4860641 * 2
def baseEnd_4860641 : Nat := 831948373983540817811275

theorem tailTrace_4860641 : CollatzResearch.WordTrace tailWord_4860641 prefixEnd_4860641 831948373983540817811275 := by
  unfold tailWord_4860641
  simp only [CollatzResearch.WordTrace]
  refine ⟨177282141583735263237773777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118188094389156842158515851 177282141583735263237773777)
  ·
    refine ⟨132961606187801447428330333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177282141583735263237773777 132961606187801447428330333)
    ·
      refine ⟨49860602320425542785623875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132961606187801447428330333 49860602320425542785623875)
      ·
        refine ⟨74790903480638314178435813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49860602320425542785623875 74790903480638314178435813)
        ·
          refine ⟨14023294402619683908456715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74790903480638314178435813 14023294402619683908456715)
          ·
            refine ⟨21034941603929525862685073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14023294402619683908456715 21034941603929525862685073)
            ·
              refine ⟨15776206202947144397013805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21034941603929525862685073 15776206202947144397013805)
              ·
                refine ⟨5916077326105179148880177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15776206202947144397013805 5916077326105179148880177)
                ·
                  refine ⟨4437057994578884361660133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5916077326105179148880177 4437057994578884361660133)
                  ·
                    refine ⟨831948373983540817811275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4437057994578884361660133 831948373983540817811275)
                    ·
                      rfl

theorem cell23_4860641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_4860641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860641 prefixEnd_4860641 := by exact prefixLift 4860641
  have htrace : WordTrace (prefixWord ++ tailWord_4860641) baseStart_4860641 baseEnd_4860641 := by
    simpa [prefixWord, tailWord_4860641, baseEnd_4860641] using wordTrace_append hprefix tailTrace_4860641
  have hstable : (prefixWord ++ tailWord_4860641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860641).length < 2 ^ (prefixWord ++ tailWord_4860641).sum := by decide
  have hdescent : baseEnd_4860641 < baseStart_4860641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860644 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_4860644 : Nat := 118140960795 + 4860644 * 2 ^ 59
def prefixEnd_4860644 : Nat := 4983230072969 + 3 ^ 40 * 4860644 * 2
def baseEnd_4860644 : Nat := 2495846662392585941696311

theorem tailTrace_4860644 : CollatzResearch.WordTrace tailWord_4860644 prefixEnd_4860644 2495846662392585941696311 := by
  unfold tailWord_4860644
  simp only [CollatzResearch.WordTrace]
  refine ⟨88641125501362197375066493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118188167335149596500088657 88641125501362197375066493)
  ·
    refine ⟨33240422063010824015649935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88641125501362197375066493 33240422063010824015649935)
    ·
      refine ⟨49860633094516236023474903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33240422063010824015649935 49860633094516236023474903)
      ·
        refine ⟨74790949641774354035212355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49860633094516236023474903 74790949641774354035212355)
        ·
          refine ⟨112186424462661531052818533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74790949641774354035212355 112186424462661531052818533)
          ·
            refine ⟨21034954586749037072403475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112186424462661531052818533 21034954586749037072403475)
            ·
              refine ⟨31552431880123555608605213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21034954586749037072403475 31552431880123555608605213)
              ·
                refine ⟨11832161955046333353226955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31552431880123555608605213 11832161955046333353226955)
                ·
                  refine ⟨17748242932569500029840433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11832161955046333353226955 17748242932569500029840433)
                  ·
                    refine ⟨13311182199427125022380325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17748242932569500029840433 13311182199427125022380325)
                    ·
                      refine ⟨2495846662392585941696311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13311182199427125022380325 2495846662392585941696311)
                      ·
                        rfl

theorem cell23_4860644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_4860644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860644 prefixEnd_4860644 := by exact prefixLift 4860644
  have htrace : WordTrace (prefixWord ++ tailWord_4860644) baseStart_4860644 baseEnd_4860644 := by
    simpa [prefixWord, tailWord_4860644, baseEnd_4860644] using wordTrace_append hprefix tailTrace_4860644
  have hstable : (prefixWord ++ tailWord_4860644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860644).length < 2 ^ (prefixWord ++ tailWord_4860644).sum := by decide
  have hdescent : baseEnd_4860644 < baseStart_4860644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860664 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 1, 3, 3]
def baseStart_4860664 : Nat := 118140960795 + 4860664 * 2 ^ 59
def prefixEnd_4860664 : Nat := 4983230072969 + 3 ^ 40 * 4860664 * 2
def baseEnd_4860664 : Nat := 2495856932005675863446219

theorem tailTrace_4860664 : CollatzResearch.WordTrace tailWord_4860664 prefixEnd_4860664 2495856932005675863446219 := by
  unfold tailWord_4860664
  simp only [CollatzResearch.WordTrace]
  refine ⟨88641490231325969082930523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118188653641767958777240697 88641490231325969082930523)
  ·
    refine ⟨132962235346988953624395785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88641490231325969082930523 132962235346988953624395785)
    ·
      refine ⟨99721676510241715218296839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132962235346988953624395785 99721676510241715218296839)
      ·
        refine ⟨149582514765362572827445259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99721676510241715218296839 149582514765362572827445259)
        ·
          refine ⟨224373772148043859241167889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149582514765362572827445259 224373772148043859241167889)
          ·
            refine ⟨168280329111032894430875917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224373772148043859241167889 168280329111032894430875917)
            ·
              refine ⟨63105123416637335411578469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168280329111032894430875917 63105123416637335411578469)
              ·
                refine ⟨11832210640619500389670963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63105123416637335411578469 11832210640619500389670963)
                ·
                  refine ⟨17748315960929250584506445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11832210640619500389670963 17748315960929250584506445)
                  ·
                    refine ⟨6655618485348468969189917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17748315960929250584506445 6655618485348468969189917)
                    ·
                      refine ⟨2495856932005675863446219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6655618485348468969189917 2495856932005675863446219)
                      ·
                        rfl

theorem cell23_4860664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_4860664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860664 prefixEnd_4860664 := by exact prefixLift 4860664
  have htrace : WordTrace (prefixWord ++ tailWord_4860664) baseStart_4860664 baseEnd_4860664 := by
    simpa [prefixWord, tailWord_4860664, baseEnd_4860664] using wordTrace_append hprefix tailTrace_4860664
  have hstable : (prefixWord ++ tailWord_4860664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860664).length < 2 ^ (prefixWord ++ tailWord_4860664).sum := by decide
  have hdescent : baseEnd_4860664 < baseStart_4860664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860668 : List Nat := [2, 2, 2, 1, 3, 2, 4, 1, 1, 2, 3]
def baseStart_4860668 : Nat := 118140960795 + 4860668 * 2 ^ 59
def prefixEnd_4860668 : Nat := 4983230072969 + 3 ^ 40 * 4860668 * 2
def baseEnd_4860668 : Nat := 2495858985928293847796201

theorem tailTrace_4860668 : CollatzResearch.WordTrace tailWord_4860668 prefixEnd_4860668 2495858985928293847796201 := by
  unfold tailWord_4860668
  simp only [CollatzResearch.WordTrace]
  refine ⟨88641563177318723424503329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118188750903091631232671105 88641563177318723424503329)
  ·
    refine ⟨66481172382989042568377497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88641563177318723424503329 66481172382989042568377497)
    ·
      refine ⟨49860879287241781926283123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66481172382989042568377497 49860879287241781926283123)
      ·
        refine ⟨74791318930862672889424685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49860879287241781926283123 74791318930862672889424685)
        ·
          refine ⟨28046744599073502333534257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74791318930862672889424685 28046744599073502333534257)
          ·
            refine ⟨21035058449305126750150693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28046744599073502333534257 21035058449305126750150693)
            ·
              refine ⟨3944073459244711265653255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21035058449305126750150693 3944073459244711265653255)
              ·
                refine ⟨5916110188867066898479883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944073459244711265653255 5916110188867066898479883)
                ·
                  refine ⟨8874165283300600347719825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5916110188867066898479883 8874165283300600347719825)
                  ·
                    refine ⟨6655623962475450260789869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8874165283300600347719825 6655623962475450260789869)
                    ·
                      refine ⟨2495858985928293847796201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6655623962475450260789869 2495858985928293847796201)
                      ·
                        rfl

theorem cell23_4860668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_4860668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860668 prefixEnd_4860668 := by exact prefixLift 4860668
  have htrace : WordTrace (prefixWord ++ tailWord_4860668) baseStart_4860668 baseEnd_4860668 := by
    simpa [prefixWord, tailWord_4860668, baseEnd_4860668] using wordTrace_append hprefix tailTrace_4860668
  have hstable : (prefixWord ++ tailWord_4860668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860668).length < 2 ^ (prefixWord ++ tailWord_4860668).sum := by decide
  have hdescent : baseEnd_4860668 < baseStart_4860668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860697 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 1, 8]
def baseStart_4860697 : Nat := 118140960795 + 4860697 * 2 ^ 59
def prefixEnd_4860697 : Nat := 4983230072969 + 3 ^ 40 * 4860697 * 2
def baseEnd_4860697 : Nat := 831957958955758078111189

theorem tailTrace_4860697 : CollatzResearch.WordTrace tailWord_4860697 prefixEnd_4860697 831957958955758078111189 := by
  unfold tailWord_4860697
  simp only [CollatzResearch.WordTrace]
  refine ⟨177284184071532384801812345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118189456047688256534541563 177284184071532384801812345)
  ·
    refine ⟨132963138053649288601359259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177284184071532384801812345 132963138053649288601359259)
    ·
      refine ⟨199444707080473932902038889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132963138053649288601359259 199444707080473932902038889)
      ·
        refine ⟨149583530310355449676529167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199444707080473932902038889 149583530310355449676529167)
        ·
          refine ⟨224375295465533174514793751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149583530310355449676529167 224375295465533174514793751)
          ·
            refine ⟨336562943198299761772190627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224375295465533174514793751 336562943198299761772190627)
            ·
              refine ⟨504844414797449642658285941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336562943198299761772190627 504844414797449642658285941)
              ·
                refine ⟨47329163887260903999214307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 504844414797449642658285941 47329163887260903999214307)
                ·
                  refine ⟨70993745830891355998821461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47329163887260903999214307 70993745830891355998821461)
                  ·
                    refine ⟨831957958955758078111189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70993745830891355998821461 831957958955758078111189)
                    ·
                      rfl

theorem cell23_4860697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_4860697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860697 prefixEnd_4860697 := by exact prefixLift 4860697
  have htrace : WordTrace (prefixWord ++ tailWord_4860697) baseStart_4860697 baseEnd_4860697 := by
    simpa [prefixWord, tailWord_4860697, baseEnd_4860697] using wordTrace_append hprefix tailTrace_4860697
  have hstable : (prefixWord ++ tailWord_4860697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860697).length < 2 ^ (prefixWord ++ tailWord_4860697).sum := by decide
  have hdescent : baseEnd_4860697 < baseStart_4860697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860721 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 3, 4, 2]
def baseStart_4860721 : Nat := 118140960795 + 4860721 * 2 ^ 59
def prefixEnd_4860721 : Nat := 4983230072969 + 3 ^ 40 * 4860721 * 2
def baseEnd_4860721 : Nat := 2495886200402982140433457

theorem tailTrace_4860721 : CollatzResearch.WordTrace tailWord_4860721 prefixEnd_4860721 2495886200402982140433457 := by
  unfold tailWord_4860721
  simp only [CollatzResearch.WordTrace]
  refine ⟨177285059423445436900686017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118190039615630291267124011 177285059423445436900686017)
  ·
    refine ⟨132963794567584077675514513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177285059423445436900686017 132963794567584077675514513)
    ·
      refine ⟨99722845925688058256635885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132963794567584077675514513 99722845925688058256635885)
      ·
        refine ⟨37396067222133021846238457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99722845925688058256635885 37396067222133021846238457)
        ·
          refine ⟨28047050416599766384678843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37396067222133021846238457 28047050416599766384678843)
          ·
            refine ⟨42070575624899649577018265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28047050416599766384678843 42070575624899649577018265)
            ·
              refine ⟨31552931718674737182763699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42070575624899649577018265 31552931718674737182763699)
              ·
                refine ⟨47329397578012105774145549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31552931718674737182763699 47329397578012105774145549)
                ·
                  refine ⟨17748524091754539665304581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47329397578012105774145549 17748524091754539665304581)
                  ·
                    refine ⟨3327848267203976187244609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17748524091754539665304581 3327848267203976187244609)
                    ·
                      refine ⟨2495886200402982140433457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327848267203976187244609 2495886200402982140433457)
                      ·
                        rfl

theorem cell23_4860721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_4860721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860721 prefixEnd_4860721 := by exact prefixLift 4860721
  have htrace : WordTrace (prefixWord ++ tailWord_4860721) baseStart_4860721 baseEnd_4860721 := by
    simpa [prefixWord, tailWord_4860721, baseEnd_4860721] using wordTrace_append hprefix tailTrace_4860721
  have hstable : (prefixWord ++ tailWord_4860721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860721).length < 2 ^ (prefixWord ++ tailWord_4860721).sum := by decide
  have hdescent : baseEnd_4860721 < baseStart_4860721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860749 : List Nat := [1, 6, 1, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_4860749 : Nat := 118140960795 + 4860749 * 2 ^ 59
def prefixEnd_4860749 : Nat := 4983230072969 + 3 ^ 40 * 4860749 * 2
def baseEnd_4860749 : Nat := 2495900577861308030883329

theorem tailTrace_4860749 : CollatzResearch.WordTrace tailWord_4860749 prefixEnd_4860749 2495900577861308030883329 := by
  unfold tailWord_4860749
  simp only [CollatzResearch.WordTrace]
  refine ⟨177286080667343997682705301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118190720444895998455136867 177286080667343997682705301)
  ·
    refine ⟨8310285031281749891376811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 177286080667343997682705301 8310285031281749891376811)
    ·
      refine ⟨12465427546922624837065217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8310285031281749891376811 12465427546922624837065217)
      ·
        refine ⟨9349070660191968627798913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12465427546922624837065217 9349070660191968627798913)
        ·
          refine ⟨7011802995143976470849185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9349070660191968627798913 7011802995143976470849185)
          ·
            refine ⟨5258852246357982353136889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7011802995143976470849185 5258852246357982353136889)
            ·
              refine ⟨3944139184768486764852667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5258852246357982353136889 3944139184768486764852667)
              ·
                refine ⟨5916208777152730147279001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944139184768486764852667 5916208777152730147279001)
                ·
                  refine ⟨4437156582864547610459251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5916208777152730147279001 4437156582864547610459251)
                  ·
                    refine ⟨6655734874296821415688877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4437156582864547610459251 6655734874296821415688877)
                    ·
                      refine ⟨2495900577861308030883329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6655734874296821415688877 2495900577861308030883329)
                      ·
                        rfl

theorem cell23_4860749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_4860749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860749 prefixEnd_4860749 := by exact prefixLift 4860749
  have htrace : WordTrace (prefixWord ++ tailWord_4860749) baseStart_4860749 baseEnd_4860749 := by
    simpa [prefixWord, tailWord_4860749, baseEnd_4860749] using wordTrace_append hprefix tailTrace_4860749
  have hstable : (prefixWord ++ tailWord_4860749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860749).length < 2 ^ (prefixWord ++ tailWord_4860749).sum := by decide
  have hdescent : baseEnd_4860749 < baseStart_4860749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860784 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 5]
def baseStart_4860784 : Nat := 118140960795 + 4860784 * 2 ^ 59
def prefixEnd_4860784 : Nat := 4983230072969 + 3 ^ 40 * 4860784 * 2
def baseEnd_4860784 : Nat := 2495918549684215393945667

theorem tailTrace_4860784 : CollatzResearch.WordTrace tailWord_4860784 prefixEnd_4860784 2495918549684215393945667 := by
  unfold tailWord_4860784
  simp only [CollatzResearch.WordTrace]
  refine ⟨88643678611108599330114703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118191571481478132440152937 88643678611108599330114703)
  ·
    refine ⟨132965517916662898995172055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88643678611108599330114703 132965517916662898995172055)
    ·
      refine ⟨199448276874994348492758083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132965517916662898995172055 199448276874994348492758083)
      ·
        refine ⟨299172415312491522739137125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199448276874994348492758083 299172415312491522739137125)
        ·
          refine ⟨56094827871092160513588211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 299172415312491522739137125 56094827871092160513588211)
          ·
            refine ⟨84142241806638240770382317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56094827871092160513588211 84142241806638240770382317)
            ·
              refine ⟨31553340677489340288893369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84142241806638240770382317 31553340677489340288893369)
              ·
                refine ⟨23665005508117005216670027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31553340677489340288893369 23665005508117005216670027)
                ·
                  refine ⟨35497508262175507825005041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23665005508117005216670027 35497508262175507825005041)
                  ·
                    refine ⟨26623131196631630868753781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35497508262175507825005041 26623131196631630868753781)
                    ·
                      refine ⟨2495918549684215393945667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26623131196631630868753781 2495918549684215393945667)
                      ·
                        rfl

theorem cell23_4860784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_4860784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860784 prefixEnd_4860784 := by exact prefixLift 4860784
  have htrace : WordTrace (prefixWord ++ tailWord_4860784) baseStart_4860784 baseEnd_4860784 := by
    simpa [prefixWord, tailWord_4860784, baseEnd_4860784] using wordTrace_append hprefix tailTrace_4860784
  have hstable : (prefixWord ++ tailWord_4860784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860784).length < 2 ^ (prefixWord ++ tailWord_4860784).sum := by decide
  have hdescent : baseEnd_4860784 < baseStart_4860784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860794 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_4860794 : Nat := 118140960795 + 4860794 * 2 ^ 59
def prefixEnd_4860794 : Nat := 4983230072969 + 3 ^ 40 * 4860794 * 2
def baseEnd_4860794 : Nat := 2495923684490760354820621

theorem tailTrace_4860794 : CollatzResearch.WordTrace tailWord_4860794 prefixEnd_4860794 2495923684490760354820621 := by
  unfold tailWord_4860794
  simp only [CollatzResearch.WordTrace]
  refine ⟨44321930488045242592023359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118191814634787313578728957 44321930488045242592023359)
  ·
    refine ⟨66482895732067863888035039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44321930488045242592023359 66482895732067863888035039)
    ·
      refine ⟨99724343598101795832052559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66482895732067863888035039 99724343598101795832052559)
      ·
        refine ⟨149586515397152693748078839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99724343598101795832052559 149586515397152693748078839)
        ·
          refine ⟨224379773095729040622118259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149586515397152693748078839 224379773095729040622118259)
          ·
            refine ⟨336569659643593560933177389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224379773095729040622118259 336569659643593560933177389)
            ·
              refine ⟨126213622366347585349941521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 336569659643593560933177389 126213622366347585349941521)
              ·
                refine ⟨94660216774760689012456141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126213622366347585349941521 94660216774760689012456141)
                ·
                  refine ⟨35497581290535258379671053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94660216774760689012456141 35497581290535258379671053)
                  ·
                    refine ⟨13311592983950721892376645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35497581290535258379671053 13311592983950721892376645)
                    ·
                      refine ⟨2495923684490760354820621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13311592983950721892376645 2495923684490760354820621)
                      ·
                        rfl

theorem cell23_4860794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_4860794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860794 prefixEnd_4860794 := by exact prefixLift 4860794
  have htrace : WordTrace (prefixWord ++ tailWord_4860794) baseStart_4860794 baseEnd_4860794 := by
    simpa [prefixWord, tailWord_4860794, baseEnd_4860794] using wordTrace_append hprefix tailTrace_4860794
  have hstable : (prefixWord ++ tailWord_4860794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860794).length < 2 ^ (prefixWord ++ tailWord_4860794).sum := by decide
  have hdescent : baseEnd_4860794 < baseStart_4860794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860804 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_4860804 : Nat := 118140960795 + 4860804 * 2 ^ 59
def prefixEnd_4860804 : Nat := 4983230072969 + 3 ^ 40 * 4860804 * 2
def baseEnd_4860804 : Nat := 831976273099101771898525

theorem tailTrace_4860804 : CollatzResearch.WordTrace tailWord_4860804 prefixEnd_4860804 831976273099101771898525 := by
  unfold tailWord_4860804
  simp only [CollatzResearch.WordTrace]
  refine ⟨88644043341072371037978733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118192057788096494717304977 88644043341072371037978733)
  ·
    refine ⟨33241516252902139139242025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88644043341072371037978733 33241516252902139139242025)
    ·
      refine ⟨24931137189676604354431519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33241516252902139139242025 24931137189676604354431519)
      ·
        refine ⟨37396705784514906531647279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24931137189676604354431519 37396705784514906531647279)
        ·
          refine ⟨56095058676772359797470919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37396705784514906531647279 56095058676772359797470919)
          ·
            refine ⟨84142588015158539696206379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56095058676772359797470919 84142588015158539696206379)
            ·
              refine ⟨126213882022737809544309569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84142588015158539696206379 126213882022737809544309569)
              ·
                refine ⟨94660411517053357158232177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126213882022737809544309569 94660411517053357158232177)
                ·
                  refine ⟨70995308637790017868674133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94660411517053357158232177 70995308637790017868674133)
                  ·
                    refine ⟨831976273099101771898525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70995308637790017868674133 831976273099101771898525)
                    ·
                      rfl

theorem cell23_4860804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_4860804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860804 prefixEnd_4860804 := by exact prefixLift 4860804
  have htrace : WordTrace (prefixWord ++ tailWord_4860804) baseStart_4860804 baseEnd_4860804 := by
    simpa [prefixWord, tailWord_4860804, baseEnd_4860804] using wordTrace_append hprefix tailTrace_4860804
  have hstable : (prefixWord ++ tailWord_4860804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860804).length < 2 ^ (prefixWord ++ tailWord_4860804).sum := by decide
  have hdescent : baseEnd_4860804 < baseStart_4860804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860811 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 1, 6, 2]
def baseStart_4860811 : Nat := 118140960795 + 4860811 * 2 ^ 59
def prefixEnd_4860811 : Nat := 4983230072969 + 3 ^ 40 * 4860811 * 2
def baseEnd_4860811 : Nat := 2495932413661886788308043

theorem tailTrace_4860811 : CollatzResearch.WordTrace tailWord_4860811 prefixEnd_4860811 2495932413661886788308043 := by
  unfold tailWord_4860811
  simp only [CollatzResearch.WordTrace]
  refine ⟨177288341993119382271462287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118192227995412921514308191 177288341993119382271462287)
  ·
    refine ⟨265932512989679073407193431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177288341993119382271462287 265932512989679073407193431)
    ·
      refine ⟨398898769484518610110790147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265932512989679073407193431 398898769484518610110790147)
      ·
        refine ⟨598348154226777915166185221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398898769484518610110790147 598348154226777915166185221)
        ·
          refine ⟨112190278917520859093659729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 598348154226777915166185221 112190278917520859093659729)
          ·
            refine ⟨84142709188140644320244797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112190278917520859093659729 84142709188140644320244797)
            ·
              refine ⟨31553515945552741620091799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84142709188140644320244797 31553515945552741620091799)
              ·
                refine ⟨47330273918329112430137699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31553515945552741620091799 47330273918329112430137699)
                ·
                  refine ⟨70995410877493668645206549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47330273918329112430137699 70995410877493668645206549)
                  ·
                    refine ⟨3327909884882515717744057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70995410877493668645206549 3327909884882515717744057)
                    ·
                      refine ⟨2495932413661886788308043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327909884882515717744057 2495932413661886788308043)
                      ·
                        rfl

theorem cell23_4860811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 6, 2].length) (baseStart_4860811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860811 prefixEnd_4860811 := by exact prefixLift 4860811
  have htrace : WordTrace (prefixWord ++ tailWord_4860811) baseStart_4860811 baseEnd_4860811 := by
    simpa [prefixWord, tailWord_4860811, baseEnd_4860811] using wordTrace_append hprefix tailTrace_4860811
  have hstable : (prefixWord ++ tailWord_4860811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860811).length < 2 ^ (prefixWord ++ tailWord_4860811).sum := by decide
  have hdescent : baseEnd_4860811 < baseStart_4860811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860821 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 5, 4]
def baseStart_4860821 : Nat := 118140960795 + 4860821 * 2 ^ 59
def prefixEnd_4860821 : Nat := 4983230072969 + 3 ^ 40 * 4860821 * 2
def baseEnd_4860821 : Nat := 831979182822810583060999

theorem tailTrace_4860821 : CollatzResearch.WordTrace tailWord_4860821 prefixEnd_4860821 831979182822810583060999 := by
  unfold tailWord_4860821
  simp only [CollatzResearch.WordTrace]
  refine ⟨177288706723083153979326317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118192471148722102652884211 177288706723083153979326317)
  ·
    refine ⟨66483265021156182742247369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177288706723083153979326317 66483265021156182742247369)
    ·
      refine ⟨49862448765867137056685527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66483265021156182742247369 49862448765867137056685527)
      ·
        refine ⟨74793673148800705585028291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49862448765867137056685527 74793673148800705585028291)
        ·
          refine ⟨112190509723201058377542437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74793673148800705585028291 112190509723201058377542437)
          ·
            refine ⟨21035720573100198445789207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112190509723201058377542437 21035720573100198445789207)
            ·
              refine ⟨31553580859650297668683811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21035720573100198445789207 31553580859650297668683811)
              ·
                refine ⟨47330371289475446503025717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31553580859650297668683811 47330371289475446503025717)
                ·
                  refine ⟨4437222308388323109658661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47330371289475446503025717 4437222308388323109658661)
                  ·
                    refine ⟨831979182822810583060999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4437222308388323109658661 831979182822810583060999)
                    ·
                      rfl

theorem cell23_4860821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_4860821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860821 prefixEnd_4860821 := by exact prefixLift 4860821
  have htrace : WordTrace (prefixWord ++ tailWord_4860821) baseStart_4860821 baseEnd_4860821 := by
    simpa [prefixWord, tailWord_4860821, baseEnd_4860821] using wordTrace_append hprefix tailTrace_4860821
  have hstable : (prefixWord ++ tailWord_4860821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860821).length < 2 ^ (prefixWord ++ tailWord_4860821).sum := by decide
  have hdescent : baseEnd_4860821 < baseStart_4860821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860828 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4860828 : Nat := 118140960795 + 4860828 * 2 ^ 59
def prefixEnd_4860828 : Nat := 4983230072969 + 3 ^ 40 * 4860828 * 2
def baseEnd_4860828 : Nat := 2495941142833013221795465

theorem tailTrace_4860828 : CollatzResearch.WordTrace tailWord_4860828 prefixEnd_4860828 2495941142833013221795465 := by
  unfold tailWord_4860828
  simp only [CollatzResearch.WordTrace]
  refine ⟨88644481017028897087415569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118192641356038529449887425 88644481017028897087415569)
  ·
    refine ⟨66483360762771672815561677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88644481017028897087415569 66483360762771672815561677)
    ·
      refine ⟨24931260286039377305835629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66483360762771672815561677 24931260286039377305835629)
      ·
        refine ⟨9349222607264766489688361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24931260286039377305835629 9349222607264766489688361)
        ·
          refine ⟨7011916955448574867266271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9349222607264766489688361 7011916955448574867266271)
          ·
            refine ⟨10517875433172862300899407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7011916955448574867266271 10517875433172862300899407)
            ·
              refine ⟨15776813149759293451349111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10517875433172862300899407 15776813149759293451349111)
              ·
                refine ⟨23665219724638940177023667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15776813149759293451349111 23665219724638940177023667)
                ·
                  refine ⟨35497829586958410265535501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23665219724638940177023667 35497829586958410265535501)
                  ·
                    refine ⟨13311686095109403849575813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35497829586958410265535501 13311686095109403849575813)
                    ·
                      refine ⟨2495941142833013221795465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13311686095109403849575813 2495941142833013221795465)
                      ·
                        rfl

theorem cell23_4860828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4860828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860828 prefixEnd_4860828 := by exact prefixLift 4860828
  have htrace : WordTrace (prefixWord ++ tailWord_4860828) baseStart_4860828 baseEnd_4860828 := by
    simpa [prefixWord, tailWord_4860828, baseEnd_4860828] using wordTrace_append hprefix tailTrace_4860828
  have hstable : (prefixWord ++ tailWord_4860828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860828).length < 2 ^ (prefixWord ++ tailWord_4860828).sum := by decide
  have hdescent : baseEnd_4860828 < baseStart_4860828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860888 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 1, 5, 2]
def baseStart_4860888 : Nat := 118140960795 + 4860888 * 2 ^ 59
def prefixEnd_4860888 : Nat := 4983230072969 + 3 ^ 40 * 4860888 * 2
def baseEnd_4860888 : Nat := 2495971951672282987045189

theorem tailTrace_4860888 : CollatzResearch.WordTrace tailWord_4860888 prefixEnd_4860888 2495971951672282987045189 := by
  unfold tailWord_4860888
  simp only [CollatzResearch.WordTrace]
  refine ⟨88645575206920212211007659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118194100275893616281343545 88645575206920212211007659)
  ·
    refine ⟨132968362810380318316511489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88645575206920212211007659 132968362810380318316511489)
    ·
      refine ⟨99726272107785238737383617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132968362810380318316511489 99726272107785238737383617)
      ·
        refine ⟨74794704080838929053037713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99726272107785238737383617 74794704080838929053037713)
        ·
          refine ⟨56096028060629196789778285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74794704080838929053037713 56096028060629196789778285)
          ·
            refine ⟨21036010522735948796166857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56096028060629196789778285 21036010522735948796166857)
            ·
              refine ⟨15777007892051961597125143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21036010522735948796166857 15777007892051961597125143)
              ·
                refine ⟨23665511838077942395687715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15777007892051961597125143 23665511838077942395687715)
                ·
                  refine ⟨35498267757116913593531573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23665511838077942395687715 35498267757116913593531573)
                  ·
                    refine ⟨3327962602229710649393585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35498267757116913593531573 3327962602229710649393585)
                    ·
                      refine ⟨2495971951672282987045189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327962602229710649393585 2495971951672282987045189)
                      ·
                        rfl

theorem cell23_4860888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_4860888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860888 prefixEnd_4860888 := by exact prefixLift 4860888
  have htrace : WordTrace (prefixWord ++ tailWord_4860888) baseStart_4860888 baseEnd_4860888 := by
    simpa [prefixWord, tailWord_4860888, baseEnd_4860888] using wordTrace_append hprefix tailTrace_4860888
  have hstable : (prefixWord ++ tailWord_4860888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860888).length < 2 ^ (prefixWord ++ tailWord_4860888).sum := by decide
  have hdescent : baseEnd_4860888 < baseStart_4860888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860921 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 5]
def baseStart_4860921 : Nat := 118140960795 + 4860921 * 2 ^ 59
def prefixEnd_4860921 : Nat := 4983230072969 + 3 ^ 40 * 4860921 * 2
def baseEnd_4860921 : Nat := 2495988896533881357932537

theorem tailTrace_4860921 : CollatzResearch.WordTrace tailWord_4860921 prefixEnd_4860921 2495988896533881357932537 := by
  unfold tailWord_4860921
  simp only [CollatzResearch.WordTrace]
  refine ⟨177292354022720871057966617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118194902681813914038644411 177292354022720871057966617)
  ·
    refine ⟨132969265517040653293474963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177292354022720871057966617 132969265517040653293474963)
    ·
      refine ⟨199453898275560979940212445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132969265517040653293474963 199453898275560979940212445)
      ·
        refine ⟨74795211853335367477579667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199453898275560979940212445 74795211853335367477579667)
        ·
          refine ⟨112192817780003051216369501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74795211853335367477579667 112192817780003051216369501)
          ·
            refine ⟨42072306667501144206138563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112192817780003051216369501 42072306667501144206138563)
            ·
              refine ⟨63108460001251716309207845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42072306667501144206138563 63108460001251716309207845)
              ·
                refine ⟨11832836250234696807976471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63108460001251716309207845 11832836250234696807976471)
                ·
                  refine ⟨17749254375352045211964707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11832836250234696807976471 17749254375352045211964707)
                  ·
                    refine ⟨26623881563028067817947061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17749254375352045211964707 26623881563028067817947061)
                    ·
                      refine ⟨2495988896533881357932537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26623881563028067817947061 2495988896533881357932537)
                      ·
                        rfl

theorem cell23_4860921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_4860921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860921 prefixEnd_4860921 := by exact prefixLift 4860921
  have htrace : WordTrace (prefixWord ++ tailWord_4860921) baseStart_4860921 baseEnd_4860921 := by
    simpa [prefixWord, tailWord_4860921, baseEnd_4860921] using wordTrace_append hprefix tailTrace_4860921
  have hstable : (prefixWord ++ tailWord_4860921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860921).length < 2 ^ (prefixWord ++ tailWord_4860921).sum := by decide
  have hdescent : baseEnd_4860921 < baseStart_4860921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860935 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 5, 2, 2]
def baseStart_4860935 : Nat := 118140960795 + 4860935 * 2 ^ 59
def prefixEnd_4860935 : Nat := 4983230072969 + 3 ^ 40 * 4860935 * 2
def baseEnd_4860935 : Nat := 2495996085263044303157473

theorem tailTrace_4860935 : CollatzResearch.WordTrace tailWord_4860935 prefixEnd_4860935 2495996085263044303157473 := by
  unfold tailWord_4860935
  simp only [CollatzResearch.WordTrace]
  refine ⟨177292864644670151448976259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118195243096446767632650839 177292864644670151448976259)
  ·
    refine ⟨265939296967005227173464389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177292864644670151448976259 265939296967005227173464389)
    ·
      refine ⟨49863618181313480095024573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265939296967005227173464389 49863618181313480095024573)
      ·
        refine ⟨18698856817992555035634215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49863618181313480095024573 18698856817992555035634215)
        ·
          refine ⟨28048285226988832553451323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18698856817992555035634215 28048285226988832553451323)
          ·
            refine ⟨42072427840483248830176985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28048285226988832553451323 42072427840483248830176985)
            ·
              refine ⟨31554320880362436622632739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42072427840483248830176985 31554320880362436622632739)
              ·
                refine ⟨47331481320543654933949109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31554320880362436622632739 47331481320543654933949109)
                ·
                  refine ⟨4437326373800967650057729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47331481320543654933949109 4437326373800967650057729)
                  ·
                    refine ⟨3327994780350725737543297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4437326373800967650057729 3327994780350725737543297)
                    ·
                      refine ⟨2495996085263044303157473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3327994780350725737543297 2495996085263044303157473)
                      ·
                        rfl

theorem cell23_4860935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_4860935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860935 prefixEnd_4860935 := by exact prefixLift 4860935
  have htrace : WordTrace (prefixWord ++ tailWord_4860935) baseStart_4860935 baseEnd_4860935 := by
    simpa [prefixWord, tailWord_4860935, baseEnd_4860935] using wordTrace_append hprefix tailTrace_4860935
  have hstable : (prefixWord ++ tailWord_4860935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860935).length < 2 ^ (prefixWord ++ tailWord_4860935).sum := by decide
  have hdescent : baseEnd_4860935 < baseStart_4860935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860981 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_4860981 : Nat := 118140960795 + 4860981 * 2 ^ 59
def prefixEnd_4860981 : Nat := 4983230072969 + 3 ^ 40 * 4860981 * 2
def baseEnd_4860981 : Nat := 2496019705373151123182261

theorem tailTrace_4860981 : CollatzResearch.WordTrace tailWord_4860981 prefixEnd_4860981 2496019705373151123182261 := by
  unfold tailWord_4860981
  simp only [CollatzResearch.WordTrace]
  refine ⟨177294542402503501305150797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118196361601669000870100531 177294542402503501305150797)
  ·
    refine ⟨66485453400938812989431549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177294542402503501305150797 66485453400938812989431549)
    ·
      refine ⟨24932045025352054871036831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66485453400938812989431549 24932045025352054871036831)
      ·
        refine ⟨37398067538028082306555247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24932045025352054871036831 37398067538028082306555247)
        ·
          refine ⟨56097101307042123459832871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37398067538028082306555247 56097101307042123459832871)
          ·
            refine ⟨84145651960563185189749307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56097101307042123459832871 84145651960563185189749307)
            ·
              refine ⟨126218477940844777784623961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84145651960563185189749307 126218477940844777784623961)
              ·
                refine ⟨94663858455633583338467971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126218477940844777784623961 94663858455633583338467971)
                ·
                  refine ⟨141995787683450375007701957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94663858455633583338467971 141995787683450375007701957)
                  ·
                    refine ⟨26624210190646945313944117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 141995787683450375007701957 26624210190646945313944117)
                    ·
                      refine ⟨2496019705373151123182261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26624210190646945313944117 2496019705373151123182261)
                      ·
                        rfl

theorem cell23_4860981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_4860981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860981 prefixEnd_4860981 := by exact prefixLift 4860981
  have htrace : WordTrace (prefixWord ++ tailWord_4860981) baseStart_4860981 baseEnd_4860981 := by
    simpa [prefixWord, tailWord_4860981, baseEnd_4860981] using wordTrace_append hprefix tailTrace_4860981
  have hstable : (prefixWord ++ tailWord_4860981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860981).length < 2 ^ (prefixWord ++ tailWord_4860981).sum := by decide
  have hdescent : baseEnd_4860981 < baseStart_4860981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860985 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 1, 3, 3]
def baseStart_4860985 : Nat := 118140960795 + 4860985 * 2 ^ 59
def prefixEnd_4860985 : Nat := 4983230072969 + 3 ^ 40 * 4860985 * 2
def baseEnd_4860985 : Nat := 2496021759295769107532243

theorem tailTrace_4860985 : CollatzResearch.WordTrace tailWord_4860985 prefixEnd_4860985 2496021759295769107532243 := by
  unfold tailWord_4860985
  simp only [CollatzResearch.WordTrace]
  refine ⟨177294688294489009988296409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118196458862992673325530939 177294688294489009988296409)
  ·
    refine ⟨132971016220866757491222307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177294688294489009988296409 132971016220866757491222307)
    ·
      refine ⟨199456524331300136236833461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132971016220866757491222307 199456524331300136236833461)
      ·
        refine ⟨18699049156059387772203137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 199456524331300136236833461 18699049156059387772203137)
        ·
          refine ⟨14024286867044540829152353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18699049156059387772203137 14024286867044540829152353)
          ·
            refine ⟨10518215150283405621864265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14024286867044540829152353 10518215150283405621864265)
            ·
              refine ⟨7888661362712554216398199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10518215150283405621864265 7888661362712554216398199)
              ·
                refine ⟨11832992044068831324597299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7888661362712554216398199 11832992044068831324597299)
                ·
                  refine ⟨17749488066103246986895949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11832992044068831324597299 17749488066103246986895949)
                  ·
                    refine ⟨6656058024788717620085981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17749488066103246986895949 6656058024788717620085981)
                    ·
                      refine ⟨2496021759295769107532243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6656058024788717620085981 2496021759295769107532243)
                      ·
                        rfl

theorem cell23_4860985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_4860985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860985 prefixEnd_4860985 := by exact prefixLift 4860985
  have htrace : WordTrace (prefixWord ++ tailWord_4860985) baseStart_4860985 baseEnd_4860985 := by
    simpa [prefixWord, tailWord_4860985, baseEnd_4860985] using wordTrace_append hprefix tailTrace_4860985
  have hstable : (prefixWord ++ tailWord_4860985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860985).length < 2 ^ (prefixWord ++ tailWord_4860985).sum := by decide
  have hdescent : baseEnd_4860985 < baseStart_4860985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860991 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 4]
def baseStart_4860991 : Nat := 118140960795 + 4860991 * 2 ^ 59
def prefixEnd_4860991 : Nat := 4983230072969 + 3 ^ 40 * 4860991 * 2
def baseEnd_4860991 : Nat := 2496024840179696084057215

theorem tailTrace_4860991 : CollatzResearch.WordTrace tailWord_4860991 prefixEnd_4860991 2496024840179696084057215 := by
  unfold tailWord_4860991
  simp only [CollatzResearch.WordTrace]
  refine ⟨177294907132467273013014827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118196604754978182008676551 177294907132467273013014827)
  ·
    refine ⟨265942360698700909519522241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177294907132467273013014827 265942360698700909519522241)
    ·
      refine ⟨199456770524025682139641681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265942360698700909519522241 199456770524025682139641681)
      ·
        refine ⟨149592577893019261604731261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199456770524025682139641681 149592577893019261604731261)
        ·
          refine ⟨56097216709882223101774223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149592577893019261604731261 56097216709882223101774223)
          ·
            refine ⟨84145825064823334652661335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56097216709882223101774223 84145825064823334652661335)
            ·
              refine ⟨126218737597235001978992003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84145825064823334652661335 126218737597235001978992003)
              ·
                refine ⟨189328106395852502968488005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126218737597235001978992003 189328106395852502968488005)
                ·
                  refine ⟨35499019949222344306591501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189328106395852502968488005 35499019949222344306591501)
                  ·
                    refine ⟨13312132480958379114971813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35499019949222344306591501 13312132480958379114971813)
                    ·
                      refine ⟨2496024840179696084057215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13312132480958379114971813 2496024840179696084057215)
                      ·
                        rfl

theorem cell23_4860991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_4860991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860991 prefixEnd_4860991 := by exact prefixLift 4860991
  have htrace : WordTrace (prefixWord ++ tailWord_4860991) baseStart_4860991 baseEnd_4860991 := by
    simpa [prefixWord, tailWord_4860991, baseEnd_4860991] using wordTrace_append hprefix tailTrace_4860991
  have hstable : (prefixWord ++ tailWord_4860991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860991).length < 2 ^ (prefixWord ++ tailWord_4860991).sum := by decide
  have hdescent : baseEnd_4860991 < baseStart_4860991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4860995 : List Nat := [1, 1, 1, 3, 1, 2, 4, 4, 1, 3, 2]
def baseStart_4860995 : Nat := 118140960795 + 4860995 * 2 ^ 59
def prefixEnd_4860995 : Nat := 4983230072969 + 3 ^ 40 * 4860995 * 2
def baseEnd_4860995 : Nat := 2496026894102314068407197

theorem tailTrace_4860995 : CollatzResearch.WordTrace tailWord_4860995 prefixEnd_4860995 2496026894102314068407197 := by
  unfold tailWord_4860995
  simp only [CollatzResearch.WordTrace]
  refine ⟨177295053024452781696160439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118196702016301854464106959 177295053024452781696160439)
  ·
    refine ⟨265942579536679172544240659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177295053024452781696160439 265942579536679172544240659)
    ·
      refine ⟨398913869305018758816360989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265942579536679172544240659 398913869305018758816360989)
      ·
        refine ⟨149592700989382034556135371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 398913869305018758816360989 149592700989382034556135371)
        ·
          refine ⟨224389051484073051834203057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149592700989382034556135371 224389051484073051834203057)
          ·
            refine ⟨168291788613054788875652293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224389051484073051834203057 168291788613054788875652293)
            ·
              refine ⟨31554710364947772914184805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168291788613054788875652293 31554710364947772914184805)
              ·
                refine ⟨5916508193427707421409651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31554710364947772914184805 5916508193427707421409651)
                ·
                  refine ⟨8874762290141561132114477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5916508193427707421409651 8874762290141561132114477)
                  ·
                    refine ⟨3328035858803085424542929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8874762290141561132114477 3328035858803085424542929)
                    ·
                      refine ⟨2496026894102314068407197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328035858803085424542929 2496026894102314068407197)
                      ·
                        rfl

theorem cell23_4860995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 3, 2].length) (baseStart_4860995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4860995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4860995 prefixEnd_4860995 := by exact prefixLift 4860995
  have htrace : WordTrace (prefixWord ++ tailWord_4860995) baseStart_4860995 baseEnd_4860995 := by
    simpa [prefixWord, tailWord_4860995, baseEnd_4860995] using wordTrace_append hprefix tailTrace_4860995
  have hstable : (prefixWord ++ tailWord_4860995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4860995).length < 2 ^ (prefixWord ++ tailWord_4860995).sum := by decide
  have hdescent : baseEnd_4860995 < baseStart_4860995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4860995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861065 : List Nat := [1, 2, 1, 1, 4, 3, 3, 3, 5]
def baseStart_4861065 : Nat := 118140960795 + 4861065 * 2 ^ 59
def prefixEnd_4861065 : Nat := 4983230072969 + 3 ^ 40 * 4861065 * 2
def baseEnd_4861065 : Nat := 277340315305347643836875

theorem tailTrace_4861065 : CollatzResearch.WordTrace tailWord_4861065 prefixEnd_4861065 277340315305347643836875 := by
  unfold tailWord_4861065
  simp only [CollatzResearch.WordTrace]
  refine ⟨177297606134199183651208649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118198404089466122434139099 177297606134199183651208649)
  ·
    refine ⟨132973204600649387738406487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177297606134199183651208649 132973204600649387738406487)
    ·
      refine ⟨199459806900974081607609731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132973204600649387738406487 199459806900974081607609731)
      ·
        refine ⟨299189710351461122411414597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199459806900974081607609731 299189710351461122411414597)
        ·
          refine ⟨56098070690898960452140237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 299189710351461122411414597 56098070690898960452140237)
          ·
            refine ⟨21036776509087110169552589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56098070690898960452140237 21036776509087110169552589)
            ·
              refine ⟨7888791190907666313582221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21036776509087110169552589 7888791190907666313582221)
              ·
                refine ⟨2958296696590374867593333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7888791190907666313582221 2958296696590374867593333)
                ·
                  refine ⟨277340315305347643836875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2958296696590374867593333 277340315305347643836875)
                  ·
                    rfl

theorem cell23_4861065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 5].length) (baseStart_4861065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861065 prefixEnd_4861065 := by exact prefixLift 4861065
  have htrace : WordTrace (prefixWord ++ tailWord_4861065) baseStart_4861065 baseEnd_4861065 := by
    simpa [prefixWord, tailWord_4861065, baseEnd_4861065] using wordTrace_append hprefix tailTrace_4861065
  have hstable : (prefixWord ++ tailWord_4861065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861065).length < 2 ^ (prefixWord ++ tailWord_4861065).sum := by decide
  have hdescent : baseEnd_4861065 < baseStart_4861065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861071 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 5]
def baseStart_4861071 : Nat := 118140960795 + 4861071 * 2 ^ 59
def prefixEnd_4861071 : Nat := 4983230072969 + 3 ^ 40 * 4861071 * 2
def baseEnd_4861071 : Nat := 2496065918632055771056847

theorem tailTrace_4861071 : CollatzResearch.WordTrace tailWord_4861071 prefixEnd_4861071 2496065918632055771056847 := by
  unfold tailWord_4861071
  simp only [CollatzResearch.WordTrace]
  refine ⟨177297824972177446675927067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118198549981451631117284711 177297824972177446675927067)
  ·
    refine ⟨265946737458266170013890601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177297824972177446675927067 265946737458266170013890601)
    ·
      refine ⟨199460053093699627510417951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265946737458266170013890601 199460053093699627510417951)
      ·
        refine ⟨299190079640549441265626927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199460053093699627510417951 299190079640549441265626927)
        ·
          refine ⟨448785119460824161898440391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299190079640549441265626927 448785119460824161898440391)
          ·
            refine ⟨673177679191236242847660587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448785119460824161898440391 673177679191236242847660587)
            ·
              refine ⟨1009766518786854364271490881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673177679191236242847660587 1009766518786854364271490881)
              ·
                refine ⟨757324889090140773203618161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1009766518786854364271490881 757324889090140773203618161)
                ·
                  refine ⟨567993666817605579902713621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 757324889090140773203618161 567993666817605579902713621)
                  ·
                    refine ⟨26624703132075261557939701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 567993666817605579902713621 26624703132075261557939701)
                    ·
                      refine ⟨2496065918632055771056847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26624703132075261557939701 2496065918632055771056847)
                      ·
                        rfl

theorem cell23_4861071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_4861071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861071 prefixEnd_4861071 := by exact prefixLift 4861071
  have htrace : WordTrace (prefixWord ++ tailWord_4861071) baseStart_4861071 baseEnd_4861071 := by
    simpa [prefixWord, tailWord_4861071, baseEnd_4861071] using wordTrace_append hprefix tailTrace_4861071
  have hstable : (prefixWord ++ tailWord_4861071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861071).length < 2 ^ (prefixWord ++ tailWord_4861071).sum := by decide
  have hdescent : baseEnd_4861071 < baseStart_4861071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861081 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 8]
def baseStart_4861081 : Nat := 118140960795 + 4861081 * 2 ^ 59
def prefixEnd_4861081 : Nat := 4983230072969 + 3 ^ 40 * 4861081 * 2
def baseEnd_4861081 : Nat := 2496071053438600731931801

theorem tailTrace_4861081 : CollatzResearch.WordTrace tailWord_4861081 prefixEnd_4861081 2496071053438600731931801 := by
  unfold tailWord_4861081
  simp only [CollatzResearch.WordTrace]
  refine ⟨177298189702141218383791097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118198793134760812255860731 177298189702141218383791097)
  ·
    refine ⟨132973642276605913787843323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177298189702141218383791097 132973642276605913787843323)
    ·
      refine ⟨199460463414908870681764985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132973642276605913787843323 199460463414908870681764985)
      ·
        refine ⟨149595347561181653011323739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199460463414908870681764985 149595347561181653011323739)
        ·
          refine ⟨224393021341772479516985609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149595347561181653011323739 224393021341772479516985609)
          ·
            refine ⟨168294766006329359637739207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224393021341772479516985609 168294766006329359637739207)
            ·
              refine ⟨252442149009494039456608811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168294766006329359637739207 252442149009494039456608811)
              ·
                refine ⟨378663223514241059184913217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252442149009494039456608811 378663223514241059184913217)
                ·
                  refine ⟨283997417635680794388684913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378663223514241059184913217 283997417635680794388684913)
                  ·
                    refine ⟨212998063226760595791513685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 283997417635680794388684913 212998063226760595791513685)
                    ·
                      refine ⟨2496071053438600731931801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 212998063226760595791513685 2496071053438600731931801)
                      ·
                        rfl

theorem cell23_4861081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_4861081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861081 prefixEnd_4861081 := by exact prefixLift 4861081
  have htrace : WordTrace (prefixWord ++ tailWord_4861081) baseStart_4861081 baseEnd_4861081 := by
    simpa [prefixWord, tailWord_4861081, baseEnd_4861081] using wordTrace_append hprefix tailTrace_4861081
  have hstable : (prefixWord ++ tailWord_4861081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861081).length < 2 ^ (prefixWord ++ tailWord_4861081).sum := by decide
  have hdescent : baseEnd_4861081 < baseStart_4861081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861085 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_4861085 : Nat := 118140960795 + 4861085 * 2 ^ 59
def prefixEnd_4861085 : Nat := 4983230072969 + 3 ^ 40 * 4861085 * 2
def baseEnd_4861085 : Nat := 2496073107361218716281783

theorem tailTrace_4861085 : CollatzResearch.WordTrace tailWord_4861085 prefixEnd_4861085 2496073107361218716281783 := by
  unfold tailWord_4861085
  simp only [CollatzResearch.WordTrace]
  refine ⟨177298335594126727066936709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118198890396084484711291139 177298335594126727066936709)
  ·
    refine ⟨33243437923898761325050633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177298335594126727066936709 33243437923898761325050633)
    ·
      refine ⟨24932578442924070993787975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33243437923898761325050633 24932578442924070993787975)
      ·
        refine ⟨37398867664386106490681963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24932578442924070993787975 37398867664386106490681963)
        ·
          refine ⟨56098301496579159736022945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37398867664386106490681963 56098301496579159736022945)
          ·
            refine ⟨42073726122434369802017209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56098301496579159736022945 42073726122434369802017209)
            ·
              refine ⟨31555294591825777351512907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42073726122434369802017209 31555294591825777351512907)
              ·
                refine ⟨47332941887738666027269361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31555294591825777351512907 47332941887738666027269361)
                ·
                  refine ⟨35499706415803999520452021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47332941887738666027269361 35499706415803999520452021)
                  ·
                    refine ⟨3328097476481624955042377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35499706415803999520452021 3328097476481624955042377)
                    ·
                      refine ⟨2496073107361218716281783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328097476481624955042377 2496073107361218716281783)
                      ·
                        rfl

theorem cell23_4861085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_4861085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861085 prefixEnd_4861085 := by exact prefixLift 4861085
  have htrace : WordTrace (prefixWord ++ tailWord_4861085) baseStart_4861085 baseEnd_4861085 := by
    simpa [prefixWord, tailWord_4861085, baseEnd_4861085] using wordTrace_append hprefix tailTrace_4861085
  have hstable : (prefixWord ++ tailWord_4861085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861085).length < 2 ^ (prefixWord ++ tailWord_4861085).sum := by decide
  have hdescent : baseEnd_4861085 < baseStart_4861085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861088 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 5]
def baseStart_4861088 : Nat := 118140960795 + 4861088 * 2 ^ 59
def prefixEnd_4861088 : Nat := 4983230072969 + 3 ^ 40 * 4861088 * 2
def baseEnd_4861088 : Nat := 2496074647803182204544269

theorem tailTrace_4861088 : CollatzResearch.WordTrace tailWord_4861088 prefixEnd_4861088 2496074647803182204544269 := by
  unfold tailWord_4861088
  simp only [CollatzResearch.WordTrace]
  refine ⟨88649222506557929289647959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118198963342077239052863945 88649222506557929289647959)
  ·
    refine ⟨132973833759836893934471939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88649222506557929289647959 132973833759836893934471939)
    ·
      refine ⟨199460750639755340901707909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132973833759836893934471939 199460750639755340901707909)
      ·
        refine ⟨37398890744954126419070233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199460750639755340901707909 37398890744954126419070233)
        ·
          refine ⟨28049168058715594814302675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37398890744954126419070233 28049168058715594814302675)
          ·
            refine ⟨42073752088073392221454013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28049168058715594814302675 42073752088073392221454013)
            ·
              refine ⟨15777657033027522083045255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42073752088073392221454013 15777657033027522083045255)
              ·
                refine ⟨23666485549541283124567883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15777657033027522083045255 23666485549541283124567883)
                ·
                  refine ⟨35499728324311924686851825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23666485549541283124567883 35499728324311924686851825)
                  ·
                    refine ⟨26624796243233943515138869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35499728324311924686851825 26624796243233943515138869)
                    ·
                      refine ⟨2496074647803182204544269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26624796243233943515138869 2496074647803182204544269)
                      ·
                        rfl

theorem cell23_4861088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_4861088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861088 prefixEnd_4861088 := by exact prefixLift 4861088
  have htrace : WordTrace (prefixWord ++ tailWord_4861088) baseStart_4861088 baseEnd_4861088 := by
    simpa [prefixWord, tailWord_4861088, baseEnd_4861088] using wordTrace_append hprefix tailTrace_4861088
  have hstable : (prefixWord ++ tailWord_4861088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861088).length < 2 ^ (prefixWord ++ tailWord_4861088).sum := by decide
  have hdescent : baseEnd_4861088 < baseStart_4861088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861133 : List Nat := [1, 6, 2, 2, 1, 2, 2, 2, 5]
def baseStart_4861133 : Nat := 118140960795 + 4861133 * 2 ^ 59
def prefixEnd_4861133 : Nat := 4983230072969 + 3 ^ 40 * 4861133 * 2
def baseEnd_4861133 : Nat := 277344194936959392053507

theorem tailTrace_4861133 : CollatzResearch.WordTrace tailWord_4861133 prefixEnd_4861133 277344194936959392053507 := by
  unfold tailWord_4861133
  simp only [CollatzResearch.WordTrace]
  refine ⟨177300086297952831264684053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118200057531968554176456035 177300086297952831264684053)
  ·
    refine ⟨8310941545216538965532065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 177300086297952831264684053 8310941545216538965532065)
    ·
      refine ⟨6233206158912404224149049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8310941545216538965532065 6233206158912404224149049)
      ·
        refine ⟨4674904619184303168111787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6233206158912404224149049 4674904619184303168111787)
        ·
          refine ⟨7012356928776454752167681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4674904619184303168111787 7012356928776454752167681)
          ·
            refine ⟨5259267696582341064125761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7012356928776454752167681 5259267696582341064125761)
            ·
              refine ⟨3944450772436755798094321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5259267696582341064125761 3944450772436755798094321)
              ·
                refine ⟨2958338079327566848570741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3944450772436755798094321 2958338079327566848570741)
                ·
                  refine ⟨277344194936959392053507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2958338079327566848570741 277344194936959392053507)
                  ·
                    rfl

theorem cell23_4861133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_4861133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861133 prefixEnd_4861133 := by exact prefixLift 4861133
  have htrace : WordTrace (prefixWord ++ tailWord_4861133) baseStart_4861133 baseEnd_4861133 := by
    simpa [prefixWord, tailWord_4861133, baseEnd_4861133] using wordTrace_append hprefix tailTrace_4861133
  have hstable : (prefixWord ++ tailWord_4861133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861133).length < 2 ^ (prefixWord ++ tailWord_4861133).sum := by decide
  have hdescent : baseEnd_4861133 < baseStart_4861133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861149 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_4861149 : Nat := 118140960795 + 4861149 * 2 ^ 59
def prefixEnd_4861149 : Nat := 4983230072969 + 3 ^ 40 * 4861149 * 2
def baseEnd_4861149 : Nat := 2496105970123106465881489

theorem tailTrace_4861149 : CollatzResearch.WordTrace tailWord_4861149 prefixEnd_4861149 2496105970123106465881489 := by
  unfold tailWord_4861149
  simp only [CollatzResearch.WordTrace]
  refine ⟨177300669865894865997266501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118200446577263243998177667 177300669865894865997266501)
  ·
    refine ⟨33243875599855287374487469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177300669865894865997266501 33243875599855287374487469)
    ·
      refine ⟨12466453349945732765432801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33243875599855287374487469 12466453349945732765432801)
      ·
        refine ⟨9349840012459299574074601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12466453349945732765432801 9349840012459299574074601)
        ·
          refine ⟨7012380009344474680555951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9349840012459299574074601 7012380009344474680555951)
          ·
            refine ⟨10518570014016712020833927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7012380009344474680555951 10518570014016712020833927)
            ·
              refine ⟨15777855021025068031250891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10518570014016712020833927 15777855021025068031250891)
              ·
                refine ⟨23666782531537602046876337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15777855021025068031250891 23666782531537602046876337)
                ·
                  refine ⟨17750086898653201535157253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23666782531537602046876337 17750086898653201535157253)
                  ·
                    refine ⟨3328141293497475287841985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17750086898653201535157253 3328141293497475287841985)
                    ·
                      refine ⟨2496105970123106465881489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328141293497475287841985 2496105970123106465881489)
                      ·
                        rfl

theorem cell23_4861149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_4861149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861149 prefixEnd_4861149 := by exact prefixLift 4861149
  have htrace : WordTrace (prefixWord ++ tailWord_4861149) baseStart_4861149 baseEnd_4861149 := by
    simpa [prefixWord, tailWord_4861149, baseEnd_4861149] using wordTrace_append hprefix tailTrace_4861149
  have hstable : (prefixWord ++ tailWord_4861149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861149).length < 2 ^ (prefixWord ++ tailWord_4861149).sum := by decide
  have hdescent : baseEnd_4861149 < baseStart_4861149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861175 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 1, 5, 2]
def baseStart_4861175 : Nat := 118140960795 + 4861175 * 2 ^ 59
def prefixEnd_4861175 : Nat := 4983230072969 + 3 ^ 40 * 4861175 * 2
def baseEnd_4861175 : Nat := 2496119320620123364156369

theorem tailTrace_4861175 : CollatzResearch.WordTrace tailWord_4861175 prefixEnd_4861175 2496119320620123364156369 := by
  unfold tailWord_4861175
  simp only [CollatzResearch.WordTrace]
  refine ⟨177301618163800672437712979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118201078775867114958475319 177301618163800672437712979)
  ·
    refine ⟨265952427245701008656569469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177301618163800672437712979 265952427245701008656569469)
    ·
      refine ⟨99732160217137878246213551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265952427245701008656569469 99732160217137878246213551)
      ·
        refine ⟨149598240325706817369320327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99732160217137878246213551 149598240325706817369320327)
        ·
          refine ⟨224397360488560226053980491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149598240325706817369320327 224397360488560226053980491)
          ·
            refine ⟨336596040732840339080970737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224397360488560226053980491 336596040732840339080970737)
            ·
              refine ⟨252447030549630254310728053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336596040732840339080970737 252447030549630254310728053)
              ·
                refine ⟨23666909114027836341630755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 252447030549630254310728053 23666909114027836341630755)
                ·
                  refine ⟨35500363671041754512446133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23666909114027836341630755 35500363671041754512446133)
                  ·
                    refine ⟨3328159094160164485541825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35500363671041754512446133 3328159094160164485541825)
                    ·
                      refine ⟨2496119320620123364156369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328159094160164485541825 2496119320620123364156369)
                      ·
                        rfl

theorem cell23_4861175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 5, 2].length) (baseStart_4861175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861175 prefixEnd_4861175 := by exact prefixLift 4861175
  have htrace : WordTrace (prefixWord ++ tailWord_4861175) baseStart_4861175 baseEnd_4861175 := by
    simpa [prefixWord, tailWord_4861175, baseEnd_4861175] using wordTrace_append hprefix tailTrace_4861175
  have hstable : (prefixWord ++ tailWord_4861175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861175).length < 2 ^ (prefixWord ++ tailWord_4861175).sum := by decide
  have hdescent : baseEnd_4861175 < baseStart_4861175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861242 : List Nat := [3, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3]
def baseStart_4861242 : Nat := 118140960795 + 4861242 * 2 ^ 59
def prefixEnd_4861242 : Nat := 4983230072969 + 3 ^ 40 * 4861242 * 2
def baseEnd_4861242 : Nat := 2496153723823974602018561

theorem tailTrace_4861242 : CollatzResearch.WordTrace tailWord_4861242 prefixEnd_4861242 2496153723823974602018561 := by
  unfold tailWord_4861242
  simp only [CollatzResearch.WordTrace]
  refine ⟨44326015463639485720100495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118202707903038628586934653 44326015463639485720100495)
  ·
    refine ⟨66489023195459228580150743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44326015463639485720100495 66489023195459228580150743)
    ·
      refine ⟨99733534793188842870226115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66489023195459228580150743 99733534793188842870226115)
      ·
        refine ⟨149600302189783264305339173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99733534793188842870226115 149600302189783264305339173)
        ·
          refine ⟨28050056660584362057251095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149600302189783264305339173 28050056660584362057251095)
          ·
            refine ⟨42075084990876543085876643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28050056660584362057251095 42075084990876543085876643)
            ·
              refine ⟨63112627486314814628814965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42075084990876543085876643 63112627486314814628814965)
              ·
                refine ⟨5916808826842013871451403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63112627486314814628814965 5916808826842013871451403)
                ·
                  refine ⟨8875213240263020807177105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5916808826842013871451403 8875213240263020807177105)
                  ·
                    refine ⟨6656409930197265605382829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8875213240263020807177105 6656409930197265605382829)
                    ·
                      refine ⟨2496153723823974602018561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6656409930197265605382829 2496153723823974602018561)
                      ·
                        rfl

theorem cell23_4861242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_4861242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861242 prefixEnd_4861242 := by exact prefixLift 4861242
  have htrace : WordTrace (prefixWord ++ tailWord_4861242) baseStart_4861242 baseEnd_4861242 := by
    simpa [prefixWord, tailWord_4861242, baseEnd_4861242] using wordTrace_append hprefix tailTrace_4861242
  have hstable : (prefixWord ++ tailWord_4861242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861242).length < 2 ^ (prefixWord ++ tailWord_4861242).sum := by decide
  have hdescent : baseEnd_4861242 < baseStart_4861242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861252 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4861252 : Nat := 118140960795 + 4861252 * 2 ^ 59
def prefixEnd_4861252 : Nat := 4983230072969 + 3 ^ 40 * 4861252 * 2
def baseEnd_4861252 : Nat := 2496158858630519562893515

theorem tailTrace_4861252 : CollatzResearch.WordTrace tailWord_4861252 prefixEnd_4861252 2496158858630519562893515 := by
  unfold tailWord_4861252
  simp only [CollatzResearch.WordTrace]
  refine ⟨88652213292260857294133005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118202951056347809725510673 88652213292260857294133005)
  ·
    refine ⟨33244579984597821485299877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88652213292260857294133005 33244579984597821485299877)
    ·
      refine ⟨6233358747112091528493727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33244579984597821485299877 6233358747112091528493727)
      ·
        refine ⟨9350038120668137292740591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6233358747112091528493727 9350038120668137292740591)
        ·
          refine ⟨14025057181002205939110887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9350038120668137292740591 14025057181002205939110887)
          ·
            refine ⟨21037585771503308908666331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14025057181002205939110887 21037585771503308908666331)
            ·
              refine ⟨31556378657254963362999497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21037585771503308908666331 31556378657254963362999497)
              ·
                refine ⟨23667283992941222522249623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31556378657254963362999497 23667283992941222522249623)
                ·
                  refine ⟨35500925989411833783374435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23667283992941222522249623 35500925989411833783374435)
                  ·
                    refine ⟨53251388984117750675061653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35500925989411833783374435 53251388984117750675061653)
                    ·
                      refine ⟨2496158858630519562893515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53251388984117750675061653 2496158858630519562893515)
                      ·
                        rfl

theorem cell23_4861252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4861252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861252 prefixEnd_4861252 := by exact prefixLift 4861252
  have htrace : WordTrace (prefixWord ++ tailWord_4861252) baseStart_4861252 baseEnd_4861252 := by
    simpa [prefixWord, tailWord_4861252, baseEnd_4861252] using wordTrace_append hprefix tailTrace_4861252
  have hstable : (prefixWord ++ tailWord_4861252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861252).length < 2 ^ (prefixWord ++ tailWord_4861252).sum := by decide
  have hdescent : baseEnd_4861252 < baseStart_4861252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861270 : List Nat := [5, 2, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_4861270 : Nat := 118140960795 + 4861270 * 2 ^ 59
def prefixEnd_4861270 : Nat := 4983230072969 + 3 ^ 40 * 4861270 * 2
def baseEnd_4861270 : Nat := 832056033760766830822811

theorem tailTrace_4861270 : CollatzResearch.WordTrace tailWord_4861270 prefixEnd_4861270 832056033760766830822811 := by
  unfold tailWord_4861270
  simp only [CollatzResearch.WordTrace]
  refine ⟨11081567693653531478901329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118203388732304335774947509 11081567693653531478901329)
  ·
    refine ⟨8311175770240148609175997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11081567693653531478901329 8311175770240148609175997)
    ·
      refine ⟨3116690913840055728440999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8311175770240148609175997 3116690913840055728440999)
      ·
        refine ⟨4675036370760083592661499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3116690913840055728440999 4675036370760083592661499)
        ·
          refine ⟨7012554556140125388992249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4675036370760083592661499 7012554556140125388992249)
          ·
            refine ⟨5259415917105094041744187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7012554556140125388992249 5259415917105094041744187)
            ·
              refine ⟨7889123875657641062616281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5259415917105094041744187 7889123875657641062616281)
              ·
                refine ⟨5916842906743230796962211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7889123875657641062616281 5916842906743230796962211)
                ·
                  refine ⟨8875264360114846195443317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5916842906743230796962211 8875264360114846195443317)
                  ·
                    refine ⟨832056033760766830822811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8875264360114846195443317 832056033760766830822811)
                    ·
                      rfl

theorem cell23_4861270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_4861270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861270 prefixEnd_4861270 := by exact prefixLift 4861270
  have htrace : WordTrace (prefixWord ++ tailWord_4861270) baseStart_4861270 baseEnd_4861270 := by
    simpa [prefixWord, tailWord_4861270, baseEnd_4861270] using wordTrace_append hprefix tailTrace_4861270
  have hstable : (prefixWord ++ tailWord_4861270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861270).length < 2 ^ (prefixWord ++ tailWord_4861270).sum := by decide
  have hdescent : baseEnd_4861270 < baseStart_4861270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861375 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 5]
def baseStart_4861375 : Nat := 118140960795 + 4861375 * 2 ^ 59
def prefixEnd_4861375 : Nat := 4983230072969 + 3 ^ 40 * 4861375 * 2
def baseEnd_4861375 : Nat := 2496222016751022581655449

theorem tailTrace_4861375 : CollatzResearch.WordTrace tailWord_4861375 prefixEnd_4861375 2496222016751022581655449 := by
  unfold tailWord_4861375
  simp only [CollatzResearch.WordTrace]
  refine ⟨177308912763076106594993579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118205941842050737729995719 177308912763076106594993579)
  ·
    refine ⟨265963369144614159892490369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177308912763076106594993579 265963369144614159892490369)
    ·
      refine ⟨199472526858460619919367777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265963369144614159892490369 199472526858460619919367777)
      ·
        refine ⟨149604395143845464939525833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199472526858460619919367777 149604395143845464939525833)
        ·
          refine ⟨112203296357884098704644375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149604395143845464939525833 112203296357884098704644375)
          ·
            refine ⟨168304944536826148056966563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112203296357884098704644375 168304944536826148056966563)
            ·
              refine ⟨252457416805239222085449845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168304944536826148056966563 252457416805239222085449845)
              ·
                refine ⟨23667882825491177070510923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 252457416805239222085449845 23667882825491177070510923)
                ·
                  refine ⟨35501824238236765605766385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23667882825491177070510923 35501824238236765605766385)
                  ·
                    refine ⟨26626368178677574204324789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35501824238236765605766385 26626368178677574204324789)
                    ·
                      refine ⟨2496222016751022581655449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26626368178677574204324789 2496222016751022581655449)
                      ·
                        rfl

theorem cell23_4861375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_4861375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861375 prefixEnd_4861375 := by exact prefixLift 4861375
  have htrace : WordTrace (prefixWord ++ tailWord_4861375) baseStart_4861375 baseEnd_4861375 := by
    simpa [prefixWord, tailWord_4861375, baseEnd_4861375] using wordTrace_append hprefix tailTrace_4861375
  have hstable : (prefixWord ++ tailWord_4861375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861375).length < 2 ^ (prefixWord ++ tailWord_4861375).sum := by decide
  have hdescent : baseEnd_4861375 < baseStart_4861375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861380 : List Nat := [2, 3, 3, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_4861380 : Nat := 118140960795 + 4861380 * 2 ^ 59
def prefixEnd_4861380 : Nat := 4983230072969 + 3 ^ 40 * 4861380 * 2
def baseEnd_4861380 : Nat := 2496224584154295062092927

theorem tailTrace_4861380 : CollatzResearch.WordTrace tailWord_4861380 prefixEnd_4861380 2496224584154295062092927 := by
  unfold tailWord_4861380
  simp only [CollatzResearch.WordTrace]
  refine ⟨88654547564028996224462797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118206063418705328299283729 88654547564028996224462797)
  ·
    refine ⟨33245455336510873584173549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88654547564028996224462797 33245455336510873584173549)
    ·
      refine ⟨12467045751191577594065081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33245455336510873584173549 12467045751191577594065081)
      ·
        refine ⟨9350284313393683195548811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12467045751191577594065081 9350284313393683195548811)
        ·
          refine ⟨14025426470090524793323217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9350284313393683195548811 14025426470090524793323217)
          ·
            refine ⟨10519069852567893594992413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14025426470090524793323217 10519069852567893594992413)
            ·
              refine ⟨3944651194712960098122155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10519069852567893594992413 3944651194712960098122155)
              ·
                refine ⟨5916976792069440147183233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944651194712960098122155 5916976792069440147183233)
                ·
                  refine ⟨4437732594052080110387425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5916976792069440147183233 4437732594052080110387425)
                  ·
                    refine ⟨3328299445539060082790569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4437732594052080110387425 3328299445539060082790569)
                    ·
                      refine ⟨2496224584154295062092927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328299445539060082790569 2496224584154295062092927)
                      ·
                        rfl

theorem cell23_4861380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_4861380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861380 prefixEnd_4861380 := by exact prefixLift 4861380
  have htrace : WordTrace (prefixWord ++ tailWord_4861380) baseStart_4861380 baseEnd_4861380 := by
    simpa [prefixWord, tailWord_4861380, baseEnd_4861380] using wordTrace_append hprefix tailTrace_4861380
  have hstable : (prefixWord ++ tailWord_4861380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861380).length < 2 ^ (prefixWord ++ tailWord_4861380).sum := by decide
  have hdescent : baseEnd_4861380 < baseStart_4861380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861402 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_4861402 : Nat := 118140960795 + 4861402 * 2 ^ 59
def prefixEnd_4861402 : Nat := 4983230072969 + 3 ^ 40 * 4861402 * 2
def baseEnd_4861402 : Nat := 2496235880728693976017825

theorem tailTrace_4861402 : CollatzResearch.WordTrace tailWord_4861402 prefixEnd_4861402 2496235880728693976017825 := by
  unfold tailWord_4861402
  simp only [CollatzResearch.WordTrace]
  refine ⟨44327474383494572551556615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118206598355985526804150973 44327474383494572551556615)
  ·
    refine ⟨66491211575241858827334923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44327474383494572551556615 66491211575241858827334923)
    ·
      refine ⟨99736817362862788241002385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66491211575241858827334923 99736817362862788241002385)
      ·
        refine ⟨74802613022147091180751789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99736817362862788241002385 74802613022147091180751789)
        ·
          refine ⟨28050979883305159192781921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74802613022147091180751789 28050979883305159192781921)
          ·
            refine ⟨21038234912478869394586441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28050979883305159192781921 21038234912478869394586441)
            ·
              refine ⟨15778676184359152045939831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21038234912478869394586441 15778676184359152045939831)
              ·
                refine ⟨23668014276538728068909747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15778676184359152045939831 23668014276538728068909747)
                ·
                  refine ⟨35502021414808092103364621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23668014276538728068909747 35502021414808092103364621)
                  ·
                    refine ⟨13313258030553034538761733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35502021414808092103364621 13313258030553034538761733)
                    ·
                      refine ⟨2496235880728693976017825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13313258030553034538761733 2496235880728693976017825)
                      ·
                        rfl

theorem cell23_4861402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_4861402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861402 prefixEnd_4861402 := by exact prefixLift 4861402
  have htrace : WordTrace (prefixWord ++ tailWord_4861402) baseStart_4861402 baseEnd_4861402 := by
    simpa [prefixWord, tailWord_4861402, baseEnd_4861402] using wordTrace_append hprefix tailTrace_4861402
  have hstable : (prefixWord ++ tailWord_4861402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861402).length < 2 ^ (prefixWord ++ tailWord_4861402).sum := by decide
  have hdescent : baseEnd_4861402 < baseStart_4861402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861412 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_4861412 : Nat := 118140960795 + 4861412 * 2 ^ 59
def prefixEnd_4861412 : Nat := 4983230072969 + 3 ^ 40 * 4861412 * 2
def baseEnd_4861412 : Nat := 832080338511746312297593

theorem tailTrace_4861412 : CollatzResearch.WordTrace tailWord_4861412 prefixEnd_4861412 832080338511746312297593 := by
  unfold tailWord_4861412
  simp only [CollatzResearch.WordTrace]
  refine ⟨88655131131971030957045245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118206841509294707942726993 88655131131971030957045245)
  ·
    refine ⟨33245674174489136608891967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88655131131971030957045245 33245674174489136608891967)
    ·
      refine ⟨49868511261733704913337951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33245674174489136608891967 49868511261733704913337951)
      ·
        refine ⟨74802766892600557370006927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49868511261733704913337951 74802766892600557370006927)
        ·
          refine ⟨112204150338900836055010391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74802766892600557370006927 112204150338900836055010391)
          ·
            refine ⟨168306225508351254082515587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112204150338900836055010391 168306225508351254082515587)
            ·
              refine ⟨252459338262526881123773381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168306225508351254082515587 252459338262526881123773381)
              ·
                refine ⟨47336125924223790210707509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252459338262526881123773381 47336125924223790210707509)
                ·
                  refine ⟨4437761805395980332253829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47336125924223790210707509 4437761805395980332253829)
                  ·
                    refine ⟨832080338511746312297593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4437761805395980332253829 832080338511746312297593)
                    ·
                      rfl

theorem cell23_4861412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_4861412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861412 prefixEnd_4861412 := by exact prefixLift 4861412
  have htrace : WordTrace (prefixWord ++ tailWord_4861412) baseStart_4861412 baseEnd_4861412 := by
    simpa [prefixWord, tailWord_4861412, baseEnd_4861412] using wordTrace_append hprefix tailTrace_4861412
  have hstable : (prefixWord ++ tailWord_4861412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861412).length < 2 ^ (prefixWord ++ tailWord_4861412).sum := by decide
  have hdescent : baseEnd_4861412 < baseStart_4861412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861509 : List Nat := [1, 3, 1, 1, 1, 4, 2, 4, 1, 1, 4]
def baseStart_4861509 : Nat := 118140960795 + 4861509 * 2 ^ 59
def prefixEnd_4861509 : Nat := 4983230072969 + 3 ^ 40 * 4861509 * 2
def baseEnd_4861509 : Nat := 2496290823158725057379833

theorem tailTrace_4861509 : CollatzResearch.WordTrace tailWord_4861509 prefixEnd_4861509 2496290823158725057379833 := by
  unfold tailWord_4861509
  simp only [CollatzResearch.WordTrace]
  refine ⟨177313800144590647480371581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118209200096393764986914387 177313800144590647480371581)
  ·
    refine ⟨66492675054221492805139343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177313800144590647480371581 66492675054221492805139343)
    ·
      refine ⟨99739012581332239207709015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66492675054221492805139343 99739012581332239207709015)
      ·
        refine ⟨149608518871998358811563523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99739012581332239207709015 149608518871998358811563523)
        ·
          refine ⟨224412778307997538217345285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149608518871998358811563523 224412778307997538217345285)
          ·
            refine ⟨42077395932749538415752241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224412778307997538217345285 42077395932749538415752241)
            ·
              refine ⟨31558046949562153811814181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42077395932749538415752241 31558046949562153811814181)
              ·
                refine ⟨5917133803042903839715159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31558046949562153811814181 5917133803042903839715159)
                ·
                  refine ⟨8875700704564355759572739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5917133803042903839715159 8875700704564355759572739)
                  ·
                    refine ⟨13313551056846533639359109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8875700704564355759572739 13313551056846533639359109)
                    ·
                      refine ⟨2496290823158725057379833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13313551056846533639359109 2496290823158725057379833)
                      ·
                        rfl

theorem cell23_4861509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_4861509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861509 prefixEnd_4861509 := by exact prefixLift 4861509
  have htrace : WordTrace (prefixWord ++ tailWord_4861509) baseStart_4861509 baseEnd_4861509 := by
    simpa [prefixWord, tailWord_4861509, baseEnd_4861509] using wordTrace_append hprefix tailTrace_4861509
  have hstable : (prefixWord ++ tailWord_4861509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861509).length < 2 ^ (prefixWord ++ tailWord_4861509).sum := by decide
  have hdescent : baseEnd_4861509 < baseStart_4861509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861612 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_4861612 : Nat := 118140960795 + 4861612 * 2 ^ 59
def prefixEnd_4861612 : Nat := 4983230072969 + 3 ^ 40 * 4861612 * 2
def baseEnd_4861612 : Nat := 2496343711666138154391859

theorem tailTrace_4861612 : CollatzResearch.WordTrace tailWord_4861612 prefixEnd_4861612 2496343711666138154391859 := by
  unfold tailWord_4861612
  simp only [CollatzResearch.WordTrace]
  refine ⟨88658778431608748035685545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118211704575478330714247393 88658778431608748035685545)
  ·
    refine ⟨66494083823706561026764159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88658778431608748035685545 66494083823706561026764159)
    ·
      refine ⟨99741125735559841540146239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66494083823706561026764159 99741125735559841540146239)
      ·
        refine ⟨149611688603339762310219359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99741125735559841540146239 149611688603339762310219359)
        ·
          refine ⟨224417532905009643465329039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149611688603339762310219359 224417532905009643465329039)
          ·
            refine ⟨336626299357514465197993559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224417532905009643465329039 336626299357514465197993559)
            ·
              refine ⟨504939449036271697796990339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336626299357514465197993559 504939449036271697796990339)
              ·
                refine ⟨757409173554407546695485509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504939449036271697796990339 757409173554407546695485509)
                ·
                  refine ⟨142014220041451415005403533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 757409173554407546695485509 142014220041451415005403533)
                  ·
                    refine ⟨53255332515544280627026325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142014220041451415005403533 53255332515544280627026325)
                    ·
                      refine ⟨2496343711666138154391859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53255332515544280627026325 2496343711666138154391859)
                      ·
                        rfl

theorem cell23_4861612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_4861612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861612 prefixEnd_4861612 := by exact prefixLift 4861612
  have htrace : WordTrace (prefixWord ++ tailWord_4861612) baseStart_4861612 baseEnd_4861612 := by
    simpa [prefixWord, tailWord_4861612, baseEnd_4861612] using wordTrace_append hprefix tailTrace_4861612
  have hstable : (prefixWord ++ tailWord_4861612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861612).length < 2 ^ (prefixWord ++ tailWord_4861612).sum := by decide
  have hdescent : baseEnd_4861612 < baseStart_4861612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861650 : List Nat := [3, 2, 2, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_4861650 : Nat := 118140960795 + 4861650 * 2 ^ 59
def prefixEnd_4861650 : Nat := 4983230072969 + 3 ^ 40 * 4861650 * 2
def baseEnd_4861650 : Nat := 2496363223931009005716685

theorem tailTrace_4861650 : CollatzResearch.WordTrace tailWord_4861650 prefixEnd_4861650 2496363223931009005716685 := by
  unfold tailWord_4861650
  simp only [CollatzResearch.WordTrace]
  refine ⟨44329735709269957140313601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118212628558053219040836269 44329735709269957140313601)
  ·
    refine ⟨33247301781952467855235201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44329735709269957140313601 33247301781952467855235201)
    ·
      refine ⟨24935476336464350891426401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33247301781952467855235201 24935476336464350891426401)
      ·
        refine ⟨18701607252348263168569801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24935476336464350891426401 18701607252348263168569801)
        ·
          refine ⟨14026205439261197376427351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18701607252348263168569801 14026205439261197376427351)
          ·
            refine ⟨21039308158891796064641027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14026205439261197376427351 21039308158891796064641027)
            ·
              refine ⟨31558962238337694096961541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21039308158891796064641027 31558962238337694096961541)
              ·
                refine ⟨5917305419688317643180289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31558962238337694096961541 5917305419688317643180289)
                ·
                  refine ⟨4437979064766238232385217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5917305419688317643180289 4437979064766238232385217)
                  ·
                    refine ⟨3328484298574678674288913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4437979064766238232385217 3328484298574678674288913)
                    ·
                      refine ⟨2496363223931009005716685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328484298574678674288913 2496363223931009005716685)
                      ·
                        rfl

theorem cell23_4861650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_4861650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861650 prefixEnd_4861650 := by exact prefixLift 4861650
  have htrace : WordTrace (prefixWord ++ tailWord_4861650) baseStart_4861650 baseEnd_4861650 := by
    simpa [prefixWord, tailWord_4861650, baseEnd_4861650] using wordTrace_append hprefix tailTrace_4861650
  have hstable : (prefixWord ++ tailWord_4861650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861650).length < 2 ^ (prefixWord ++ tailWord_4861650).sum := by decide
  have hdescent : baseEnd_4861650 < baseStart_4861650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861656 : List Nat := [2, 1, 2, 2, 3, 1, 3, 4, 5]
def baseStart_4861656 : Nat := 118140960795 + 4861656 * 2 ^ 59
def prefixEnd_4861656 : Nat := 4983230072969 + 3 ^ 40 * 4861656 * 2
def baseEnd_4861656 : Nat := 277374033868326220249073

theorem tailTrace_4861656 : CollatzResearch.WordTrace tailWord_4861656 prefixEnd_4861656 277374033868326220249073 := by
  unfold tailWord_4861656
  simp only [CollatzResearch.WordTrace]
  refine ⟨88659580837529045792986411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118212774450038727723981881 88659580837529045792986411)
  ·
    refine ⟨132989371256293568689479617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88659580837529045792986411 132989371256293568689479617)
    ·
      refine ⟨99742028442220176517109713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132989371256293568689479617 99742028442220176517109713)
      ·
        refine ⟨74806521331665132387832285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99742028442220176517109713 74806521331665132387832285)
        ·
          refine ⟨28052445499374424645437107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74806521331665132387832285 28052445499374424645437107)
          ·
            refine ⟨42078668249061636968155661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28052445499374424645437107 42078668249061636968155661)
            ·
              refine ⟨15779500593398113863058373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42078668249061636968155661 15779500593398113863058373)
              ·
                refine ⟨2958656361262146349323445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15779500593398113863058373 2958656361262146349323445)
                ·
                  refine ⟨277374033868326220249073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2958656361262146349323445 277374033868326220249073)
                  ·
                    rfl

theorem cell23_4861656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 5].length) (baseStart_4861656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861656 prefixEnd_4861656 := by exact prefixLift 4861656
  have htrace : WordTrace (prefixWord ++ tailWord_4861656) baseStart_4861656 baseEnd_4861656 := by
    simpa [prefixWord, tailWord_4861656, baseEnd_4861656] using wordTrace_append hprefix tailTrace_4861656
  have hstable : (prefixWord ++ tailWord_4861656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861656).length < 2 ^ (prefixWord ++ tailWord_4861656).sum := by decide
  have hdescent : baseEnd_4861656 < baseStart_4861656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861669 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 1, 7]
def baseStart_4861669 : Nat := 118140960795 + 4861669 * 2 ^ 59
def prefixEnd_4861669 : Nat := 4983230072969 + 3 ^ 40 * 4861669 * 2
def baseEnd_4861669 : Nat := 832124326687814810459699

theorem tailTrace_4861669 : CollatzResearch.WordTrace tailWord_4861669 prefixEnd_4861669 832124326687814810459699 := by
  unfold tailWord_4861669
  simp only [CollatzResearch.WordTrace]
  refine ⟨177319635824010994806196061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118213090549340663204130707 177319635824010994806196061)
  ·
    refine ⟨66494863434004123052323523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177319635824010994806196061 66494863434004123052323523)
    ·
      refine ⟨99742295151006184578485285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66494863434004123052323523 99742295151006184578485285)
      ·
        refine ⟨18701680340813659608465991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99742295151006184578485285 18701680340813659608465991)
        ·
          refine ⟨28052520511220489412698987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18701680340813659608465991 28052520511220489412698987)
          ·
            refine ⟨42078780766830734119048481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28052520511220489412698987 42078780766830734119048481)
            ·
              refine ⟨31559085575123050589286361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42078780766830734119048481 31559085575123050589286361)
              ·
                refine ⟨23669314181342287941964771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31559085575123050589286361 23669314181342287941964771)
                ·
                  refine ⟨35503971272013431912947157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23669314181342287941964771 35503971272013431912947157)
                  ·
                    refine ⟨832124326687814810459699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35503971272013431912947157 832124326687814810459699)
                    ·
                      rfl

theorem cell23_4861669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_4861669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861669 prefixEnd_4861669 := by exact prefixLift 4861669
  have htrace : WordTrace (prefixWord ++ tailWord_4861669) baseStart_4861669 baseEnd_4861669 := by
    simpa [prefixWord, tailWord_4861669, baseEnd_4861669] using wordTrace_append hprefix tailTrace_4861669
  have hstable : (prefixWord ++ tailWord_4861669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861669).length < 2 ^ (prefixWord ++ tailWord_4861669).sum := by decide
  have hdescent : baseEnd_4861669 < baseStart_4861669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861686 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_4861686 : Nat := 118140960795 + 4861686 * 2 ^ 59
def prefixEnd_4861686 : Nat := 4983230072969 + 3 ^ 40 * 4861686 * 2
def baseEnd_4861686 : Nat := 832127236411523621622173

theorem tailTrace_4861686 : CollatzResearch.WordTrace tailWord_4861686 prefixEnd_4861686 832127236411523621622173 := by
  unfold tailWord_4861686
  simp only [CollatzResearch.WordTrace]
  refine ⟨11082515991559337919347807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118213503909966271139709941 11082515991559337919347807)
  ·
    refine ⟨16623773987339006879021711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11082515991559337919347807 16623773987339006879021711)
    ·
      refine ⟨24935660981008510318532567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16623773987339006879021711 24935660981008510318532567)
      ·
        refine ⟨37403491471512765477798851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24935660981008510318532567 37403491471512765477798851)
        ·
          refine ⟨56105237207269148216698277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37403491471512765477798851 56105237207269148216698277)
          ·
            refine ⟨10519731976362965290630927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56105237207269148216698277 10519731976362965290630927)
            ·
              refine ⟨15779597964544447935946391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10519731976362965290630927 15779597964544447935946391)
              ·
                refine ⟨23669396946816671903919587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15779597964544447935946391 23669396946816671903919587)
                ·
                  refine ⟨35504095420225007855879381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23669396946816671903919587 35504095420225007855879381)
                  ·
                    refine ⟨832127236411523621622173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35504095420225007855879381 832127236411523621622173)
                    ·
                      rfl

theorem cell23_4861686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_4861686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861686 prefixEnd_4861686 := by exact prefixLift 4861686
  have htrace : WordTrace (prefixWord ++ tailWord_4861686) baseStart_4861686 baseEnd_4861686 := by
    simpa [prefixWord, tailWord_4861686, baseEnd_4861686] using wordTrace_append hprefix tailTrace_4861686
  have hstable : (prefixWord ++ tailWord_4861686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861686).length < 2 ^ (prefixWord ++ tailWord_4861686).sum := by decide
  have hdescent : baseEnd_4861686 < baseStart_4861686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861779 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 4]
def baseStart_4861779 : Nat := 118140960795 + 4861779 * 2 ^ 59
def prefixEnd_4861779 : Nat := 4983230072969 + 3 ^ 40 * 4861779 * 2
def baseEnd_4861779 : Nat := 2496429462935439001003591

theorem tailTrace_4861779 : CollatzResearch.WordTrace tailWord_4861779 prefixEnd_4861779 2496429462935439001003591 := by
  unfold tailWord_4861779
  simp only [CollatzResearch.WordTrace]
  refine ⟨177323647853612483592700391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118215765235741655728466927 177323647853612483592700391)
  ·
    refine ⟨265985471780418725389050587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177323647853612483592700391 265985471780418725389050587)
    ·
      refine ⟨398978207670628088083575881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265985471780418725389050587 398978207670628088083575881)
      ·
        refine ⟨299233655752971066062681911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398978207670628088083575881 299233655752971066062681911)
        ·
          refine ⟨448850483629456599094022867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299233655752971066062681911 448850483629456599094022867)
          ·
            refine ⟨673275725444184898641034301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448850483629456599094022867 673275725444184898641034301)
            ·
              refine ⟨252478397041569336990387863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 673275725444184898641034301 252478397041569336990387863)
              ·
                refine ⟨378717595562354005485581795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252478397041569336990387863 378717595562354005485581795)
                ·
                  refine ⟨568076393343531008228372693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378717595562354005485581795 568076393343531008228372693)
                  ·
                    refine ⟨13314290468989008005352485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 568076393343531008228372693 13314290468989008005352485)
                    ·
                      refine ⟨2496429462935439001003591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13314290468989008005352485 2496429462935439001003591)
                      ·
                        rfl

theorem cell23_4861779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_4861779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861779 prefixEnd_4861779 := by exact prefixLift 4861779
  have htrace : WordTrace (prefixWord ++ tailWord_4861779) baseStart_4861779 baseEnd_4861779 := by
    simpa [prefixWord, tailWord_4861779, baseEnd_4861779] using wordTrace_append hprefix tailTrace_4861779
  have hstable : (prefixWord ++ tailWord_4861779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861779).length < 2 ^ (prefixWord ++ tailWord_4861779).sum := by decide
  have hdescent : baseEnd_4861779 < baseStart_4861779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861780 : List Nat := [2, 4, 1, 1, 3, 3, 2, 1, 6]
def baseStart_4861780 : Nat := 118140960795 + 4861780 * 2 ^ 59
def prefixEnd_4861780 : Nat := 4983230072969 + 3 ^ 40 * 4861780 * 2
def baseEnd_4861780 : Nat := 277381108490677055232343

theorem tailTrace_4861780 : CollatzResearch.WordTrace tailWord_4861780 prefixEnd_4861780 277381108490677055232343 := by
  unfold tailWord_4861780
  simp only [CollatzResearch.WordTrace]
  refine ⟨88661842163304430381743397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118215789551072573842324529 88661842163304430381743397)
  ·
    refine ⟨16624095405619580696576887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88661842163304430381743397 16624095405619580696576887)
    ·
      refine ⟨24936143108429371044865331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16624095405619580696576887 24936143108429371044865331)
      ·
        refine ⟨37404214662644056567297997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24936143108429371044865331 37404214662644056567297997)
        ·
          refine ⟨14026580498491521212736749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37404214662644056567297997 14026580498491521212736749)
          ·
            refine ⟨5259967686934320454776281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14026580498491521212736749 5259967686934320454776281)
            ·
              refine ⟨3944975765200740341082211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5259967686934320454776281 3944975765200740341082211)
              ·
                refine ⟨5917463647801110511623317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944975765200740341082211 5917463647801110511623317)
                ·
                  refine ⟨277381108490677055232343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5917463647801110511623317 277381108490677055232343)
                  ·
                    rfl

theorem cell23_4861780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_4861780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861780 prefixEnd_4861780 := by exact prefixLift 4861780
  have htrace : WordTrace (prefixWord ++ tailWord_4861780) baseStart_4861780 baseEnd_4861780 := by
    simpa [prefixWord, tailWord_4861780, baseEnd_4861780] using wordTrace_append hprefix tailTrace_4861780
  have hstable : (prefixWord ++ tailWord_4861780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861780).length < 2 ^ (prefixWord ++ tailWord_4861780).sum := by decide
  have hdescent : baseEnd_4861780 < baseStart_4861780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861800 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_4861800 : Nat := 118140960795 + 4861800 * 2 ^ 59
def prefixEnd_4861800 : Nat := 4983230072969 + 3 ^ 40 * 4861800 * 2
def baseEnd_4861800 : Nat := 2496440246029183418840995

theorem tailTrace_4861800 : CollatzResearch.WordTrace tailWord_4861800 prefixEnd_4861800 2496440246029183418840995 := by
  unfold tailWord_4861800
  simp only [CollatzResearch.WordTrace]
  refine ⟨88662206893268202089607427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118216275857690936119476569 88662206893268202089607427)
  ·
    refine ⟨132993310339902303134411141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88662206893268202089607427 132993310339902303134411141)
    ·
      refine ⟨24936245688731681837702089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132993310339902303134411141 24936245688731681837702089)
      ·
        refine ⟨18702184266548761378276567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24936245688731681837702089 18702184266548761378276567)
        ·
          refine ⟨28053276399823142067414851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18702184266548761378276567 28053276399823142067414851)
          ·
            refine ⟨42079914599734713101122277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28053276399823142067414851 42079914599734713101122277)
            ·
              refine ⟨7889983987450258706460427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42079914599734713101122277 7889983987450258706460427)
              ·
                refine ⟨11834975981175388059690641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7889983987450258706460427 11834975981175388059690641)
                ·
                  refine ⟨8876231985881541044767981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11834975981175388059690641 8876231985881541044767981)
                  ·
                    refine ⟨3328586994705577891787993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8876231985881541044767981 3328586994705577891787993)
                    ·
                      refine ⟨2496440246029183418840995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328586994705577891787993 2496440246029183418840995)
                      ·
                        rfl

theorem cell23_4861800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_4861800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861800 prefixEnd_4861800 := by exact prefixLift 4861800
  have htrace : WordTrace (prefixWord ++ tailWord_4861800) baseStart_4861800 baseEnd_4861800 := by
    simpa [prefixWord, tailWord_4861800, baseEnd_4861800] using wordTrace_append hprefix tailTrace_4861800
  have hstable : (prefixWord ++ tailWord_4861800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861800).length < 2 ^ (prefixWord ++ tailWord_4861800).sum := by decide
  have hdescent : baseEnd_4861800 < baseStart_4861800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861853 : List Nat := [1, 4, 2, 1, 2, 3, 3, 7]
def baseStart_4861853 : Nat := 118140960795 + 4861853 * 2 ^ 59
def prefixEnd_4861853 : Nat := 4983230072969 + 3 ^ 40 * 4861853 * 2
def baseEnd_4861853 : Nat := 92461757796439693017713

theorem tailTrace_4861853 : CollatzResearch.WordTrace tailWord_4861853 prefixEnd_4861853 92461757796439693017713 := by
  unfold tailWord_4861853
  simp only [CollatzResearch.WordTrace]
  refine ⟨177326346855344394230894213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118217564570229596153929475 177326346855344394230894213)
  ·
    refine ⟨33248690035377073918292665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177326346855344394230894213 33248690035377073918292665)
    ·
      refine ⟨24936517526532805438719499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33248690035377073918292665 24936517526532805438719499)
      ·
        refine ⟨37404776289799208158079249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24936517526532805438719499 37404776289799208158079249)
        ·
          refine ⟨28053582217349406118559437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37404776289799208158079249 28053582217349406118559437)
          ·
            refine ⟨10520093331506027294459789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28053582217349406118559437 10520093331506027294459789)
            ·
              refine ⟨3945034999314760235422421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10520093331506027294459789 3945034999314760235422421)
              ·
                refine ⟨92461757796439693017713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3945034999314760235422421 92461757796439693017713)
                ·
                  rfl

theorem cell23_4861853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 7].length) (baseStart_4861853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861853 prefixEnd_4861853 := by exact prefixLift 4861853
  have htrace : WordTrace (prefixWord ++ tailWord_4861853) baseStart_4861853 baseEnd_4861853 := by
    simpa [prefixWord, tailWord_4861853, baseEnd_4861853] using wordTrace_append hprefix tailTrace_4861853
  have hstable : (prefixWord ++ tailWord_4861853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861853).length < 2 ^ (prefixWord ++ tailWord_4861853).sum := by decide
  have hdescent : baseEnd_4861853 < baseStart_4861853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861923 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 5]
def baseStart_4861923 : Nat := 118140960795 + 4861923 * 2 ^ 59
def prefixEnd_4861923 : Nat := 4983230072969 + 3 ^ 40 * 4861923 * 2
def baseEnd_4861923 : Nat := 2496503404149686437602929

theorem tailTrace_4861923 : CollatzResearch.WordTrace tailWord_4861923 prefixEnd_4861923 2496503404149686437602929 := by
  unfold tailWord_4861923
  simp only [CollatzResearch.WordTrace]
  refine ⟨177328899965090796185942423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118219266643393864123961615 177328899965090796185942423)
  ·
    refine ⟨265993349947636194278913635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177328899965090796185942423 265993349947636194278913635)
    ·
      refine ⟨398990024921454291418370453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265993349947636194278913635 398990024921454291418370453)
      ·
        refine ⟨18702657418193169910236115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 398990024921454291418370453 18702657418193169910236115)
        ·
          refine ⟨28053986127289754865354173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18702657418193169910236115 28053986127289754865354173)
          ·
            refine ⟨10520244797733658074507815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28053986127289754865354173 10520244797733658074507815)
            ·
              refine ⟨15780367196600487111761723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10520244797733658074507815 15780367196600487111761723)
              ·
                refine ⟨23670550794900730667642585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15780367196600487111761723 23670550794900730667642585)
                ·
                  refine ⟨17752913096175548000731939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23670550794900730667642585 17752913096175548000731939)
                  ·
                    refine ⟨26629369644263322001097909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17752913096175548000731939 26629369644263322001097909)
                    ·
                      refine ⟨2496503404149686437602929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26629369644263322001097909 2496503404149686437602929)
                      ·
                        rfl

theorem cell23_4861923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_4861923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861923 prefixEnd_4861923 := by exact prefixLift 4861923
  have htrace : WordTrace (prefixWord ++ tailWord_4861923) baseStart_4861923 baseEnd_4861923 := by
    simpa [prefixWord, tailWord_4861923, baseEnd_4861923] using wordTrace_append hprefix tailTrace_4861923
  have hstable : (prefixWord ++ tailWord_4861923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861923).length < 2 ^ (prefixWord ++ tailWord_4861923).sum := by decide
  have hdescent : baseEnd_4861923 < baseStart_4861923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861953 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_4861953 : Nat := 118140960795 + 4861953 * 2 ^ 59
def prefixEnd_4861953 : Nat := 4983230072969 + 3 ^ 40 * 4861953 * 2
def baseEnd_4861953 : Nat := 2496518808569321320227791

theorem tailTrace_4861953 : CollatzResearch.WordTrace tailWord_4861953 prefixEnd_4861953 2496518808569321320227791 := by
  unfold tailWord_4861953
  simp only [CollatzResearch.WordTrace]
  refine ⟨177329994154982111309534513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118219996103321407539689675 177329994154982111309534513)
  ·
    refine ⟨132997495616236583482150885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177329994154982111309534513 132997495616236583482150885)
    ·
      refine ⟨24937030428044359402903291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132997495616236583482150885 24937030428044359402903291)
      ·
        refine ⟨37405545642066539104354937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24937030428044359402903291 37405545642066539104354937)
        ·
          refine ⟨28054159231549904328266203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37405545642066539104354937 28054159231549904328266203)
          ·
            refine ⟨42081238847324856492399305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28054159231549904328266203 42081238847324856492399305)
            ·
              refine ⟨31560929135493642369299479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42081238847324856492399305 31560929135493642369299479)
              ·
                refine ⟨47341393703240463553949219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31560929135493642369299479 47341393703240463553949219)
                ·
                  refine ⟨71012090554860695330923829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47341393703240463553949219 71012090554860695330923829)
                  ·
                    refine ⟨6657383489518190187274109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71012090554860695330923829 6657383489518190187274109)
                    ·
                      refine ⟨2496518808569321320227791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6657383489518190187274109 2496518808569321320227791)
                      ·
                        rfl

theorem cell23_4861953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_4861953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861953 prefixEnd_4861953 := by exact prefixLift 4861953
  have htrace : WordTrace (prefixWord ++ tailWord_4861953) baseStart_4861953 baseEnd_4861953 := by
    simpa [prefixWord, tailWord_4861953, baseEnd_4861953] using wordTrace_append hprefix tailTrace_4861953
  have hstable : (prefixWord ++ tailWord_4861953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861953).length < 2 ^ (prefixWord ++ tailWord_4861953).sum := by decide
  have hdescent : baseEnd_4861953 < baseStart_4861953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861958 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4861958 : Nat := 118140960795 + 4861958 * 2 ^ 59
def prefixEnd_4861958 : Nat := 4983230072969 + 3 ^ 40 * 4861958 * 2
def baseEnd_4861958 : Nat := 2496521375972593800665269

theorem tailTrace_4861958 : CollatzResearch.WordTrace tailWord_4861958 prefixEnd_4861958 2496521375972593800665269 := by
  unfold tailWord_4861958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5541568016248874911358329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118220117679975998108977685 5541568016248874911358329)
  ·
    refine ⟨4156176012186656183518747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5541568016248874911358329 4156176012186656183518747)
    ·
      refine ⟨6234264018279984275278121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4156176012186656183518747 6234264018279984275278121)
      ·
        refine ⟨4675698013709988206458591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6234264018279984275278121 4675698013709988206458591)
        ·
          refine ⟨7013547020564982309687887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4675698013709988206458591 7013547020564982309687887)
          ·
            refine ⟨10520320530847473464531831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7013547020564982309687887 10520320530847473464531831)
            ·
              refine ⟨15780480796271210196797747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10520320530847473464531831 15780480796271210196797747)
              ·
                refine ⟨23670721194406815295196621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15780480796271210196797747 23670721194406815295196621)
                ·
                  refine ⟨8876520447902555735698733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23670721194406815295196621 8876520447902555735698733)
                  ·
                    refine ⟨3328695167963458400887025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8876520447902555735698733 3328695167963458400887025)
                    ·
                      refine ⟨2496521375972593800665269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328695167963458400887025 2496521375972593800665269)
                      ·
                        rfl

theorem cell23_4861958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4861958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861958 prefixEnd_4861958 := by exact prefixLift 4861958
  have htrace : WordTrace (prefixWord ++ tailWord_4861958) baseStart_4861958 baseEnd_4861958 := by
    simpa [prefixWord, tailWord_4861958, baseEnd_4861958] using wordTrace_append hprefix tailTrace_4861958
  have hstable : (prefixWord ++ tailWord_4861958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861958).length < 2 ^ (prefixWord ++ tailWord_4861958).sum := by decide
  have hdescent : baseEnd_4861958 < baseStart_4861958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4861994 : List Nat := [3, 1, 4, 1, 2, 3, 2, 2, 5]
def baseStart_4861994 : Nat := 118140960795 + 4861994 * 2 ^ 59
def prefixEnd_4861994 : Nat := 4983230072969 + 3 ^ 40 * 4861994 * 2
def baseEnd_4861994 : Nat := 277393317919572851090567

theorem tailTrace_4861994 : CollatzResearch.WordTrace tailWord_4861994 prefixEnd_4861994 277393317919572851090567 := by
  unfold tailWord_4861994
  simp only [CollatzResearch.WordTrace]
  refine ⟨44332872386958393827944259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118220993031889050207851357 44332872386958393827944259)
  ·
    refine ⟨66499308580437590741916389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44332872386958393827944259 66499308580437590741916389)
    ·
      refine ⟨12468620358832048264109323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66499308580437590741916389 12468620358832048264109323)
      ·
        refine ⟨18702930538248072396163985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12468620358832048264109323 18702930538248072396163985)
        ·
          refine ⟨14027197903686054297122989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18702930538248072396163985 14027197903686054297122989)
          ·
            refine ⟨5260199213882270361421121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14027197903686054297122989 5260199213882270361421121)
            ·
              refine ⟨3945149410411702771065841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5260199213882270361421121 3945149410411702771065841)
              ·
                refine ⟨2958862057808777078299381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3945149410411702771065841 2958862057808777078299381)
                ·
                  refine ⟨277393317919572851090567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2958862057808777078299381 277393317919572851090567)
                  ·
                    rfl

theorem cell23_4861994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 5].length) (baseStart_4861994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4861994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4861994 prefixEnd_4861994 := by exact prefixLift 4861994
  have htrace : WordTrace (prefixWord ++ tailWord_4861994) baseStart_4861994 baseEnd_4861994 := by
    simpa [prefixWord, tailWord_4861994, baseEnd_4861994] using wordTrace_append hprefix tailTrace_4861994
  have hstable : (prefixWord ++ tailWord_4861994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4861994).length < 2 ^ (prefixWord ++ tailWord_4861994).sum := by decide
  have hdescent : baseEnd_4861994 < baseStart_4861994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4861994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862030 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_4862030 : Nat := 118140960795 + 4862030 * 2 ^ 59
def prefixEnd_4862030 : Nat := 4983230072969 + 3 ^ 40 * 4862030 * 2
def baseEnd_4862030 : Nat := 2496558346579717518964937

theorem tailTrace_4862030 : CollatzResearch.WordTrace tailWord_4862030 prefixEnd_4862030 2496558346579717518964937 := by
  unfold tailWord_4862030
  simp only [CollatzResearch.WordTrace]
  refine ⟨22166600321962894182510943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118221868383802102306725029 22166600321962894182510943)
  ·
    refine ⟨33249900482944341273766415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22166600321962894182510943 33249900482944341273766415)
    ·
      refine ⟨49874850724416511910649623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33249900482944341273766415 49874850724416511910649623)
      ·
        refine ⟨74812276086624767865974435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49874850724416511910649623 74812276086624767865974435)
        ·
          refine ⟨112218414129937151798961653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74812276086624767865974435 112218414129937151798961653)
          ·
            refine ⟨10520476324681607981152655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112218414129937151798961653 10520476324681607981152655)
            ·
              refine ⟨15780714487022411971728983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10520476324681607981152655 15780714487022411971728983)
              ·
                refine ⟨23671071730533617957593475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15780714487022411971728983 23671071730533617957593475)
                ·
                  refine ⟨35506607595800426936390213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23671071730533617957593475 35506607595800426936390213)
                  ·
                    refine ⟨6657488924212580050573165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35506607595800426936390213 6657488924212580050573165)
                    ·
                      refine ⟨2496558346579717518964937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6657488924212580050573165 2496558346579717518964937)
                      ·
                        rfl

theorem cell23_4862030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_4862030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862030 prefixEnd_4862030 := by exact prefixLift 4862030
  have htrace : WordTrace (prefixWord ++ tailWord_4862030) baseStart_4862030 baseEnd_4862030 := by
    simpa [prefixWord, tailWord_4862030, baseEnd_4862030] using wordTrace_append hprefix tailTrace_4862030
  have hstable : (prefixWord ++ tailWord_4862030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862030).length < 2 ^ (prefixWord ++ tailWord_4862030).sum := by decide
  have hdescent : baseEnd_4862030 < baseStart_4862030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862037 : List Nat := [1, 3, 2, 2, 1, 3, 1, 5, 1, 4]
def baseStart_4862037 : Nat := 118140960795 + 4862037 * 2 ^ 59
def prefixEnd_4862037 : Nat := 4983230072969 + 3 ^ 40 * 4862037 * 2
def baseEnd_4862037 : Nat := 832187313648099663859135

theorem tailTrace_4862037 : CollatzResearch.WordTrace tailWord_4862037 prefixEnd_4862037 832187313648099663859135 := by
  unfold tailWord_4862037
  simp only [CollatzResearch.WordTrace]
  refine ⟨177333057886677793655592365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118222038591118529103728243 177333057886677793655592365)
  ·
    refine ⟨66499896707504172620847137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177333057886677793655592365 66499896707504172620847137)
    ·
      refine ⟨49874922530628129465635353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66499896707504172620847137 49874922530628129465635353)
      ·
        refine ⟨37406191897971097099226515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49874922530628129465635353 37406191897971097099226515)
        ·
          refine ⟨56109287846956645648839773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37406191897971097099226515 56109287846956645648839773)
          ·
            refine ⟨21040982942608742118314915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56109287846956645648839773 21040982942608742118314915)
            ·
              refine ⟨31561474413913113177472373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21040982942608742118314915 31561474413913113177472373)
              ·
                refine ⟨2958888226304354360388035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31561474413913113177472373 2958888226304354360388035)
                ·
                  refine ⟨4438332339456531540582053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2958888226304354360388035 4438332339456531540582053)
                  ·
                    refine ⟨832187313648099663859135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4438332339456531540582053 832187313648099663859135)
                    ·
                      rfl

theorem cell23_4862037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_4862037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862037 prefixEnd_4862037 := by exact prefixLift 4862037
  have htrace : WordTrace (prefixWord ++ tailWord_4862037) baseStart_4862037 baseEnd_4862037 := by
    simpa [prefixWord, tailWord_4862037, baseEnd_4862037] using wordTrace_append hprefix tailTrace_4862037
  have hstable : (prefixWord ++ tailWord_4862037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862037).length < 2 ^ (prefixWord ++ tailWord_4862037).sum := by decide
  have hdescent : baseEnd_4862037 < baseStart_4862037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862053 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_4862053 : Nat := 118140960795 + 4862053 * 2 ^ 59
def prefixEnd_4862053 : Nat := 4983230072969 + 3 ^ 40 * 4862053 * 2
def baseEnd_4862053 : Nat := 2496570156634770928977331

theorem tailTrace_4862053 : CollatzResearch.WordTrace tailWord_4862053 prefixEnd_4862053 2496570156634770928977331 := by
  unfold tailWord_4862053
  simp only [CollatzResearch.WordTrace]
  refine ⟨177333641454619828388174813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118222427636413218925449875 177333641454619828388174813)
  ·
    refine ⟨66500115545482435645565555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177333641454619828388174813 66500115545482435645565555)
    ·
      refine ⟨99750173318223653468348333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66500115545482435645565555 99750173318223653468348333)
      ·
        refine ⟨37406314994333870050630625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99750173318223653468348333 37406314994333870050630625)
        ·
          refine ⟨28054736245750402537972969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37406314994333870050630625 28054736245750402537972969)
          ·
            refine ⟨21041052184312801903479727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28054736245750402537972969 21041052184312801903479727)
            ·
              refine ⟨31561578276469202855219591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21041052184312801903479727 31561578276469202855219591)
              ·
                refine ⟨47342367414703804282829387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31561578276469202855219591 47342367414703804282829387)
                ·
                  refine ⟨71013551122055706424244081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47342367414703804282829387 71013551122055706424244081)
                  ·
                    refine ⟨53260163341541779818183061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71013551122055706424244081 53260163341541779818183061)
                    ·
                      refine ⟨2496570156634770928977331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53260163341541779818183061 2496570156634770928977331)
                      ·
                        rfl

theorem cell23_4862053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_4862053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862053 prefixEnd_4862053 := by exact prefixLift 4862053
  have htrace : WordTrace (prefixWord ++ tailWord_4862053) baseStart_4862053 baseEnd_4862053 := by
    simpa [prefixWord, tailWord_4862053, baseEnd_4862053] using wordTrace_append hprefix tailTrace_4862053
  have hstable : (prefixWord ++ tailWord_4862053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862053).length < 2 ^ (prefixWord ++ tailWord_4862053).sum := by decide
  have hdescent : baseEnd_4862053 < baseStart_4862053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862077 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_4862077 : Nat := 118140960795 + 4862077 * 2 ^ 59
def prefixEnd_4862077 : Nat := 4983230072969 + 3 ^ 40 * 4862077 * 2
def baseEnd_4862077 : Nat := 2496582480170478835077221

theorem tailTrace_4862077 : CollatzResearch.WordTrace tailWord_4862077 prefixEnd_4862077 2496582480170478835077221 := by
  unfold tailWord_4862077
  simp only [CollatzResearch.WordTrace]
  refine ⟨177334516806532880487048485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118223011204355253658032323 177334516806532880487048485)
  ·
    refine ⟨33250221901224915091321591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177334516806532880487048485 33250221901224915091321591)
    ·
      refine ⟨49875332851837372636982387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33250221901224915091321591 49875332851837372636982387)
      ·
        refine ⟨74812999277756058955473581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49875332851837372636982387 74812999277756058955473581)
        ·
          refine ⟨28054874729158522108302593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74812999277756058955473581 28054874729158522108302593)
          ·
            refine ⟨21041156046868891581226945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28054874729158522108302593 21041156046868891581226945)
            ·
              refine ⟨15780867035151668685920209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21041156046868891581226945 15780867035151668685920209)
              ·
                refine ⟨11835650276363751514440157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15780867035151668685920209 11835650276363751514440157)
                ·
                  refine ⟨4438368853636406817915059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11835650276363751514440157 4438368853636406817915059)
                  ·
                    refine ⟨6657553280454610226872589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4438368853636406817915059 6657553280454610226872589)
                    ·
                      refine ⟨2496582480170478835077221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6657553280454610226872589 2496582480170478835077221)
                      ·
                        rfl

theorem cell23_4862077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_4862077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862077 prefixEnd_4862077 := by exact prefixLift 4862077
  have htrace : WordTrace (prefixWord ++ tailWord_4862077) baseStart_4862077 baseEnd_4862077 := by
    simpa [prefixWord, tailWord_4862077, baseEnd_4862077] using wordTrace_append hprefix tailTrace_4862077
  have hstable : (prefixWord ++ tailWord_4862077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862077).length < 2 ^ (prefixWord ++ tailWord_4862077).sum := by decide
  have hdescent : baseEnd_4862077 < baseStart_4862077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862104 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 2, 3, 2]
def baseStart_4862104 : Nat := 118140960795 + 4862104 * 2 ^ 59
def prefixEnd_4862104 : Nat := 4983230072969 + 3 ^ 40 * 4862104 * 2
def baseEnd_4862104 : Nat := 2496596344148150229439597

theorem tailTrace_4862104 : CollatzResearch.WordTrace tailWord_4862104 prefixEnd_4862104 2496596344148150229439597 := by
  unfold tailWord_4862104
  simp only [CollatzResearch.WordTrace]
  refine ⟨88667750788717532049140683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118223667718290042732187577 88667750788717532049140683)
  ·
    refine ⟨133001626183076298073711025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88667750788717532049140683 133001626183076298073711025)
    ·
      refine ⟨99751219637307223555283269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133001626183076298073711025 99751219637307223555283269)
      ·
        refine ⟨18703353681995104416615613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99751219637307223555283269 18703353681995104416615613)
        ·
          refine ⟨7013757630748164156230855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18703353681995104416615613 7013757630748164156230855)
          ·
            refine ⟨10520636446122246234346283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7013757630748164156230855 10520636446122246234346283)
            ·
              refine ⟨15780954669183369351519425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10520636446122246234346283 15780954669183369351519425)
              ·
                refine ⟨11835716001887527013639569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15780954669183369351519425 11835716001887527013639569)
                ·
                  refine ⟨8876787001415645260229677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11835716001887527013639569 8876787001415645260229677)
                  ·
                    refine ⟨3328795125530866972586129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8876787001415645260229677 3328795125530866972586129)
                    ·
                      refine ⟨2496596344148150229439597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328795125530866972586129 2496596344148150229439597)
                      ·
                        rfl

theorem cell23_4862104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_4862104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862104 prefixEnd_4862104 := by exact prefixLift 4862104
  have htrace : WordTrace (prefixWord ++ tailWord_4862104) baseStart_4862104 baseEnd_4862104 := by
    simpa [prefixWord, tailWord_4862104, baseEnd_4862104] using wordTrace_append hprefix tailTrace_4862104
  have hstable : (prefixWord ++ tailWord_4862104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862104).length < 2 ^ (prefixWord ++ tailWord_4862104).sum := by decide
  have hdescent : baseEnd_4862104 < baseStart_4862104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862130 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_4862130 : Nat := 118140960795 + 4862130 * 2 ^ 59
def prefixEnd_4862130 : Nat := 4983230072969 + 3 ^ 40 * 4862130 * 2
def baseEnd_4862130 : Nat := 2496609694645167127714477

theorem tailTrace_4862130 : CollatzResearch.WordTrace tailWord_4862130 prefixEnd_4862130 2496609694645167127714477 := by
  unfold tailWord_4862130
  simp only [CollatzResearch.WordTrace]
  refine ⟨44334112468835217634681961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118224299916893913692485229 44334112468835217634681961)
  ·
    refine ⟨33250584351626413226011471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44334112468835217634681961 33250584351626413226011471)
    ·
      refine ⟨49875876527439619839017207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33250584351626413226011471 49875876527439619839017207)
      ·
        refine ⟨74813814791159429758525811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49875876527439619839017207 74813814791159429758525811)
        ·
          refine ⟨112220722186739144637788717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74813814791159429758525811 112220722186739144637788717)
          ·
            refine ⟨42082770820027179239170769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112220722186739144637788717 42082770820027179239170769)
            ·
              refine ⟨31562078115020384429378077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42082770820027179239170769 31562078115020384429378077)
              ·
                refine ⟨11835779293132644161016779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31562078115020384429378077 11835779293132644161016779)
                ·
                  refine ⟨17753668939698966241525169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11835779293132644161016779 17753668939698966241525169)
                  ·
                    refine ⟨13315251704774224681143877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17753668939698966241525169 13315251704774224681143877)
                    ·
                      refine ⟨2496609694645167127714477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13315251704774224681143877 2496609694645167127714477)
                      ·
                        rfl

theorem cell23_4862130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_4862130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862130 prefixEnd_4862130 := by exact prefixLift 4862130
  have htrace : WordTrace (prefixWord ++ tailWord_4862130) baseStart_4862130 baseEnd_4862130 := by
    simpa [prefixWord, tailWord_4862130, baseEnd_4862130] using wordTrace_append hprefix tailTrace_4862130
  have hstable : (prefixWord ++ tailWord_4862130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862130).length < 2 ^ (prefixWord ++ tailWord_4862130).sum := by decide
  have hdescent : baseEnd_4862130 < baseStart_4862130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862154 : List Nat := [3, 1, 2, 1, 3, 1, 5, 1, 1, 2, 3]
def baseStart_4862154 : Nat := 118140960795 + 4862154 * 2 ^ 59
def prefixEnd_4862154 : Nat := 4983230072969 + 3 ^ 40 * 4862154 * 2
def baseEnd_4862154 : Nat := 2496622018180875033814367

theorem tailTrace_4862154 : CollatzResearch.WordTrace tailWord_4862154 prefixEnd_4862154 2496622018180875033814367 := by
  unfold tailWord_4862154
  simp only [CollatzResearch.WordTrace]
  refine ⟨44334331306813480659400379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118224883484835948425067677 44334331306813480659400379)
  ·
    refine ⟨66501496960220220989100569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44334331306813480659400379 66501496960220220989100569)
    ·
      refine ⟨49876122720165165741825427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66501496960220220989100569 49876122720165165741825427)
      ·
        refine ⟨74814184080247748612738141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49876122720165165741825427 74814184080247748612738141)
        ·
          refine ⟨28055319030092905729776803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74814184080247748612738141 28055319030092905729776803)
          ·
            refine ⟨42082978545139358594665205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28055319030092905729776803 42082978545139358594665205)
            ·
              refine ⟨3945279238606814868249863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42082978545139358594665205 3945279238606814868249863)
              ·
                refine ⟨5917918857910222302374795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3945279238606814868249863 5917918857910222302374795)
                ·
                  refine ⟨8876878286865333453562193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5917918857910222302374795 8876878286865333453562193)
                  ·
                    refine ⟨6657658715149000090171645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8876878286865333453562193 6657658715149000090171645)
                    ·
                      refine ⟨2496622018180875033814367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6657658715149000090171645 2496622018180875033814367)
                      ·
                        rfl

theorem cell23_4862154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_4862154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862154 prefixEnd_4862154 := by exact prefixLift 4862154
  have htrace : WordTrace (prefixWord ++ tailWord_4862154) baseStart_4862154 baseEnd_4862154 := by
    simpa [prefixWord, tailWord_4862154, baseEnd_4862154] using wordTrace_append hprefix tailTrace_4862154
  have hstable : (prefixWord ++ tailWord_4862154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862154).length < 2 ^ (prefixWord ++ tailWord_4862154).sum := by decide
  have hdescent : baseEnd_4862154 < baseStart_4862154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862168 : List Nat := [2, 1, 2, 2, 4, 1, 4, 2, 1, 2, 2]
def baseStart_4862168 : Nat := 118140960795 + 4862168 * 2 ^ 59
def prefixEnd_4862168 : Nat := 4983230072969 + 3 ^ 40 * 4862168 * 2
def baseEnd_4862168 : Nat := 2496629206910037979039303

theorem tailTrace_4862168 : CollatzResearch.WordTrace tailWord_4862168 prefixEnd_4862168 2496629206910037979039303 := by
  unfold tailWord_4862168
  simp only [CollatzResearch.WordTrace]
  refine ⟨88668917924601601514305579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118225223899468802019074105 88668917924601601514305579)
  ·
    refine ⟨133003376886902402271458369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88668917924601601514305579 133003376886902402271458369)
    ·
      refine ⟨99752532665176801703593777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133003376886902402271458369 99752532665176801703593777)
      ·
        refine ⟨74814399498882601277695333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99752532665176801703593777 74814399498882601277695333)
        ·
          refine ⟨14027699906040487739567875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74814399498882601277695333 14027699906040487739567875)
          ·
            refine ⟨21041549859060731609351813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14027699906040487739567875 21041549859060731609351813)
            ·
              refine ⟨3945290598573887176753465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21041549859060731609351813 3945290598573887176753465)
              ·
                refine ⟨2958967948930415382565099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3945290598573887176753465 2958967948930415382565099)
                ·
                  refine ⟨4438451923395623073847649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2958967948930415382565099 4438451923395623073847649)
                  ·
                    refine ⟨3328838942546717305385737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4438451923395623073847649 3328838942546717305385737)
                    ·
                      refine ⟨2496629206910037979039303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328838942546717305385737 2496629206910037979039303)
                      ·
                        rfl

theorem cell23_4862168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_4862168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862168 prefixEnd_4862168 := by exact prefixLift 4862168
  have htrace : WordTrace (prefixWord ++ tailWord_4862168) baseStart_4862168 baseEnd_4862168 := by
    simpa [prefixWord, tailWord_4862168, baseEnd_4862168] using wordTrace_append hprefix tailTrace_4862168
  have hstable : (prefixWord ++ tailWord_4862168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862168).length < 2 ^ (prefixWord ++ tailWord_4862168).sum := by decide
  have hdescent : baseEnd_4862168 < baseStart_4862168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862177 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 5, 3, 2]
def baseStart_4862177 : Nat := 118140960795 + 4862177 * 2 ^ 59
def prefixEnd_4862177 : Nat := 4983230072969 + 3 ^ 40 * 4862177 * 2
def baseEnd_4862177 : Nat := 2496633828235928443826761

theorem tailTrace_4862177 : CollatzResearch.WordTrace tailWord_4862177 prefixEnd_4862177 2496633828235928443826761 := by
  unfold tailWord_4862177
  simp only [CollatzResearch.WordTrace]
  refine ⟨177338164106170597565688785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118225442737447065043792523 177338164106170597565688785)
  ·
    refine ⟨133003623079627948174266589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177338164106170597565688785 133003623079627948174266589)
    ·
      refine ⟨49876358654860480565349971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133003623079627948174266589 49876358654860480565349971)
      ·
        refine ⟨74814537982290720848024957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49876358654860480565349971 74814537982290720848024957)
        ·
          refine ⟨28055451743359020318009359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74814537982290720848024957 28055451743359020318009359)
          ·
            refine ⟨42083177615038530477014039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28055451743359020318009359 42083177615038530477014039)
            ·
              refine ⟨63124766422557795715521059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42083177615038530477014039 63124766422557795715521059)
              ·
                refine ⟨94687149633836693573281589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63124766422557795715521059 94687149633836693573281589)
                ·
                  refine ⟨8876920278172190022495149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94687149633836693573281589 8876920278172190022495149)
                  ·
                    refine ⟨3328845104314571258435681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8876920278172190022495149 3328845104314571258435681)
                    ·
                      refine ⟨2496633828235928443826761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328845104314571258435681 2496633828235928443826761)
                      ·
                        rfl

theorem cell23_4862177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_4862177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862177 prefixEnd_4862177 := by exact prefixLift 4862177
  have htrace : WordTrace (prefixWord ++ tailWord_4862177) baseStart_4862177 baseEnd_4862177 := by
    simpa [prefixWord, tailWord_4862177, baseEnd_4862177] using wordTrace_append hprefix tailTrace_4862177
  have hstable : (prefixWord ++ tailWord_4862177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862177).length < 2 ^ (prefixWord ++ tailWord_4862177).sum := by decide
  have hdescent : baseEnd_4862177 < baseStart_4862177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862184 : List Nat := [2, 1, 4, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_4862184 : Nat := 118140960795 + 4862184 * 2 ^ 59
def prefixEnd_4862184 : Nat := 4983230072969 + 3 ^ 40 * 4862184 * 2
def baseEnd_4862184 : Nat := 2496637422600509916439229

theorem tailTrace_4862184 : CollatzResearch.WordTrace tailWord_4862184 prefixEnd_4862184 2496637422600509916439229 := by
  unfold tailWord_4862184
  simp only [CollatzResearch.WordTrace]
  refine ⟨88669209708572618880596803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118225612944763491840795737 88669209708572618880596803)
  ·
    refine ⟨133003814562858928320895205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88669209708572618880596803 133003814562858928320895205)
    ·
      refine ⟨24938215230536049060167851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133003814562858928320895205 24938215230536049060167851)
      ·
        refine ⟨37407322845804073590251777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24938215230536049060167851 37407322845804073590251777)
        ·
          refine ⟨28055492134353055192688833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37407322845804073590251777 28055492134353055192688833)
          ·
            refine ⟨21041619100764791394516625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28055492134353055192688833 21041619100764791394516625)
            ·
              refine ⟨15781214325573593545887469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21041619100764791394516625 15781214325573593545887469)
              ·
                refine ⟨5917955372090097579707801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15781214325573593545887469 5917955372090097579707801)
                ·
                  refine ⟨4438466529067573184780851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5917955372090097579707801 4438466529067573184780851)
                  ·
                    refine ⟨6657699793601359777171277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4438466529067573184780851 6657699793601359777171277)
                    ·
                      refine ⟨2496637422600509916439229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6657699793601359777171277 2496637422600509916439229)
                      ·
                        rfl

theorem cell23_4862184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_4862184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862184 prefixEnd_4862184 := by exact prefixLift 4862184
  have htrace : WordTrace (prefixWord ++ tailWord_4862184) baseStart_4862184 baseEnd_4862184 := by
    simpa [prefixWord, tailWord_4862184, baseEnd_4862184] using wordTrace_append hprefix tailTrace_4862184
  have hstable : (prefixWord ++ tailWord_4862184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862184).length < 2 ^ (prefixWord ++ tailWord_4862184).sum := by decide
  have hdescent : baseEnd_4862184 < baseStart_4862184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862190 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_4862190 : Nat := 118140960795 + 4862190 * 2 ^ 59
def prefixEnd_4862190 : Nat := 4983230072969 + 3 ^ 40 * 4862190 * 2
def baseEnd_4862190 : Nat := 2496640503484436892964201

theorem tailTrace_4862190 : CollatzResearch.WordTrace tailWord_4862190 prefixEnd_4862190 2496640503484436892964201 := by
  unfold tailWord_4862190
  simp only [CollatzResearch.WordTrace]
  refine ⟨22167329781890437598239003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118225758836749000523941349 22167329781890437598239003)
  ·
    refine ⟨33250994672835656397358505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22167329781890437598239003 33250994672835656397358505)
    ·
      refine ⟨24938246004626742298018879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33250994672835656397358505 24938246004626742298018879)
      ·
        refine ⟨37407369006940113447028319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24938246004626742298018879 37407369006940113447028319)
        ·
          refine ⟨56111053510410170170542479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37407369006940113447028319 56111053510410170170542479)
          ·
            refine ⟨84166580265615255255813719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56111053510410170170542479 84166580265615255255813719)
            ·
              refine ⟨126249870398422882883720579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84166580265615255255813719 126249870398422882883720579)
              ·
                refine ⟨189374805597634324325580869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126249870398422882883720579 189374805597634324325580869)
                ·
                  refine ⟨35507776049556435811046413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189374805597634324325580869 35507776049556435811046413)
                  ·
                    refine ⟨13315416018583663429142405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35507776049556435811046413 13315416018583663429142405)
                    ·
                      refine ⟨2496640503484436892964201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13315416018583663429142405 2496640503484436892964201)
                      ·
                        rfl

theorem cell23_4862190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_4862190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862190 prefixEnd_4862190 := by exact prefixLift 4862190
  have htrace : WordTrace (prefixWord ++ tailWord_4862190) baseStart_4862190 baseEnd_4862190 := by
    simpa [prefixWord, tailWord_4862190, baseEnd_4862190] using wordTrace_append hprefix tailTrace_4862190
  have hstable : (prefixWord ++ tailWord_4862190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862190).length < 2 ^ (prefixWord ++ tailWord_4862190).sum := by decide
  have hdescent : baseEnd_4862190 < baseStart_4862190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862194 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 3, 3, 2]
def baseStart_4862194 : Nat := 118140960795 + 4862194 * 2 ^ 59
def prefixEnd_4862194 : Nat := 4983230072969 + 3 ^ 40 * 4862194 * 2
def baseEnd_4862194 : Nat := 2496642557407054877314183

theorem tailTrace_4862194 : CollatzResearch.WordTrace tailWord_4862194 prefixEnd_4862194 2496642557407054877314183 := by
  unfold tailWord_4862194
  simp only [CollatzResearch.WordTrace]
  refine ⟨44334696036777252367264409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118225856098072672979371757 44334696036777252367264409)
  ·
    refine ⟨33251022027582939275448307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44334696036777252367264409 33251022027582939275448307)
    ·
      refine ⟨49876533041374408913172461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33251022027582939275448307 49876533041374408913172461)
      ·
        refine ⟨18703699890515403342439673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49876533041374408913172461 18703699890515403342439673)
        ·
          refine ⟨14027774917886552506829755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18703699890515403342439673 14027774917886552506829755)
          ·
            refine ⟨21041662376829828760244633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14027774917886552506829755 21041662376829828760244633)
            ·
              refine ⟨15781246782622371570183475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21041662376829828760244633 15781246782622371570183475)
              ·
                refine ⟨23671870173933557355275213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15781246782622371570183475 23671870173933557355275213)
                ·
                  refine ⟨8876951315225084008228205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23671870173933557355275213 8876951315225084008228205)
                  ·
                    refine ⟨3328856743209406503085577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8876951315225084008228205 3328856743209406503085577)
                    ·
                      refine ⟨2496642557407054877314183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328856743209406503085577 2496642557407054877314183)
                      ·
                        rfl

theorem cell23_4862194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_4862194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862194 prefixEnd_4862194 := by exact prefixLift 4862194
  have htrace : WordTrace (prefixWord ++ tailWord_4862194) baseStart_4862194 baseEnd_4862194 := by
    simpa [prefixWord, tailWord_4862194, baseEnd_4862194] using wordTrace_append hprefix tailTrace_4862194
  have hstable : (prefixWord ++ tailWord_4862194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862194).length < 2 ^ (prefixWord ++ tailWord_4862194).sum := by decide
  have hdescent : baseEnd_4862194 < baseStart_4862194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862207 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 1, 4, 2]
def baseStart_4862207 : Nat := 118140960795 + 4862207 * 2 ^ 59
def prefixEnd_4862207 : Nat := 4983230072969 + 3 ^ 40 * 4862207 * 2
def baseEnd_4862207 : Nat := 2496649232655563326451623

theorem tailTrace_4862207 : CollatzResearch.WordTrace tailWord_4862207 prefixEnd_4862207 2496649232655563326451623 := by
  unfold tailWord_4862207
  simp only [CollatzResearch.WordTrace]
  refine ⟨177339258296061912689280875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118226172197374608459520583 177339258296061912689280875)
  ·
    refine ⟨266008887444092869033921313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177339258296061912689280875 266008887444092869033921313)
    ·
      refine ⟨199506665583069651775440985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266008887444092869033921313 199506665583069651775440985)
      ·
        refine ⟨149629999187302238831580739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199506665583069651775440985 149629999187302238831580739)
        ·
          refine ⟨224444998780953358247371109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149629999187302238831580739 224444998780953358247371109)
          ·
            refine ⟨42083437271428754671382083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224444998780953358247371109 42083437271428754671382083)
            ·
              refine ⟨63125155907143132007073125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42083437271428754671382083 63125155907143132007073125)
              ·
                refine ⟨11835966732589337251326211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63125155907143132007073125 11835966732589337251326211)
                ·
                  refine ⟨17753950098884005876989317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11835966732589337251326211 17753950098884005876989317)
                  ·
                    refine ⟨3328865643540751101935497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17753950098884005876989317 3328865643540751101935497)
                    ·
                      refine ⟨2496649232655563326451623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328865643540751101935497 2496649232655563326451623)
                      ·
                        rfl

theorem cell23_4862207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 4, 2].length) (baseStart_4862207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862207 prefixEnd_4862207 := by exact prefixLift 4862207
  have htrace : WordTrace (prefixWord ++ tailWord_4862207) baseStart_4862207 baseEnd_4862207 := by
    simpa [prefixWord, tailWord_4862207, baseEnd_4862207] using wordTrace_append hprefix tailTrace_4862207
  have hstable : (prefixWord ++ tailWord_4862207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862207).length < 2 ^ (prefixWord ++ tailWord_4862207).sum := by decide
  have hdescent : baseEnd_4862207 < baseStart_4862207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862220 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_4862220 : Nat := 118140960795 + 4862220 * 2 ^ 59
def prefixEnd_4862220 : Nat := 4983230072969 + 3 ^ 40 * 4862220 * 2
def baseEnd_4862220 : Nat := 2496655907904071775589063

theorem tailTrace_4862220 : CollatzResearch.WordTrace tailWord_4862220 prefixEnd_4862220 2496655907904071775589063 := by
  unfold tailWord_4862220
  simp only [CollatzResearch.WordTrace]
  refine ⟨88669866222507407954752057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118226488296676543939669409 88669866222507407954752057)
  ·
    refine ⟨66502399666880555966064043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88669866222507407954752057 66502399666880555966064043)
    ·
      refine ⟨99753599500320833949096065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66502399666880555966064043 99753599500320833949096065)
      ·
        refine ⟨74815199625240625461822049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99753599500320833949096065 74815199625240625461822049)
        ·
          refine ⟨56111399718930469096366537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74815199625240625461822049 56111399718930469096366537)
          ·
            refine ⟨42083549789197851822274903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56111399718930469096366537 42083549789197851822274903)
            ·
              refine ⟨63125324683796777733412355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42083549789197851822274903 63125324683796777733412355)
              ·
                refine ⟨94687987025695166600118533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63125324683796777733412355 94687987025695166600118533)
                ·
                  refine ⟨17753997567317843737522225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94687987025695166600118533 17753997567317843737522225)
                  ·
                    refine ⟨13315498175488382803141669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17753997567317843737522225 13315498175488382803141669)
                    ·
                      refine ⟨2496655907904071775589063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13315498175488382803141669 2496655907904071775589063)
                      ·
                        rfl

theorem cell23_4862220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_4862220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862220 prefixEnd_4862220 := by exact prefixLift 4862220
  have htrace : WordTrace (prefixWord ++ tailWord_4862220) baseStart_4862220 baseEnd_4862220 := by
    simpa [prefixWord, tailWord_4862220, baseEnd_4862220] using wordTrace_append hprefix tailTrace_4862220
  have hstable : (prefixWord ++ tailWord_4862220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862220).length < 2 ^ (prefixWord ++ tailWord_4862220).sum := by decide
  have hdescent : baseEnd_4862220 < baseStart_4862220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862297 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 1, 6, 2]
def baseStart_4862297 : Nat := 118140960795 + 4862297 * 2 ^ 59
def prefixEnd_4862297 : Nat := 4983230072969 + 3 ^ 40 * 4862297 * 2
def baseEnd_4862297 : Nat := 2496695445914467974326209

theorem tailTrace_4862297 : CollatzResearch.WordTrace tailWord_4862297 prefixEnd_4862297 2496695445914467974326209 := by
  unfold tailWord_4862297
  simp only [CollatzResearch.WordTrace]
  refine ⟨177342540865735858060057145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118228360577157238706704763 177342540865735858060057145)
  ·
    refine ⟨133006905649301893545042859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177342540865735858060057145 133006905649301893545042859)
    ·
      refine ⟨199510358473952840317564289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133006905649301893545042859 199510358473952840317564289)
      ·
        refine ⟨149632768855464630238173217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199510358473952840317564289 149632768855464630238173217)
        ·
          refine ⟨112224576641598472678629913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149632768855464630238173217 112224576641598472678629913)
          ·
            refine ⟨84168432481198854508972435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112224576641598472678629913 84168432481198854508972435)
            ·
              refine ⟨126252648721798281763458653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84168432481198854508972435 126252648721798281763458653)
              ·
                refine ⟨47344743270674355661296995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126252648721798281763458653 47344743270674355661296995)
                ·
                  refine ⟨71017114906011533491945493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47344743270674355661296995 71017114906011533491945493)
                  ·
                    refine ⟨3328927261219290632434945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71017114906011533491945493 3328927261219290632434945)
                    ·
                      refine ⟨2496695445914467974326209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3328927261219290632434945 2496695445914467974326209)
                      ·
                        rfl

theorem cell23_4862297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 6, 2].length) (baseStart_4862297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862297 prefixEnd_4862297 := by exact prefixLift 4862297
  have htrace : WordTrace (prefixWord ++ tailWord_4862297) baseStart_4862297 baseEnd_4862297 := by
    simpa [prefixWord, tailWord_4862297, baseEnd_4862297] using wordTrace_append hprefix tailTrace_4862297
  have hstable : (prefixWord ++ tailWord_4862297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862297).length < 2 ^ (prefixWord ++ tailWord_4862297).sum := by decide
  have hdescent : baseEnd_4862297 < baseStart_4862297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862307 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 5, 4]
def baseStart_4862307 : Nat := 118140960795 + 4862307 * 2 ^ 59
def prefixEnd_4862307 : Nat := 4983230072969 + 3 ^ 40 * 4862307 * 2
def baseEnd_4862307 : Nat := 832233526907004311733721

theorem tailTrace_4862307 : CollatzResearch.WordTrace tailWord_4862307 prefixEnd_4862307 832233526907004311733721 := by
  unfold tailWord_4862307
  simp only [CollatzResearch.WordTrace]
  refine ⟨177342905595699629767921175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118228603730466419845280783 177342905595699629767921175)
  ·
    refine ⟨266014358393549444651881763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177342905595699629767921175 266014358393549444651881763)
    ·
      refine ⟨399021537590324166977822645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266014358393549444651881763 399021537590324166977822645)
      ·
        refine ⟨37408269149092890654170873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 399021537590324166977822645 37408269149092890654170873)
        ·
          refine ⟨28056201861819667990628155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37408269149092890654170873 28056201861819667990628155)
          ·
            refine ⟨42084302792729501985942233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28056201861819667990628155 42084302792729501985942233)
            ·
              refine ⟨31563227094547126489456675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42084302792729501985942233 31563227094547126489456675)
              ·
                refine ⟨47344840641820689734185013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31563227094547126489456675 47344840641820689734185013)
                ·
                  refine ⟨4438578810170689662579845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47344840641820689734185013 4438578810170689662579845)
                  ·
                    refine ⟨832233526907004311733721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4438578810170689662579845 832233526907004311733721)
                    ·
                      rfl

theorem cell23_4862307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 4].length) (baseStart_4862307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862307 prefixEnd_4862307 := by exact prefixLift 4862307
  have htrace : WordTrace (prefixWord ++ tailWord_4862307) baseStart_4862307 baseEnd_4862307 := by
    simpa [prefixWord, tailWord_4862307, baseEnd_4862307] using wordTrace_append hprefix tailTrace_4862307
  have hstable : (prefixWord ++ tailWord_4862307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862307).length < 2 ^ (prefixWord ++ tailWord_4862307).sum := by decide
  have hdescent : baseEnd_4862307 < baseStart_4862307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862314 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_4862314 : Nat := 118140960795 + 4862314 * 2 ^ 59
def prefixEnd_4862314 : Nat := 4983230072969 + 3 ^ 40 * 4862314 * 2
def baseEnd_4862314 : Nat := 2496704175085594407813631

theorem tailTrace_4862314 : CollatzResearch.WordTrace tailWord_4862314 prefixEnd_4862314 2496704175085594407813631 := by
  unfold tailWord_4862314
  simp only [CollatzResearch.WordTrace]
  refine ⟨44335790226668567490856499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118228773937782846642283997 44335790226668567490856499)
  ·
    refine ⟨66503685340002851236284749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44335790226668567490856499 66503685340002851236284749)
    ·
      refine ⟨24938882002501069213606781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66503685340002851236284749 24938882002501069213606781)
      ·
        refine ⟨9352080750937900955102543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24938882002501069213606781 9352080750937900955102543)
        ·
          refine ⟨14028121126406851432653815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9352080750937900955102543 14028121126406851432653815)
          ·
            refine ⟨21042181689610277148980723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14028121126406851432653815 21042181689610277148980723)
            ·
              refine ⟨31563272534415415723471085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21042181689610277148980723 31563272534415415723471085)
              ·
                refine ⟨11836227200405780896301657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31563272534415415723471085 11836227200405780896301657)
                ·
                  refine ⟨8877170400304335672226243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11836227200405780896301657 8877170400304335672226243)
                  ·
                    refine ⟨13315755600456503508339365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8877170400304335672226243 13315755600456503508339365)
                    ·
                      refine ⟨2496704175085594407813631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13315755600456503508339365 2496704175085594407813631)
                      ·
                        rfl

theorem cell23_4862314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_4862314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862314 prefixEnd_4862314 := by exact prefixLift 4862314
  have htrace : WordTrace (prefixWord ++ tailWord_4862314) baseStart_4862314 baseEnd_4862314 := by
    simpa [prefixWord, tailWord_4862314, baseEnd_4862314] using wordTrace_append hprefix tailTrace_4862314
  have hstable : (prefixWord ++ tailWord_4862314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862314).length < 2 ^ (prefixWord ++ tailWord_4862314).sum := by decide
  have hdescent : baseEnd_4862314 < baseStart_4862314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862367 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 3, 5]
def baseStart_4862367 : Nat := 118140960795 + 4862367 * 2 ^ 59
def prefixEnd_4862367 : Nat := 4983230072969 + 3 ^ 40 * 4862367 * 2
def baseEnd_4862367 : Nat := 832243796520094233483629

theorem tailTrace_4862367 : CollatzResearch.WordTrace tailWord_4862367 prefixEnd_4862367 832243796520094233483629 := by
  unfold tailWord_4862367
  simp only [CollatzResearch.WordTrace]
  refine ⟨177345093975482260015105355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118230062650321506676736903 177345093975482260015105355)
  ·
    refine ⟨266017640963223390022658033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177345093975482260015105355 266017640963223390022658033)
    ·
      refine ⟨199513230722417542516993525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266017640963223390022658033 199513230722417542516993525)
      ·
        refine ⟨18704365380226644610968143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 199513230722417542516993525 18704365380226644610968143)
        ·
          refine ⟨28056548070339966916452215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18704365380226644610968143 28056548070339966916452215)
          ·
            refine ⟨42084822105509950374678323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28056548070339966916452215 42084822105509950374678323)
            ·
              refine ⟨63127233158264925562017485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42084822105509950374678323 63127233158264925562017485)
              ·
                refine ⟨23672712434349347085756557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63127233158264925562017485 23672712434349347085756557)
                ·
                  refine ⟨8877267162881005157158709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23672712434349347085756557 8877267162881005157158709)
                  ·
                    refine ⟨832243796520094233483629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8877267162881005157158709 832243796520094233483629)
                    ·
                      rfl

theorem cell23_4862367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 5].length) (baseStart_4862367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862367 prefixEnd_4862367 := by exact prefixLift 4862367
  have htrace : WordTrace (prefixWord ++ tailWord_4862367) baseStart_4862367 baseEnd_4862367 := by
    simpa [prefixWord, tailWord_4862367, baseEnd_4862367] using wordTrace_append hprefix tailTrace_4862367
  have hstable : (prefixWord ++ tailWord_4862367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862367).length < 2 ^ (prefixWord ++ tailWord_4862367).sum := by decide
  have hdescent : baseEnd_4862367 < baseStart_4862367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862398 : List Nat := [4, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_4862398 : Nat := 118140960795 + 4862398 * 2 ^ 59
def prefixEnd_4862398 : Nat := 4983230072969 + 3 ^ 40 * 4862398 * 2
def baseEnd_4862398 : Nat := 2496747307460572079163245

theorem tailTrace_4862398 : CollatzResearch.WordTrace tailWord_4862398 prefixEnd_4862398 2496747307460572079163245 := by
  unfold tailWord_4862398
  simp only [CollatzResearch.WordTrace]
  refine ⟨22168278079796244038685481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118230816425579968206322565 22168278079796244038685481)
  ·
    refine ⟨16626208559847183029014111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22168278079796244038685481 16626208559847183029014111)
    ·
      refine ⟨24939312839770774543521167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16626208559847183029014111 24939312839770774543521167)
      ·
        refine ⟨37408969259656161815281751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24939312839770774543521167 37408969259656161815281751)
        ·
          refine ⟨56113453889484242722922627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37408969259656161815281751 56113453889484242722922627)
          ·
            refine ⟨84170180834226364084383941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56113453889484242722922627 84170180834226364084383941)
            ·
              refine ⟨15781908906417443265821989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84170180834226364084383941 15781908906417443265821989)
              ·
                refine ⟨2959107919953270612341623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15781908906417443265821989 2959107919953270612341623)
                ·
                  refine ⟨4438661879929905918512435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2959107919953270612341623 4438661879929905918512435)
                  ·
                    refine ⟨6657992819894858877768653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4438661879929905918512435 6657992819894858877768653)
                    ·
                      refine ⟨2496747307460572079163245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6657992819894858877768653 2496747307460572079163245)
                      ·
                        rfl

theorem cell23_4862398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_4862398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862398 prefixEnd_4862398 := by exact prefixLift 4862398
  have htrace : WordTrace (prefixWord ++ tailWord_4862398) baseStart_4862398 baseEnd_4862398 := by
    simpa [prefixWord, tailWord_4862398, baseEnd_4862398] using wordTrace_append hprefix tailTrace_4862398
  have hstable : (prefixWord ++ tailWord_4862398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862398).length < 2 ^ (prefixWord ++ tailWord_4862398).sum := by decide
  have hdescent : baseEnd_4862398 < baseStart_4862398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862407 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_4862407 : Nat := 118140960795 + 4862407 * 2 ^ 59
def prefixEnd_4862407 : Nat := 4983230072969 + 3 ^ 40 * 4862407 * 2
def baseEnd_4862407 : Nat := 2496751928786462543950703

theorem tailTrace_4862407 : CollatzResearch.WordTrace tailWord_4862407 prefixEnd_4862407 2496751928786462543950703 := by
  unfold tailWord_4862407
  simp only [CollatzResearch.WordTrace]
  refine ⟨177346552895337346846561475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118231035263558231231040983 177346552895337346846561475)
  ·
    refine ⟨266019829343006020269842213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177346552895337346846561475 266019829343006020269842213)
    ·
      refine ⟨49878718001813628800595415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266019829343006020269842213 49878718001813628800595415)
      ·
        refine ⟨74818077002720443200893123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49878718001813628800595415 74818077002720443200893123)
        ·
          refine ⟨112227115504080664801339685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74818077002720443200893123 112227115504080664801339685)
          ·
            refine ⟨21042584157015124650251191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112227115504080664801339685 21042584157015124650251191)
            ·
              refine ⟨31563876235522686975376787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21042584157015124650251191 31563876235522686975376787)
              ·
                refine ⟨47345814353284030463065181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31563876235522686975376787 47345814353284030463065181)
                ·
                  refine ⟨17754680382481511423649443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47345814353284030463065181 17754680382481511423649443)
                  ·
                    refine ⟨26632020573722267135474165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17754680382481511423649443 26632020573722267135474165)
                    ·
                      refine ⟨2496751928786462543950703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26632020573722267135474165 2496751928786462543950703)
                      ·
                        rfl

theorem cell23_4862407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_4862407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862407 prefixEnd_4862407 := by exact prefixLift 4862407
  have htrace : WordTrace (prefixWord ++ tailWord_4862407) baseStart_4862407 baseEnd_4862407 := by
    simpa [prefixWord, tailWord_4862407, baseEnd_4862407] using wordTrace_append hprefix tailTrace_4862407
  have hstable : (prefixWord ++ tailWord_4862407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862407).length < 2 ^ (prefixWord ++ tailWord_4862407).sum := by decide
  have hdescent : baseEnd_4862407 < baseStart_4862407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862418 : List Nat := [3, 2, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_4862418 : Nat := 118140960795 + 4862418 * 2 ^ 59
def prefixEnd_4862418 : Nat := 4983230072969 + 3 ^ 40 * 4862418 * 2
def baseEnd_4862418 : Nat := 832252525691220666971051

theorem tailTrace_4862418 : CollatzResearch.WordTrace tailWord_4862418 prefixEnd_4862418 832252525691220666971051 := by
  unfold tailWord_4862418
  simp only [CollatzResearch.WordTrace]
  refine ⟨44336738524574373931302977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118231302732198330483474605 44336738524574373931302977)
  ·
    refine ⟨33252553893430780448477233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44336738524574373931302977 33252553893430780448477233)
    ·
      refine ⟨24939415420073085336357925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33252553893430780448477233 24939415420073085336357925)
      ·
        refine ⟨4676140391263703500567111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24939415420073085336357925 4676140391263703500567111)
        ·
          refine ⟨7014210586895555250850667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4676140391263703500567111 7014210586895555250850667)
          ·
            refine ⟨10521315880343332876276001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7014210586895555250850667 10521315880343332876276001)
            ·
              refine ⟨7890986910257499657207001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10521315880343332876276001 7890986910257499657207001)
              ·
                refine ⟨5918240182693124742905251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7890986910257499657207001 5918240182693124742905251)
                ·
                  refine ⟨8877360274039687114357877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5918240182693124742905251 8877360274039687114357877)
                  ·
                    refine ⟨832252525691220666971051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8877360274039687114357877 832252525691220666971051)
                    ·
                      rfl

theorem cell23_4862418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_4862418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862418 prefixEnd_4862418 := by exact prefixLift 4862418
  have htrace : WordTrace (prefixWord ++ tailWord_4862418) baseStart_4862418 baseEnd_4862418 := by
    simpa [prefixWord, tailWord_4862418, baseEnd_4862418] using wordTrace_append hprefix tailTrace_4862418
  have hstable : (prefixWord ++ tailWord_4862418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862418).length < 2 ^ (prefixWord ++ tailWord_4862418).sum := by decide
  have hdescent : baseEnd_4862418 < baseStart_4862418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862421 : List Nat := [1, 3, 2, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_4862421 : Nat := 118140960795 + 4862421 * 2 ^ 59
def prefixEnd_4862421 : Nat := 4983230072969 + 3 ^ 40 * 4862421 * 2
def baseEnd_4862421 : Nat := 2496759117515625489175639

theorem tailTrace_4862421 : CollatzResearch.WordTrace tailWord_4862421 prefixEnd_4862421 2496759117515625489175639 := by
  unfold tailWord_4862421
  simp only [CollatzResearch.WordTrace]
  refine ⟨177347063517286627237571117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118231375678191084825047411 177347063517286627237571117)
  ·
    refine ⟨66505148818982485214089169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177347063517286627237571117 66505148818982485214089169)
    ·
      refine ⟨49878861614236863910566877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66505148818982485214089169 49878861614236863910566877)
      ·
        refine ⟨18704573105338823966462579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49878861614236863910566877 18704573105338823966462579)
        ·
          refine ⟨28056859658008235949693869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18704573105338823966462579 28056859658008235949693869)
          ·
            refine ⟨10521322371753088481135201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28056859658008235949693869 10521322371753088481135201)
            ·
              refine ⟨7890991778814816360851401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10521322371753088481135201 7890991778814816360851401)
              ·
                refine ⟨5918243834111112270638551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7890991778814816360851401 5918243834111112270638551)
                ·
                  refine ⟨8877365751166668405957827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5918243834111112270638551 8877365751166668405957827)
                  ·
                    refine ⟨13316048626750002608936741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8877365751166668405957827 13316048626750002608936741)
                    ·
                      refine ⟨2496759117515625489175639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13316048626750002608936741 2496759117515625489175639)
                      ·
                        rfl

theorem cell23_4862421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_4862421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862421 prefixEnd_4862421 := by exact prefixLift 4862421
  have htrace : WordTrace (prefixWord ++ tailWord_4862421) baseStart_4862421 baseEnd_4862421 := by
    simpa [prefixWord, tailWord_4862421, baseEnd_4862421] using wordTrace_append hprefix tailTrace_4862421
  have hstable : (prefixWord ++ tailWord_4862421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862421).length < 2 ^ (prefixWord ++ tailWord_4862421).sum := by decide
  have hdescent : baseEnd_4862421 < baseStart_4862421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862481 : List Nat := [1, 2, 2, 1, 1, 2, 2, 6, 1, 3, 2]
def baseStart_4862481 : Nat := 118140960795 + 4862481 * 2 ^ 59
def prefixEnd_4862481 : Nat := 4983230072969 + 3 ^ 40 * 4862481 * 2
def baseEnd_4862481 : Nat := 2496789926354895254425363

theorem tailTrace_4862481 : CollatzResearch.WordTrace tailWord_4862481 prefixEnd_4862481 2496789926354895254425363 := by
  unfold tailWord_4862481
  simp only [CollatzResearch.WordTrace]
  refine ⟨177349251897069257484755297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118232834598046171656503531 177349251897069257484755297)
  ·
    refine ⟨133011938922801943113566473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177349251897069257484755297 133011938922801943113566473)
    ·
      refine ⟨99758954192101457335174855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133011938922801943113566473 99758954192101457335174855)
      ·
        refine ⟨149638431288152186002762283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99758954192101457335174855 149638431288152186002762283)
        ·
          refine ⟨224457646932228279004143425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149638431288152186002762283 224457646932228279004143425)
          ·
            refine ⟨168343235199171209253107569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224457646932228279004143425 168343235199171209253107569)
            ·
              refine ⟨126257426399378406939830677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168343235199171209253107569 126257426399378406939830677)
              ·
                refine ⟨5918316862470862825304563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126257426399378406939830677 5918316862470862825304563)
                ·
                  refine ⟨8877475293706294237956845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5918316862470862825304563 8877475293706294237956845)
                  ·
                    refine ⟨3329053235139860339233817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8877475293706294237956845 3329053235139860339233817)
                    ·
                      refine ⟨2496789926354895254425363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3329053235139860339233817 2496789926354895254425363)
                      ·
                        rfl

theorem cell23_4862481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 3, 2].length) (baseStart_4862481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862481 prefixEnd_4862481 := by exact prefixLift 4862481
  have htrace : WordTrace (prefixWord ++ tailWord_4862481) baseStart_4862481 baseEnd_4862481 := by
    simpa [prefixWord, tailWord_4862481, baseEnd_4862481] using wordTrace_append hprefix tailTrace_4862481
  have hstable : (prefixWord ++ tailWord_4862481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862481).length < 2 ^ (prefixWord ++ tailWord_4862481).sum := by decide
  have hdescent : baseEnd_4862481 < baseStart_4862481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862507 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 4]
def baseStart_4862507 : Nat := 118140960795 + 4862507 * 2 ^ 59
def prefixEnd_4862507 : Nat := 4983230072969 + 3 ^ 40 * 4862507 * 2
def baseEnd_4862507 : Nat := 2496803276851912152700243

theorem tailTrace_4862507 : CollatzResearch.WordTrace tailWord_4862507 prefixEnd_4862507 2496803276851912152700243 := by
  unfold tailWord_4862507
  simp only [CollatzResearch.WordTrace]
  refine ⟨177350200194975063925201775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118233466796650042616801183 177350200194975063925201775)
  ·
    refine ⟨266025300292462595887802663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177350200194975063925201775 266025300292462595887802663)
    ·
      refine ⟨399037950438693893831703995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266025300292462595887802663 399037950438693893831703995)
      ·
        refine ⟨598556925658040840747555993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399037950438693893831703995 598556925658040840747555993)
        ·
          refine ⟨448917694243530630560666995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 598556925658040840747555993 448917694243530630560666995)
          ·
            refine ⟨673376541365295945841000493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448917694243530630560666995 673376541365295945841000493)
            ·
              refine ⟨252516203011985979690375185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 673376541365295945841000493 252516203011985979690375185)
              ·
                refine ⟨189387152258989484767781389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252516203011985979690375185 189387152258989484767781389)
                ·
                  refine ⟨71020182097121056787918021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189387152258989484767781389 71020182097121056787918021)
                  ·
                    refine ⟨13316284143210198147734629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71020182097121056787918021 13316284143210198147734629)
                    ·
                      refine ⟨2496803276851912152700243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13316284143210198147734629 2496803276851912152700243)
                      ·
                        rfl

theorem cell23_4862507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 4].length) (baseStart_4862507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862507 prefixEnd_4862507 := by exact prefixLift 4862507
  have htrace : WordTrace (prefixWord ++ tailWord_4862507) baseStart_4862507 baseEnd_4862507 := by
    simpa [prefixWord, tailWord_4862507, baseEnd_4862507] using wordTrace_append hprefix tailTrace_4862507
  have hstable : (prefixWord ++ tailWord_4862507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862507).length < 2 ^ (prefixWord ++ tailWord_4862507).sum := by decide
  have hdescent : baseEnd_4862507 < baseStart_4862507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862514 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_4862514 : Nat := 118140960795 + 4862514 * 2 ^ 59
def prefixEnd_4862514 : Nat := 4983230072969 + 3 ^ 40 * 4862514 * 2
def baseEnd_4862514 : Nat := 2496806871216493625312711

theorem tailTrace_4862514 : CollatzResearch.WordTrace tailWord_4862514 prefixEnd_4862514 2496806871216493625312711 := by
  unfold tailWord_4862514
  simp only [CollatzResearch.WordTrace]
  refine ⟨44337613876487426030176649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118233637003966469413804397 44337613876487426030176649)
  ·
    refine ⟨33253210407365569522632487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44337613876487426030176649 33253210407365569522632487)
    ·
      refine ⟨49879815611048354283948731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33253210407365569522632487 49879815611048354283948731)
      ·
        refine ⟨74819723416572531425923097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49879815611048354283948731 74819723416572531425923097)
        ·
          refine ⟨56114792562429398569442323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74819723416572531425923097 56114792562429398569442323)
          ·
            refine ⟨84172188843644097854163485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56114792562429398569442323 84172188843644097854163485)
            ·
              refine ⟨31564570816366536695311307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84172188843644097854163485 31564570816366536695311307)
              ·
                refine ⟨47346856224549805042966961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31564570816366536695311307 47346856224549805042966961)
                ·
                  refine ⟨35510142168412353782225221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47346856224549805042966961 35510142168412353782225221)
                  ·
                    refine ⟨6658151656577316334167229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35510142168412353782225221 6658151656577316334167229)
                    ·
                      refine ⟨2496806871216493625312711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6658151656577316334167229 2496806871216493625312711)
                      ·
                        rfl

theorem cell23_4862514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_4862514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862514 prefixEnd_4862514 := by exact prefixLift 4862514
  have htrace : WordTrace (prefixWord ++ tailWord_4862514) baseStart_4862514 baseEnd_4862514 := by
    simpa [prefixWord, tailWord_4862514, baseEnd_4862514] using wordTrace_append hprefix tailTrace_4862514
  have hstable : (prefixWord ++ tailWord_4862514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862514).length < 2 ^ (prefixWord ++ tailWord_4862514).sum := by decide
  have hdescent : baseEnd_4862514 < baseStart_4862514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862524 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_4862524 : Nat := 118140960795 + 4862524 * 2 ^ 59
def prefixEnd_4862524 : Nat := 4983230072969 + 3 ^ 40 * 4862524 * 2
def baseEnd_4862524 : Nat := 2496812006023038586187665

theorem tailTrace_4862524 : CollatzResearch.WordTrace tailWord_4862524 prefixEnd_4862524 2496812006023038586187665 := by
  unfold tailWord_4862524
  simp only [CollatzResearch.WordTrace]
  refine ⟨88675410117956737914285313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118233880157275650552380417 88675410117956737914285313)
  ·
    refine ⟨66506557588467553435713985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88675410117956737914285313 66506557588467553435713985)
    ·
      refine ⟨49879918191350665076785489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66506557588467553435713985 49879918191350665076785489)
      ·
        refine ⟨37409938643512998807589117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49879918191350665076785489 37409938643512998807589117)
        ·
          refine ⟨14028726991317374552845919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37409938643512998807589117 14028726991317374552845919)
          ·
            refine ⟨21043090486976061829268879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14028726991317374552845919 21043090486976061829268879)
            ·
              refine ⟨31564635730464092743903319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21043090486976061829268879 31564635730464092743903319)
              ·
                refine ⟨47346953595696139115854979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31564635730464092743903319 47346953595696139115854979)
                ·
                  refine ⟨71020430393544208673782469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47346953595696139115854979 71020430393544208673782469)
                  ·
                    refine ⟨13316330698789539126334213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71020430393544208673782469 13316330698789539126334213)
                    ·
                      refine ⟨2496812006023038586187665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13316330698789539126334213 2496812006023038586187665)
                      ·
                        rfl

theorem cell23_4862524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_4862524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862524 prefixEnd_4862524 := by exact prefixLift 4862524
  have htrace : WordTrace (prefixWord ++ tailWord_4862524) baseStart_4862524 baseEnd_4862524 := by
    simpa [prefixWord, tailWord_4862524, baseEnd_4862524] using wordTrace_append hprefix tailTrace_4862524
  have hstable : (prefixWord ++ tailWord_4862524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862524).length < 2 ^ (prefixWord ++ tailWord_4862524).sum := by decide
  have hdescent : baseEnd_4862524 < baseStart_4862524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862528 : List Nat := [2, 1, 1, 2, 2, 2, 4, 3, 2, 2, 2]
def baseStart_4862528 : Nat := 118140960795 + 4862528 * 2 ^ 59
def prefixEnd_4862528 : Nat := 4983230072969 + 3 ^ 40 * 4862528 * 2
def baseEnd_4862528 : Nat := 2496814059945656570537647

theorem tailTrace_4862528 : CollatzResearch.WordTrace tailWord_4862528 prefixEnd_4862528 2496814059945656570537647 := by
  unfold tailWord_4862528
  simp only [CollatzResearch.WordTrace]
  refine ⟨88675483063949492255858119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118233977418599323007810825 88675483063949492255858119)
  ·
    refine ⟨133013224595924238383787179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88675483063949492255858119 133013224595924238383787179)
    ·
      refine ⟨199519836893886357575680769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133013224595924238383787179 199519836893886357575680769)
      ·
        refine ⟨149639877670414768181760577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199519836893886357575680769 149639877670414768181760577)
        ·
          refine ⟨112229908252811076136320433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149639877670414768181760577 112229908252811076136320433)
          ·
            refine ⟨84172431189608307102240325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112229908252811076136320433 84172431189608307102240325)
            ·
              refine ⟨15782330848051557581670061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84172431189608307102240325 15782330848051557581670061)
              ·
                refine ⟨5918374068019334093126273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15782330848051557581670061 5918374068019334093126273)
                ·
                  refine ⟨4438780551014500569844705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5918374068019334093126273 4438780551014500569844705)
                  ·
                    refine ⟨3329085413260875427383529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4438780551014500569844705 3329085413260875427383529)
                    ·
                      refine ⟨2496814059945656570537647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3329085413260875427383529 2496814059945656570537647)
                      ·
                        rfl

theorem cell23_4862528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 2, 2, 2].length) (baseStart_4862528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862528 prefixEnd_4862528 := by exact prefixLift 4862528
  have htrace : WordTrace (prefixWord ++ tailWord_4862528) baseStart_4862528 baseEnd_4862528 := by
    simpa [prefixWord, tailWord_4862528, baseEnd_4862528] using wordTrace_append hprefix tailTrace_4862528
  have hstable : (prefixWord ++ tailWord_4862528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862528).length < 2 ^ (prefixWord ++ tailWord_4862528).sum := by decide
  have hdescent : baseEnd_4862528 < baseStart_4862528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862551 : List Nat := [1, 1, 3, 2, 2, 2, 4, 3, 5]
def baseStart_4862551 : Nat := 118140960795 + 4862551 * 2 ^ 59
def prefixEnd_4862551 : Nat := 4983230072969 + 3 ^ 40 * 4862551 * 2
def baseEnd_4862551 : Nat := 277425096666745553394449

theorem tailTrace_4862551 : CollatzResearch.WordTrace tailWord_4862551 prefixEnd_4862551 277425096666745553394449 := by
  unfold tailWord_4862551
  simp only [CollatzResearch.WordTrace]
  refine ⟨177351805006815659439803507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118234536671210439626535671 177351805006815659439803507)
  ·
    refine ⟨266027707510223489159705261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177351805006815659439803507 266027707510223489159705261)
    ·
      refine ⟨99760390316333808434889473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266027707510223489159705261 99760390316333808434889473)
      ·
        refine ⟨74820292737250356326167105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99760390316333808434889473 74820292737250356326167105)
        ·
          refine ⟨56115219552937767244625329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74820292737250356326167105 56115219552937767244625329)
          ·
            refine ⟨42086414664703325433468997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56115219552937767244625329 42086414664703325433468997)
            ·
              refine ⟨7891202749631873518775437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42086414664703325433468997 7891202749631873518775437)
              ·
                refine ⟨2959201031111952569540789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7891202749631873518775437 2959201031111952569540789)
                ·
                  refine ⟨277425096666745553394449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2959201031111952569540789 277425096666745553394449)
                  ·
                    rfl

theorem cell23_4862551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 5].length) (baseStart_4862551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862551 prefixEnd_4862551 := by exact prefixLift 4862551
  have htrace : WordTrace (prefixWord ++ tailWord_4862551) baseStart_4862551 baseEnd_4862551 := by
    simpa [prefixWord, tailWord_4862551, baseEnd_4862551] using wordTrace_append hprefix tailTrace_4862551
  have hstable : (prefixWord ++ tailWord_4862551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862551).length < 2 ^ (prefixWord ++ tailWord_4862551).sum := by decide
  have hdescent : baseEnd_4862551 < baseStart_4862551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862562 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_4862562 : Nat := 118140960795 + 4862562 * 2 ^ 59
def prefixEnd_4862562 : Nat := 4983230072969 + 3 ^ 40 * 4862562 * 2
def baseEnd_4862562 : Nat := 2496831518287909437512491

theorem tailTrace_4862562 : CollatzResearch.WordTrace tailWord_4862562 prefixEnd_4862562 2496831518287909437512491 := by
  unfold tailWord_4862562
  simp only [CollatzResearch.WordTrace]
  refine ⟨44338051552443952079613485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118234804139850538878969293 44338051552443952079613485)
  ·
    refine ⟨16626769332166482029855057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44338051552443952079613485 16626769332166482029855057)
    ·
      refine ⟨12470076999124861522391293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16626769332166482029855057 12470076999124861522391293)
      ·
        refine ⟨4676278874671823070896735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12470076999124861522391293 4676278874671823070896735)
        ·
          refine ⟨7014418312007734606345103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4676278874671823070896735 7014418312007734606345103)
          ·
            refine ⟨10521627468011601909517655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7014418312007734606345103 10521627468011601909517655)
            ·
              refine ⟨15782441202017402864276483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10521627468011601909517655 15782441202017402864276483)
              ·
                refine ⟨23673661803026104296414725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15782441202017402864276483 23673661803026104296414725)
                ·
                  refine ⟨4438811588067394555577761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23673661803026104296414725 4438811588067394555577761)
                  ·
                    refine ⟨3329108691050545916683321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4438811588067394555577761 3329108691050545916683321)
                    ·
                      refine ⟨2496831518287909437512491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3329108691050545916683321 2496831518287909437512491)
                      ·
                        rfl

theorem cell23_4862562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_4862562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862562 prefixEnd_4862562 := by exact prefixLift 4862562
  have htrace : WordTrace (prefixWord ++ tailWord_4862562) baseStart_4862562 baseEnd_4862562 := by
    simpa [prefixWord, tailWord_4862562, baseEnd_4862562] using wordTrace_append hprefix tailTrace_4862562
  have hstable : (prefixWord ++ tailWord_4862562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862562).length < 2 ^ (prefixWord ++ tailWord_4862562).sum := by decide
  have hdescent : baseEnd_4862562 < baseStart_4862562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862564 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_4862564 : Nat := 118140960795 + 4862564 * 2 ^ 59
def prefixEnd_4862564 : Nat := 4983230072969 + 3 ^ 40 * 4862564 * 2
def baseEnd_4862564 : Nat := 832277515083072809895827

theorem tailTrace_4862564 : CollatzResearch.WordTrace tailWord_4862564 prefixEnd_4862564 832277515083072809895827 := by
  unfold tailWord_4862564
  simp only [CollatzResearch.WordTrace]
  refine ⟨88676139577884281330013373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118234852770512375106684497 88676139577884281330013373)
  ·
    refine ⟨33253552341706605498755015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88676139577884281330013373 33253552341706605498755015)
    ·
      refine ⟨49880328512559908248132523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33253552341706605498755015 49880328512559908248132523)
      ·
        refine ⟨74820492768839862372198785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49880328512559908248132523 74820492768839862372198785)
        ·
          refine ⟨56115369576629896779149089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74820492768839862372198785 56115369576629896779149089)
          ·
            refine ⟨42086527182472422584361817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56115369576629896779149089 42086527182472422584361817)
            ·
              refine ⟨31564895386854316938271363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42086527182472422584361817 31564895386854316938271363)
              ·
                refine ⟨47347343080281475407407045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31564895386854316938271363 47347343080281475407407045)
                ·
                  refine ⟨8877626827552776638888821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47347343080281475407407045 8877626827552776638888821)
                  ·
                    refine ⟨832277515083072809895827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8877626827552776638888821 832277515083072809895827)
                    ·
                      rfl

theorem cell23_4862564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_4862564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862564 prefixEnd_4862564 := by exact prefixLift 4862564
  have htrace : WordTrace (prefixWord ++ tailWord_4862564) baseStart_4862564 baseEnd_4862564 := by
    simpa [prefixWord, tailWord_4862564, baseEnd_4862564] using wordTrace_append hprefix tailTrace_4862564
  have hstable : (prefixWord ++ tailWord_4862564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862564).length < 2 ^ (prefixWord ++ tailWord_4862564).sum := by decide
  have hdescent : baseEnd_4862564 < baseStart_4862564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862584 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_4862584 : Nat := 118140960795 + 4862584 * 2 ^ 59
def prefixEnd_4862584 : Nat := 4983230072969 + 3 ^ 40 * 4862584 * 2
def baseEnd_4862584 : Nat := 2496842814862308351437389

theorem tailTrace_4862584 : CollatzResearch.WordTrace tailWord_4862584 prefixEnd_4862584 2496842814862308351437389 := by
  unfold tailWord_4862584
  simp only [CollatzResearch.WordTrace]
  refine ⟨88676504307848053037877403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118235339077130737383836537 88676504307848053037877403)
  ·
    refine ⟨133014756461772079556816105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88676504307848053037877403 133014756461772079556816105)
    ·
      refine ⟨99761067346329059667612079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133014756461772079556816105 99761067346329059667612079)
      ·
        refine ⟨149641601019493589501418119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99761067346329059667612079 149641601019493589501418119)
        ·
          refine ⟨224462401529240384252127179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149641601019493589501418119 224462401529240384252127179)
          ·
            refine ⟨336693602293860576378190769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224462401529240384252127179 336693602293860576378190769)
            ·
              refine ⟨252520201720395432283643077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336693602293860576378190769 252520201720395432283643077)
              ·
                refine ⟨47347537822574143553183077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252520201720395432283643077 47347537822574143553183077)
                ·
                  refine ⟨8877663341732651916221827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47347537822574143553183077 8877663341732651916221827)
                  ·
                    refine ⟨13316495012598977874332741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8877663341732651916221827 13316495012598977874332741)
                    ·
                      refine ⟨2496842814862308351437389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13316495012598977874332741 2496842814862308351437389)
                      ·
                        rfl

theorem cell23_4862584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_4862584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862584 prefixEnd_4862584 := by exact prefixLift 4862584
  have htrace : WordTrace (prefixWord ++ tailWord_4862584) baseStart_4862584 baseEnd_4862584 := by
    simpa [prefixWord, tailWord_4862584, baseEnd_4862584] using wordTrace_append hprefix tailTrace_4862584
  have hstable : (prefixWord ++ tailWord_4862584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862584).length < 2 ^ (prefixWord ++ tailWord_4862584).sum := by decide
  have hdescent : baseEnd_4862584 < baseStart_4862584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862621 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_4862621 : Nat := 118140960795 + 4862621 * 2 ^ 59
def prefixEnd_4862621 : Nat := 4983230072969 + 3 ^ 40 * 4862621 * 2
def baseEnd_4862621 : Nat := 2496861813646524706674719

theorem tailTrace_4862621 : CollatzResearch.WordTrace tailWord_4862621 prefixEnd_4862621 2496861813646524706674719 := by
  unfold tailWord_4862621
  simp only [CollatzResearch.WordTrace]
  refine ⟨177354358116562061394851717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118236238744374707596567811 177354358116562061394851717)
  ·
    refine ⟨33253942146855386511534697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177354358116562061394851717 33253942146855386511534697)
    ·
      refine ⟨24940456610141539883651023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33253942146855386511534697 24940456610141539883651023)
      ·
        refine ⟨37410684915212309825476535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24940456610141539883651023 37410684915212309825476535)
        ·
          refine ⟨56116027372818464738214803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37410684915212309825476535 56116027372818464738214803)
          ·
            refine ⟨84174041059227697107322205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56116027372818464738214803 84174041059227697107322205)
            ·
              refine ⟨31565265397210386415245827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84174041059227697107322205 31565265397210386415245827)
              ·
                refine ⟨47347898095815579622868741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31565265397210386415245827 47347898095815579622868741)
                ·
                  refine ⟨8877730892965421179287889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47347898095815579622868741 8877730892965421179287889)
                  ·
                    refine ⟨6658298169724065884465917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8877730892965421179287889 6658298169724065884465917)
                    ·
                      refine ⟨2496861813646524706674719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6658298169724065884465917 2496861813646524706674719)
                      ·
                        rfl

theorem cell23_4862621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_4862621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862621 prefixEnd_4862621 := by exact prefixLift 4862621
  have htrace : WordTrace (prefixWord ++ tailWord_4862621) baseStart_4862621 baseEnd_4862621 := by
    simpa [prefixWord, tailWord_4862621, baseEnd_4862621] using wordTrace_append hprefix tailTrace_4862621
  have hstable : (prefixWord ++ tailWord_4862621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862621).length < 2 ^ (prefixWord ++ tailWord_4862621).sum := by decide
  have hdescent : baseEnd_4862621 < baseStart_4862621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862714 : List Nat := [3, 1, 1, 1, 1, 3, 2, 11]
def baseStart_4862714 : Nat := 118140960795 + 4862714 * 2 ^ 59
def prefixEnd_4862714 : Nat := 4983230072969 + 3 ^ 40 * 4862714 * 2
def baseEnd_4862714 : Nat := 92478132123977512696733

theorem tailTrace_4862714 : CollatzResearch.WordTrace tailWord_4862714 prefixEnd_4862714 92478132123977512696733 := by
  unfold tailWord_4862714
  simp only [CollatzResearch.WordTrace]
  refine ⟨44339437526306284569496799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118238500070150092185324797 44339437526306284569496799)
  ·
    refine ⟨66509156289459426854245199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44339437526306284569496799 66509156289459426854245199)
    ·
      refine ⟨99763734434189140281367799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66509156289459426854245199 99763734434189140281367799)
      ·
        refine ⟨149645601651283710422051699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99763734434189140281367799 149645601651283710422051699)
        ·
          refine ⟨224468402476925565633077549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149645601651283710422051699 224468402476925565633077549)
          ·
            refine ⟨84175650928847087112404081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224468402476925565633077549 84175650928847087112404081)
            ·
              refine ⟨63131738196635315334303061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84175650928847087112404081 63131738196635315334303061)
              ·
                refine ⟨92478132123977512696733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 63131738196635315334303061 92478132123977512696733)
                ·
                  rfl

theorem cell23_4862714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 11].length) (baseStart_4862714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862714 prefixEnd_4862714 := by exact prefixLift 4862714
  have htrace : WordTrace (prefixWord ++ tailWord_4862714) baseStart_4862714 baseEnd_4862714 := by
    simpa [prefixWord, tailWord_4862714, baseEnd_4862714] using wordTrace_append hprefix tailTrace_4862714
  have hstable : (prefixWord ++ tailWord_4862714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862714).length < 2 ^ (prefixWord ++ tailWord_4862714).sum := by decide
  have hdescent : baseEnd_4862714 < baseStart_4862714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862718 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_4862718 : Nat := 118140960795 + 4862718 * 2 ^ 59
def prefixEnd_4862718 : Nat := 4983230072969 + 3 ^ 40 * 4862718 * 2
def baseEnd_4862718 : Nat := 832303873756670275720591

theorem tailTrace_4862718 : CollatzResearch.WordTrace tailWord_4862718 prefixEnd_4862718 832303873756670275720591 := by
  unfold tailWord_4862718
  simp only [CollatzResearch.WordTrace]
  refine ⟨22169736999651330870141601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118238597331473764640755205 22169736999651330870141601)
  ·
    refine ⟨16627302749738498152606201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22169736999651330870141601 16627302749738498152606201)
    ·
      refine ⟨12470477062303873614454651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16627302749738498152606201 12470477062303873614454651)
      ·
        refine ⟨18705715593455810421681977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12470477062303873614454651 18705715593455810421681977)
        ·
          refine ⟨14029286695091857816261483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18705715593455810421681977 14029286695091857816261483)
          ·
            refine ⟨21043930042637786724392225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14029286695091857816261483 21043930042637786724392225)
            ·
              refine ⟨15782947531978340043294169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21043930042637786724392225 15782947531978340043294169)
              ·
                refine ⟨11837210648983755032470627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15782947531978340043294169 11837210648983755032470627)
                ·
                  refine ⟨17755815973475632548705941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11837210648983755032470627 17755815973475632548705941)
                  ·
                    refine ⟨832303873756670275720591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17755815973475632548705941 832303873756670275720591)
                    ·
                      rfl

theorem cell23_4862718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_4862718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862718 prefixEnd_4862718 := by exact prefixLift 4862718
  have htrace : WordTrace (prefixWord ++ tailWord_4862718) baseStart_4862718 baseEnd_4862718 := by
    simpa [prefixWord, tailWord_4862718, baseEnd_4862718] using wordTrace_append hprefix tailTrace_4862718
  have hstable : (prefixWord ++ tailWord_4862718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862718).length < 2 ^ (prefixWord ++ tailWord_4862718).sum := by decide
  have hdescent : baseEnd_4862718 < baseStart_4862718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862722 : List Nat := [3, 4, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_4862722 : Nat := 118140960795 + 4862722 * 2 ^ 59
def prefixEnd_4862722 : Nat := 4983230072969 + 3 ^ 40 * 4862722 * 2
def baseEnd_4862722 : Nat := 832304558397542937170585

theorem tailTrace_4862722 : CollatzResearch.WordTrace tailWord_4862722 prefixEnd_4862722 832304558397542937170585 := by
  unfold tailWord_4862722
  simp only [CollatzResearch.WordTrace]
  refine ⟨44339510472299038911069605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118238694592797437096185613 44339510472299038911069605)
  ·
    refine ⟨8313658213556069795825551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44339510472299038911069605 8313658213556069795825551)
    ·
      refine ⟨12470487320334104693738327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8313658213556069795825551 12470487320334104693738327)
      ·
        refine ⟨18705730980501157040607491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12470487320334104693738327 18705730980501157040607491)
        ·
          refine ⟨28058596470751735560911237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18705730980501157040607491 28058596470751735560911237)
          ·
            refine ⟨5260986838265950417670857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28058596470751735560911237 5260986838265950417670857)
            ·
              refine ⟨3945740128699462813253143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5260986838265950417670857 3945740128699462813253143)
              ·
                refine ⟨5918610193049194219879715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3945740128699462813253143 5918610193049194219879715)
                ·
                  refine ⟨8877915289573791329819573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5918610193049194219879715 8877915289573791329819573)
                  ·
                    refine ⟨832304558397542937170585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8877915289573791329819573 832304558397542937170585)
                    ·
                      rfl

theorem cell23_4862722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_4862722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862722 prefixEnd_4862722 := by exact prefixLift 4862722
  have htrace : WordTrace (prefixWord ++ tailWord_4862722) baseStart_4862722 baseEnd_4862722 := by
    simpa [prefixWord, tailWord_4862722, baseEnd_4862722] using wordTrace_append hprefix tailTrace_4862722
  have hstable : (prefixWord ++ tailWord_4862722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862722).length < 2 ^ (prefixWord ++ tailWord_4862722).sum := by decide
  have hdescent : baseEnd_4862722 < baseStart_4862722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862765 : List Nat := [1, 5, 3, 2, 1, 1, 1, 9]
def baseStart_4862765 : Nat := 118140960795 + 4862765 * 2 ^ 59
def prefixEnd_4862765 : Nat := 4983230072969 + 3 ^ 40 * 4862765 * 2
def baseEnd_4862765 : Nat := 92479102031880449750891

theorem tailTrace_4862765 : CollatzResearch.WordTrace tailWord_4862765 prefixEnd_4862765 92479102031880449750891 := by
  unfold tailWord_4862765
  simp only [CollatzResearch.WordTrace]
  refine ⟨177359610228040373988093749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118239740152026915992062499 177359610228040373988093749)
  ·
    refine ⟨16627463458878785061383789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177359610228040373988093749 16627463458878785061383789)
    ·
      refine ⟨6235298797079544398018921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16627463458878785061383789 6235298797079544398018921)
      ·
        refine ⟨4676474097809658298514191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6235298797079544398018921 4676474097809658298514191)
        ·
          refine ⟨7014711146714487447771287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4676474097809658298514191 7014711146714487447771287)
          ·
            refine ⟨10522066720071731171656931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7014711146714487447771287 10522066720071731171656931)
            ·
              refine ⟨15783100080107596757485397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10522066720071731171656931 15783100080107596757485397)
              ·
                refine ⟨92479102031880449750891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15783100080107596757485397 92479102031880449750891)
                ·
                  rfl

theorem cell23_4862765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 9].length) (baseStart_4862765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862765 prefixEnd_4862765 := by exact prefixLift 4862765
  have htrace : WordTrace (prefixWord ++ tailWord_4862765) baseStart_4862765 baseEnd_4862765 := by
    simpa [prefixWord, tailWord_4862765, baseEnd_4862765] using wordTrace_append hprefix tailTrace_4862765
  have hstable : (prefixWord ++ tailWord_4862765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862765).length < 2 ^ (prefixWord ++ tailWord_4862765).sum := by decide
  have hdescent : baseEnd_4862765 < baseStart_4862765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862768 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 3, 3, 2]
def baseStart_4862768 : Nat := 118140960795 + 4862768 * 2 ^ 59
def prefixEnd_4862768 : Nat := 4983230072969 + 3 ^ 40 * 4862768 * 2
def baseEnd_4862768 : Nat := 2496937295302735631536543

theorem tailTrace_4862768 : CollatzResearch.WordTrace tailWord_4862768 prefixEnd_4862768 2496937295302735631536543 := by
  unfold tailWord_4862768
  simp only [CollatzResearch.WordTrace]
  refine ⟨88679859823514752750226479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118239813098019670333635305 88679859823514752750226479)
  ·
    refine ⟨133019789735272129125339719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88679859823514752750226479 133019789735272129125339719)
    ·
      refine ⟨199529684602908193688009579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133019789735272129125339719 199529684602908193688009579)
      ·
        refine ⟨299294526904362290532014369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199529684602908193688009579 299294526904362290532014369)
        ·
          refine ⟨224470895178271717899010777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299294526904362290532014369 224470895178271717899010777)
          ·
            refine ⟨168353171383703788424258083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224470895178271717899010777 168353171383703788424258083)
            ·
              refine ⟨252529757075555682636387125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168353171383703788424258083 252529757075555682636387125)
              ·
                refine ⟨23674664725833345247161293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 252529757075555682636387125 23674664725833345247161293)
                ·
                  refine ⟨8877999272187504467685485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23674664725833345247161293 8877999272187504467685485)
                  ·
                    refine ⟨3329249727070314175382057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8877999272187504467685485 3329249727070314175382057)
                    ·
                      refine ⟨2496937295302735631536543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3329249727070314175382057 2496937295302735631536543)
                      ·
                        rfl

theorem cell23_4862768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3, 3, 2].length) (baseStart_4862768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862768 prefixEnd_4862768 := by exact prefixLift 4862768
  have htrace : WordTrace (prefixWord ++ tailWord_4862768) baseStart_4862768 baseEnd_4862768 := by
    simpa [prefixWord, tailWord_4862768, baseEnd_4862768] using wordTrace_append hprefix tailTrace_4862768
  have hstable : (prefixWord ++ tailWord_4862768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862768).length < 2 ^ (prefixWord ++ tailWord_4862768).sum := by decide
  have hdescent : baseEnd_4862768 < baseStart_4862768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862771 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 5]
def baseStart_4862771 : Nat := 118140960795 + 4862771 * 2 ^ 59
def prefixEnd_4862771 : Nat := 4983230072969 + 3 ^ 40 * 4862771 * 2
def baseEnd_4862771 : Nat := 2496938835744699119799029

theorem tailTrace_4862771 : CollatzResearch.WordTrace tailWord_4862771 prefixEnd_4862771 2496938835744699119799029 := by
  unfold tailWord_4862771
  simp only [CollatzResearch.WordTrace]
  refine ⟨177359829066018637012812167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118239886044012424675208111 177359829066018637012812167)
  ·
    refine ⟨266039743599027955519218251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177359829066018637012812167 266039743599027955519218251)
    ·
      refine ⟨399059615398541933278827377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266039743599027955519218251 399059615398541933278827377)
      ·
        refine ⟨299294711548906449959120533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399059615398541933278827377 299294711548906449959120533)
        ·
          refine ⟨14029439603854989841833775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 299294711548906449959120533 14029439603854989841833775)
          ·
            refine ⟨21044159405782484762750663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14029439603854989841833775 21044159405782484762750663)
            ·
              refine ⟨31566239108673727144125995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21044159405782484762750663 31566239108673727144125995)
              ·
                refine ⟨47349358663010590716188993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31566239108673727144125995 47349358663010590716188993)
                ·
                  refine ⟨35512018997257943037141745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47349358663010590716188993 35512018997257943037141745)
                  ·
                    refine ⟨26634014247943457277856309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35512018997257943037141745 26634014247943457277856309)
                    ·
                      refine ⟨2496938835744699119799029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26634014247943457277856309 2496938835744699119799029)
                      ·
                        rfl

theorem cell23_4862771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_4862771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862771 prefixEnd_4862771 := by exact prefixLift 4862771
  have htrace : WordTrace (prefixWord ++ tailWord_4862771) baseStart_4862771 baseEnd_4862771 := by
    simpa [prefixWord, tailWord_4862771, baseEnd_4862771] using wordTrace_append hprefix tailTrace_4862771
  have hstable : (prefixWord ++ tailWord_4862771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862771).length < 2 ^ (prefixWord ++ tailWord_4862771).sum := by decide
  have hdescent : baseEnd_4862771 < baseStart_4862771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862821 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 7]
def baseStart_4862821 : Nat := 118140960795 + 4862821 * 2 ^ 59
def prefixEnd_4862821 : Nat := 4983230072969 + 3 ^ 40 * 4862821 * 2
def baseEnd_4862821 : Nat := 277440501086380436019311

theorem tailTrace_4862821 : CollatzResearch.WordTrace tailWord_4862821 prefixEnd_4862821 277440501086380436019311 := by
  unfold tailWord_4862821
  simp only [CollatzResearch.WordTrace]
  refine ⟨177361652715837495552132317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118241101810558330368088211 177361652715837495552132317)
  ·
    refine ⟨66510619768439060832049619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177361652715837495552132317 66510619768439060832049619)
    ·
      refine ⟨99765929652658591248074429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66510619768439060832049619 99765929652658591248074429)
      ·
        refine ⟨37412223619746971718027911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99765929652658591248074429 37412223619746971718027911)
        ·
          refine ⟨56118335429620457577041867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37412223619746971718027911 56118335429620457577041867)
          ·
            refine ⟨84177503144430686365562801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56118335429620457577041867 84177503144430686365562801)
            ·
              refine ⟨63133127358323014774172101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84177503144430686365562801 63133127358323014774172101)
              ·
                refine ⟨11837461379685565270157269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63133127358323014774172101 11837461379685565270157269)
                ·
                  refine ⟨277440501086380436019311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11837461379685565270157269 277440501086380436019311)
                  ·
                    rfl

theorem cell23_4862821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_4862821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862821 prefixEnd_4862821 := by exact prefixLift 4862821
  have htrace : WordTrace (prefixWord ++ tailWord_4862821) baseStart_4862821 baseEnd_4862821 := by
    simpa [prefixWord, tailWord_4862821, baseEnd_4862821] using wordTrace_append hprefix tailTrace_4862821
  have hstable : (prefixWord ++ tailWord_4862821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862821).length < 2 ^ (prefixWord ++ tailWord_4862821).sum := by decide
  have hdescent : baseEnd_4862821 < baseStart_4862821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862855 : List Nat := [1, 1, 4, 2, 3, 2, 1, 4, 5]
def baseStart_4862855 : Nat := 118140960795 + 4862855 * 2 ^ 59
def prefixEnd_4862855 : Nat := 4983230072969 + 3 ^ 40 * 4862855 * 2
def baseEnd_4862855 : Nat := 277442440902186310127627

theorem tailTrace_4862855 : CollatzResearch.WordTrace tailWord_4862855 prefixEnd_4862855 277442440902186310127627 := by
  unfold tailWord_4862855
  simp only [CollatzResearch.WordTrace]
  refine ⟨177362892797714319358870019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118241928531809546239246679 177362892797714319358870019)
  ·
    refine ⟨266044339196571479038305029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177362892797714319358870019 266044339196571479038305029)
    ·
      refine ⟨49883313599357152319682193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266044339196571479038305029 49883313599357152319682193)
      ·
        refine ⟨37412485199517864239761645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49883313599357152319682193 37412485199517864239761645)
        ·
          refine ⟨14029681949819199089910617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37412485199517864239761645 14029681949819199089910617)
          ·
            refine ⟨10522261462364399317432963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14029681949819199089910617 10522261462364399317432963)
            ·
              refine ⟨15783392193546598976149445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10522261462364399317432963 15783392193546598976149445)
              ·
                refine ⟨2959386036289987308028021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15783392193546598976149445 2959386036289987308028021)
                ·
                  refine ⟨277442440902186310127627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2959386036289987308028021 277442440902186310127627)
                  ·
                    rfl

theorem cell23_4862855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 5].length) (baseStart_4862855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862855 prefixEnd_4862855 := by exact prefixLift 4862855
  have htrace : WordTrace (prefixWord ++ tailWord_4862855) baseStart_4862855 baseEnd_4862855 := by
    simpa [prefixWord, tailWord_4862855, baseEnd_4862855] using wordTrace_append hprefix tailTrace_4862855
  have hstable : (prefixWord ++ tailWord_4862855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862855).length < 2 ^ (prefixWord ++ tailWord_4862855).sum := by decide
  have hdescent : baseEnd_4862855 < baseStart_4862855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862868 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_4862868 : Nat := 118140960795 + 4862868 * 2 ^ 59
def prefixEnd_4862868 : Nat := 4983230072969 + 3 ^ 40 * 4862868 * 2
def baseEnd_4862868 : Nat := 832329547789395080095361

theorem tailTrace_4862868 : CollatzResearch.WordTrace tailWord_4862868 prefixEnd_4862868 832329547789395080095361 := by
  unfold tailWord_4862868
  simp only [CollatzResearch.WordTrace]
  refine ⟨88681683473333611289546629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118242244631111481719395505 88681683473333611289546629)
  ·
    refine ⟨16627815651250052116789993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88681683473333611289546629 16627815651250052116789993)
    ·
      refine ⟨12470861738437539087592495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16627815651250052116789993 12470861738437539087592495)
      ·
        refine ⟨18706292607656308631388743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12470861738437539087592495 18706292607656308631388743)
        ·
          refine ⟨28059438911484462947083115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18706292607656308631388743 28059438911484462947083115)
          ·
            refine ⟨42089158367226694420624673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28059438911484462947083115 42089158367226694420624673)
            ·
              refine ⟨31566868775420020815468505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42089158367226694420624673 31566868775420020815468505)
              ·
                refine ⟨23675151581565015611601379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31566868775420020815468505 23675151581565015611601379)
                ·
                  refine ⟨35512727372347523417402069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23675151581565015611601379 35512727372347523417402069)
                  ·
                    refine ⟨832329547789395080095361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35512727372347523417402069 832329547789395080095361)
                    ·
                      rfl

theorem cell23_4862868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_4862868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862868 prefixEnd_4862868 := by exact prefixLift 4862868
  have htrace : WordTrace (prefixWord ++ tailWord_4862868) baseStart_4862868 baseEnd_4862868 := by
    simpa [prefixWord, tailWord_4862868, baseEnd_4862868] using wordTrace_append hprefix tailTrace_4862868
  have hstable : (prefixWord ++ tailWord_4862868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862868).length < 2 ^ (prefixWord ++ tailWord_4862868).sum := by decide
  have hdescent : baseEnd_4862868 < baseStart_4862868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862905 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 2, 4, 2]
def baseStart_4862905 : Nat := 118140960795 + 4862905 * 2 ^ 59
def prefixEnd_4862905 : Nat := 4983230072969 + 3 ^ 40 * 4862905 * 2
def baseEnd_4862905 : Nat := 2497007642152401595523413

theorem tailTrace_4862905 : CollatzResearch.WordTrace tailWord_4862905 prefixEnd_4862905 2497007642152401595523413 := by
  unfold tailWord_4862905
  simp only [CollatzResearch.WordTrace]
  refine ⟨177364716447533177898190169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118243144298355451932126779 177364716447533177898190169)
  ·
    refine ⟨133023537335649883423642627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177364716447533177898190169 133023537335649883423642627)
    ·
      refine ⟨199535306003474825135463941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133023537335649883423642627 199535306003474825135463941)
      ·
        refine ⟨37412869875651529712899489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199535306003474825135463941 37412869875651529712899489)
        ·
          refine ⟨28059652406738647284674617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37412869875651529712899489 28059652406738647284674617)
          ·
            refine ⟨21044739305053985463505963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28059652406738647284674617 21044739305053985463505963)
            ·
              refine ⟨31567108957580978195258945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21044739305053985463505963 31567108957580978195258945)
              ·
                refine ⟨23675331718185733646444209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31567108957580978195258945 23675331718185733646444209)
                ·
                  refine ⟨17756498788639300234833157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23675331718185733646444209 17756498788639300234833157)
                  ·
                    refine ⟨3329343522869868794031217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17756498788639300234833157 3329343522869868794031217)
                    ·
                      refine ⟨2497007642152401595523413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3329343522869868794031217 2497007642152401595523413)
                      ·
                        rfl

theorem cell23_4862905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_4862905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862905 prefixEnd_4862905 := by exact prefixLift 4862905
  have htrace : WordTrace (prefixWord ++ tailWord_4862905) baseStart_4862905 baseEnd_4862905 := by
    simpa [prefixWord, tailWord_4862905, baseEnd_4862905] using wordTrace_append hprefix tailTrace_4862905
  have hstable : (prefixWord ++ tailWord_4862905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862905).length < 2 ^ (prefixWord ++ tailWord_4862905).sum := by decide
  have hdescent : baseEnd_4862905 < baseStart_4862905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862966 : List Nat := [5, 1, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_4862966 : Nat := 118140960795 + 4862966 * 2 ^ 59
def prefixEnd_4862966 : Nat := 4983230072969 + 3 ^ 40 * 4862966 * 2
def baseEnd_4862966 : Nat := 832346321490775285620211

theorem tailTrace_4862966 : CollatzResearch.WordTrace tailWord_4862966 prefixEnd_4862966 832346321490775285620211 := by
  unfold tailWord_4862966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11085433831269511582260047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118244627533541456877440501 11085433831269511582260047)
  ·
    refine ⟨16628150746904267373390071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11085433831269511582260047 16628150746904267373390071)
    ·
      refine ⟨24942226120356401060085107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16628150746904267373390071 24942226120356401060085107)
      ·
        refine ⟨37413339180534601590127661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24942226120356401060085107 37413339180534601590127661)
        ·
          refine ⟨14030002192700475596297873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37413339180534601590127661 14030002192700475596297873)
          ·
            refine ⟨10522501644525356697223405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14030002192700475596297873 10522501644525356697223405)
            ·
              refine ⟨3945938116697008761458777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10522501644525356697223405 3945938116697008761458777)
              ·
                refine ⟨2959453587522756571094083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3945938116697008761458777 2959453587522756571094083)
                ·
                  refine ⟨4439180381284134856641125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2959453587522756571094083 4439180381284134856641125)
                  ·
                    refine ⟨832346321490775285620211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4439180381284134856641125 832346321490775285620211)
                    ·
                      rfl

theorem cell23_4862966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_4862966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862966 prefixEnd_4862966 := by exact prefixLift 4862966
  have htrace : WordTrace (prefixWord ++ tailWord_4862966) baseStart_4862966 baseEnd_4862966 := by
    simpa [prefixWord, tailWord_4862966, baseEnd_4862966] using wordTrace_append hprefix tailTrace_4862966
  have hstable : (prefixWord ++ tailWord_4862966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862966).length < 2 ^ (prefixWord ++ tailWord_4862966).sum := by decide
  have hdescent : baseEnd_4862966 < baseStart_4862966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862972 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_4862972 : Nat := 118140960795 + 4862972 * 2 ^ 59
def prefixEnd_4862972 : Nat := 4983230072969 + 3 ^ 40 * 4862972 * 2
def baseEnd_4862972 : Nat := 2497042045356252833385605

theorem tailTrace_4862972 : CollatzResearch.WordTrace tailWord_4862972 prefixEnd_4862972 2497042045356252833385605 := by
  unfold tailWord_4862972
  simp only [CollatzResearch.WordTrace]
  refine ⟨88683580069145224170439585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118244773425526965560586113 88683580069145224170439585)
  ·
    refine ⟨66512685051858918127829689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88683580069145224170439585 66512685051858918127829689)
    ·
      refine ⟨49884513788894188595872267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66512685051858918127829689 49884513788894188595872267)
      ·
        refine ⟨74826770683341282893808401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49884513788894188595872267 74826770683341282893808401)
        ·
          refine ⟨56120078012505962170356301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74826770683341282893808401 56120078012505962170356301)
          ·
            refine ⟨21045029254689735813883613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56120078012505962170356301 21045029254689735813883613)
            ·
              refine ⟨7891885970508650930206355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21045029254689735813883613 7891885970508650930206355)
              ·
                refine ⟨11837828955762976395309533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7891885970508650930206355 11837828955762976395309533)
                ·
                  refine ⟨4439185858411116148241075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11837828955762976395309533 4439185858411116148241075)
                  ·
                    refine ⟨6658778787616674222361613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4439185858411116148241075 6658778787616674222361613)
                    ·
                      refine ⟨2497042045356252833385605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6658778787616674222361613 2497042045356252833385605)
                      ·
                        rfl

theorem cell23_4862972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_4862972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862972 prefixEnd_4862972 := by exact prefixLift 4862972
  have htrace : WordTrace (prefixWord ++ tailWord_4862972) baseStart_4862972 baseEnd_4862972 := by
    simpa [prefixWord, tailWord_4862972, baseEnd_4862972] using wordTrace_append hprefix tailTrace_4862972
  have hstable : (prefixWord ++ tailWord_4862972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862972).length < 2 ^ (prefixWord ++ tailWord_4862972).sum := by decide
  have hdescent : baseEnd_4862972 < baseStart_4862972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4862999 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 2, 3, 2]
def baseStart_4862999 : Nat := 118140960795 + 4862999 * 2 ^ 59
def prefixEnd_4862999 : Nat := 4983230072969 + 3 ^ 40 * 4862999 * 2
def baseEnd_4862999 : Nat := 2497055909333924227747981

theorem tailTrace_4862999 : CollatzResearch.WordTrace tailWord_4862999 prefixEnd_4862999 2497055909333924227747981 := by
  unfold tailWord_4862999
  simp only [CollatzResearch.WordTrace]
  refine ⟨177368144909192631952112051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118245429939461754634741367 177368144909192631952112051)
  ·
    refine ⟨266052217363788947928168077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177368144909192631952112051 266052217363788947928168077)
    ·
      refine ⟨99769581511420855473063029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266052217363788947928168077 99769581511420855473063029)
      ·
        refine ⟨9353398266695705200599659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99769581511420855473063029 9353398266695705200599659)
        ·
          refine ⟨14030097400043557800899489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9353398266695705200599659 14030097400043557800899489)
          ·
            refine ⟨10522573050032668350674617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14030097400043557800899489 10522573050032668350674617)
            ·
              refine ⟨7891929787524501263005963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10522573050032668350674617 7891929787524501263005963)
              ·
                refine ⟨11837894681286751894508945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7891929787524501263005963 11837894681286751894508945)
                ·
                  refine ⟨8878421010965063920881709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11837894681286751894508945 8878421010965063920881709)
                  ·
                    refine ⟨3329407879111898970330641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8878421010965063920881709 3329407879111898970330641)
                    ·
                      refine ⟨2497055909333924227747981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3329407879111898970330641 2497055909333924227747981)
                      ·
                        rfl

theorem cell23_4862999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_4862999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4862999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4862999 prefixEnd_4862999 := by exact prefixLift 4862999
  have htrace : WordTrace (prefixWord ++ tailWord_4862999) baseStart_4862999 baseEnd_4862999 := by
    simpa [prefixWord, tailWord_4862999, baseEnd_4862999] using wordTrace_append hprefix tailTrace_4862999
  have hstable : (prefixWord ++ tailWord_4862999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4862999).length < 2 ^ (prefixWord ++ tailWord_4862999).sum := by decide
  have hdescent : baseEnd_4862999 < baseStart_4862999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4862999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863018 : List Nat := [3, 1, 4, 1, 14]
def baseStart_4863018 : Nat := 118140960795 + 4863018 * 2 ^ 59
def prefixEnd_4863018 : Nat := 4983230072969 + 3 ^ 40 * 4863018 * 2
def baseEnd_4863018 : Nat := 3425330130955225862017

theorem tailTrace_4863018 : CollatzResearch.WordTrace tailWord_4863018 prefixEnd_4863018 3425330130955225862017 := by
  unfold tailWord_4863018
  simp only [CollatzResearch.WordTrace]
  refine ⟨44342209474030949549263427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118245891930749198798035805 44342209474030949549263427)
  ·
    refine ⟨66513314211046424323895141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44342209474030949549263427 66513314211046424323895141)
    ·
      refine ⟨12471246414571204560730339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66513314211046424323895141 12471246414571204560730339)
      ·
        refine ⟨18706869621856806841095509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12471246414571204560730339 18706869621856806841095509)
        ·
          refine ⟨3425330130955225862017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 18706869621856806841095509 3425330130955225862017)
          ·
            rfl

theorem cell23_4863018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 14].length) (baseStart_4863018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863018 prefixEnd_4863018 := by exact prefixLift 4863018
  have htrace : WordTrace (prefixWord ++ tailWord_4863018) baseStart_4863018 baseEnd_4863018 := by
    simpa [prefixWord, tailWord_4863018, baseEnd_4863018] using wordTrace_append hprefix tailTrace_4863018
  have hstable : (prefixWord ++ tailWord_4863018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863018).length < 2 ^ (prefixWord ++ tailWord_4863018).sum := by decide
  have hdescent : baseEnd_4863018 < baseStart_4863018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863045 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 1, 3, 3]
def baseStart_4863045 : Nat := 118140960795 + 4863045 * 2 ^ 59
def prefixEnd_4863045 : Nat := 4983230072969 + 3 ^ 40 * 4863045 * 2
def baseEnd_4863045 : Nat := 2497079529444031047772769

theorem tailTrace_4863045 : CollatzResearch.WordTrace tailWord_4863045 prefixEnd_4863045 2497079529444031047772769 := by
  unfold tailWord_4863045
  simp only [CollatzResearch.WordTrace]
  refine ⟨177369822667025981808286589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118246548444683987872191059 177369822667025981808286589)
  ·
    refine ⟨66513683500134743178107471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177369822667025981808286589 66513683500134743178107471)
    ·
      refine ⟨99770525250202114767161207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66513683500134743178107471 99770525250202114767161207)
      ·
        refine ⟨149655787875303172150741811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99770525250202114767161207 149655787875303172150741811)
        ·
          refine ⟨224483681812954758226112717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149655787875303172150741811 224483681812954758226112717)
          ·
            refine ⟨84181380679858034334792269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224483681812954758226112717 84181380679858034334792269)
            ·
              refine ⟨31568017754946762875547101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84181380679858034334792269 31568017754946762875547101)
              ·
                refine ⟨11838006658105036078330163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31568017754946762875547101 11838006658105036078330163)
                ·
                  refine ⟨17757009987157554117495245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11838006658105036078330163 17757009987157554117495245)
                  ·
                    refine ⟨6658878745184082794060717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17757009987157554117495245 6658878745184082794060717)
                    ·
                      refine ⟨2497079529444031047772769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6658878745184082794060717 2497079529444031047772769)
                      ·
                        rfl

theorem cell23_4863045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_4863045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863045 prefixEnd_4863045 := by exact prefixLift 4863045
  have htrace : WordTrace (prefixWord ++ tailWord_4863045) baseStart_4863045 baseEnd_4863045 := by
    simpa [prefixWord, tailWord_4863045, baseEnd_4863045] using wordTrace_append hprefix tailTrace_4863045
  have hstable : (prefixWord ++ tailWord_4863045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863045).length < 2 ^ (prefixWord ++ tailWord_4863045).sum := by decide
  have hdescent : baseEnd_4863045 < baseStart_4863045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863046 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_4863046 : Nat := 118140960795 + 4863046 * 2 ^ 59
def prefixEnd_4863046 : Nat := 4983230072969 + 3 ^ 40 * 4863046 * 2
def baseEnd_4863046 : Nat := 2497080042924685543860265

theorem tailTrace_4863046 : CollatzResearch.WordTrace tailWord_4863046 prefixEnd_4863046 2497080042924685543860265 := by
  unfold tailWord_4863046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5542808098125698718096031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118246572760014905986048661 5542808098125698718096031)
  ·
    refine ⟨8314212147188548077144047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5542808098125698718096031 8314212147188548077144047)
    ·
      refine ⟨12471318220782822115716071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8314212147188548077144047 12471318220782822115716071)
      ·
        refine ⟨18706977331174233173574107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12471318220782822115716071 18706977331174233173574107)
        ·
          refine ⟨28060465996761349760361161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18706977331174233173574107 28060465996761349760361161)
          ·
            refine ⟨21045349497571012320270871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28060465996761349760361161 21045349497571012320270871)
            ·
              refine ⟨31568024246356518480406307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21045349497571012320270871 31568024246356518480406307)
              ·
                refine ⟨47352036369534777720609461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31568024246356518480406307 47352036369534777720609461)
                ·
                  refine ⟨4439253409643885411307137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47352036369534777720609461 4439253409643885411307137)
                  ·
                    refine ⟨3329440057232914058480353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4439253409643885411307137 3329440057232914058480353)
                    ·
                      refine ⟨2497080042924685543860265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3329440057232914058480353 2497080042924685543860265)
                      ·
                        rfl

theorem cell23_4863046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_4863046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863046 prefixEnd_4863046 := by exact prefixLift 4863046
  have htrace : WordTrace (prefixWord ++ tailWord_4863046) baseStart_4863046 baseEnd_4863046 := by
    simpa [prefixWord, tailWord_4863046, baseEnd_4863046] using wordTrace_append hprefix tailTrace_4863046
  have hstable : (prefixWord ++ tailWord_4863046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863046).length < 2 ^ (prefixWord ++ tailWord_4863046).sum := by decide
  have hdescent : baseEnd_4863046 < baseStart_4863046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863048 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 2, 7]
def baseStart_4863048 : Nat := 118140960795 + 4863048 * 2 ^ 59
def prefixEnd_4863048 : Nat := 4983230072969 + 3 ^ 40 * 4863048 * 2
def baseEnd_4863048 : Nat := 832360356628664845345085

theorem tailTrace_4863048 : CollatzResearch.WordTrace tailWord_4863048 prefixEnd_4863048 832360356628664845345085 := by
  unfold tailWord_4863048
  simp only [CollatzResearch.WordTrace]
  refine ⟨88684966043007556660322899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118246621390676742213763865 88684966043007556660322899)
  ·
    refine ⟨133027449064511334990484349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88684966043007556660322899 133027449064511334990484349)
    ·
      refine ⟨49885293399191750621431631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133027449064511334990484349 49885293399191750621431631)
      ·
        refine ⟨74827940098787625932147447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49885293399191750621431631 74827940098787625932147447)
        ·
          refine ⟨112241910148181438898221171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74827940098787625932147447 112241910148181438898221171)
          ·
            refine ⟨168362865222272158347331757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112241910148181438898221171 168362865222272158347331757)
            ·
              refine ⟨63136074458352059380249409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168362865222272158347331757 63136074458352059380249409)
              ·
                refine ⟨47352055843764044535187057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63136074458352059380249409 47352055843764044535187057)
                ·
                  refine ⟨35514041882823033401390293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47352055843764044535187057 35514041882823033401390293)
                  ·
                    refine ⟨832360356628664845345085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35514041882823033401390293 832360356628664845345085)
                    ·
                      rfl

theorem cell23_4863048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_4863048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863048 prefixEnd_4863048 := by exact prefixLift 4863048
  have htrace : WordTrace (prefixWord ++ tailWord_4863048) baseStart_4863048 baseEnd_4863048 := by
    simpa [prefixWord, tailWord_4863048, baseEnd_4863048] using wordTrace_append hprefix tailTrace_4863048
  have hstable : (prefixWord ++ tailWord_4863048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863048).length < 2 ^ (prefixWord ++ tailWord_4863048).sum := by decide
  have hdescent : baseEnd_4863048 < baseStart_4863048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
