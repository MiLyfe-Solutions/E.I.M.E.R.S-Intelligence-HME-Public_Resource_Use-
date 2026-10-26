import V185TrunkScan22Chunk181

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1623510 : List Nat := [5, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_1623510 : Nat := 118140960795 + 1623510 * 2 ^ 59
def prefixEnd_1623510 : Nat := 4983230072969 + 3 ^ 40 * 1623510 * 2
def baseEnd_1623510 : Nat := 185253550529121831857471

theorem tailTrace_1623510 : CollatzResearch.WordTrace tailWord_1623510 prefixEnd_1623510 185253550529121831857471 := by
  unfold tailWord_1623510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3700892146769251142390249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39476182898872012185495989 3700892146769251142390249)
  ·
    refine ⟨2775669110076938356792687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3700892146769251142390249 2775669110076938356792687)
    ·
      refine ⟨4163503665115407535189031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2775669110076938356792687 4163503665115407535189031)
      ·
        refine ⟨6245255497673111302783547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4163503665115407535189031 6245255497673111302783547)
        ·
          refine ⟨9367883246509666954175321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6245255497673111302783547 9367883246509666954175321)
          ·
            refine ⟨7025912434882250215631491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9367883246509666954175321 7025912434882250215631491)
            ·
              refine ⟨10538868652323375323447237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7025912434882250215631491 10538868652323375323447237)
              ·
                refine ⟨1976037872310632873146357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10538868652323375323447237 1976037872310632873146357)
                ·
                  refine ⟨185253550529121831857471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1976037872310632873146357 185253550529121831857471)
                  ·
                    rfl

theorem cell22_1623510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_1623510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623510 prefixEnd_1623510 := by exact prefixLift 1623510
  have htrace : WordTrace (prefixWord ++ tailWord_1623510) baseStart_1623510 baseEnd_1623510 := by
    simpa [prefixWord, tailWord_1623510, baseEnd_1623510] using wordTrace_append hprefix tailTrace_1623510
  have hstable : (prefixWord ++ tailWord_1623510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623510).length < 2 ^ (prefixWord ++ tailWord_1623510).sum := by decide
  have hdescent : baseEnd_1623510 < baseStart_1623510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623514 : List Nat := [3, 1, 1, 2, 3, 4, 2, 2, 1, 3]
def baseStart_1623514 : Nat := 118140960795 + 1623514 * 2 ^ 59
def prefixEnd_1623514 : Nat := 4983230072969 + 3 ^ 40 * 1623514 * 2
def baseEnd_1623514 : Nat := 555762020869110818472401

theorem tailTrace_1623514 : CollatzResearch.WordTrace tailWord_1623514 prefixEnd_1623514 555762020869110818472401 := by
  unfold tailWord_1623514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14803605060073381740347399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39476280160195684640926397 14803605060073381740347399)
  ·
    refine ⟨22205407590110072610521099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14803605060073381740347399 22205407590110072610521099)
    ·
      refine ⟨33308111385165108915781649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22205407590110072610521099 33308111385165108915781649)
      ·
        refine ⟨24981083538873831686836237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33308111385165108915781649 24981083538873831686836237)
        ·
          refine ⟨9367906327077686882563589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24981083538873831686836237 9367906327077686882563589)
          ·
            refine ⟨1756482436327066290480673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9367906327077686882563589 1756482436327066290480673)
            ·
              refine ⟨1317361827245299717860505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1756482436327066290480673 1317361827245299717860505)
              ·
                refine ⟨988021370433974788395379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1317361827245299717860505 988021370433974788395379)
                ·
                  refine ⟨1482032055650962182593069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 988021370433974788395379 1482032055650962182593069)
                  ·
                    refine ⟨555762020869110818472401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1482032055650962182593069 555762020869110818472401)
                    ·
                      rfl

theorem cell22_1623514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_1623514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623514 prefixEnd_1623514 := by exact prefixLift 1623514
  have htrace : WordTrace (prefixWord ++ tailWord_1623514) baseStart_1623514 baseEnd_1623514 := by
    simpa [prefixWord, tailWord_1623514, baseEnd_1623514] using wordTrace_append hprefix tailTrace_1623514
  have hstable : (prefixWord ++ tailWord_1623514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623514).length < 2 ^ (prefixWord ++ tailWord_1623514).sum := by decide
  have hdescent : baseEnd_1623514 < baseStart_1623514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623523 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 3, 4]
def baseStart_1623523 : Nat := 118140960795 + 1623523 * 2 ^ 59
def prefixEnd_1623523 : Nat := 4983230072969 + 3 ^ 40 * 1623523 * 2
def baseEnd_1623523 : Nat := 555765101753037794997373

theorem tailTrace_1623523 : CollatzResearch.WordTrace tailWord_1623523 prefixEnd_1623523 555765101753037794997373 := by
  unfold tailWord_1623523
  simp only [CollatzResearch.WordTrace]
  refine ⟨59214748497260921498467223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39476498998173947665644815 59214748497260921498467223)
  ·
    refine ⟨88822122745891382247700835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59214748497260921498467223 88822122745891382247700835)
    ·
      refine ⟨133233184118837073371551253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88822122745891382247700835 133233184118837073371551253)
      ·
        refine ⟨6245305505570487814291465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133233184118837073371551253 6245305505570487814291465)
        ·
          refine ⟨4683979129177865860718599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6245305505570487814291465 4683979129177865860718599)
          ·
            refine ⟨7025968693766798791077899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4683979129177865860718599 7025968693766798791077899)
            ·
              refine ⟨10538953040650198186616849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7025968693766798791077899 10538953040650198186616849)
              ·
                refine ⟨7904214780487648639962637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10538953040650198186616849 7904214780487648639962637)
                ·
                  refine ⟨2964080542682868239985989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7904214780487648639962637 2964080542682868239985989)
                  ·
                    refine ⟨555765101753037794997373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2964080542682868239985989 555765101753037794997373)
                    ·
                      rfl

theorem cell22_1623523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 4].length) (baseStart_1623523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623523 prefixEnd_1623523 := by exact prefixLift 1623523
  have htrace : WordTrace (prefixWord ++ tailWord_1623523) baseStart_1623523 baseEnd_1623523 := by
    simpa [prefixWord, tailWord_1623523, baseEnd_1623523] using wordTrace_append hprefix tailTrace_1623523
  have hstable : (prefixWord ++ tailWord_1623523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623523).length < 2 ^ (prefixWord ++ tailWord_1623523).sum := by decide
  have hdescent : baseEnd_1623523 < baseStart_1623523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623538 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 8]
def baseStart_1623538 : Nat := 118140960795 + 1623538 * 2 ^ 59
def prefixEnd_1623538 : Nat := 4983230072969 + 3 ^ 40 * 1623538 * 2
def baseEnd_1623538 : Nat := 185256745519860918624109

theorem tailTrace_1623538 : CollatzResearch.WordTrace tailWord_1623538 prefixEnd_1623538 185256745519860918624109 := by
  unfold tailWord_1623538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14803823898051644765065817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39476863728137719373508845 14803823898051644765065817)
  ·
    refine ⟨11102867923538733573799363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14803823898051644765065817 11102867923538733573799363)
    ·
      refine ⟨16654301885308100360699045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11102867923538733573799363 16654301885308100360699045)
      ·
        refine ⟨3122681603495268817631071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16654301885308100360699045 3122681603495268817631071)
        ·
          refine ⟨4684022405242903226446607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3122681603495268817631071 4684022405242903226446607)
          ·
            refine ⟨7026033607864354839669911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4684022405242903226446607 7026033607864354839669911)
            ·
              refine ⟨10539050411796532259504867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7026033607864354839669911 10539050411796532259504867)
              ·
                refine ⟨15808575617694798389257301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10539050411796532259504867 15808575617694798389257301)
                ·
                  refine ⟨185256745519860918624109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15808575617694798389257301 185256745519860918624109)
                  ·
                    rfl

theorem cell22_1623538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_1623538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623538 prefixEnd_1623538 := by exact prefixLift 1623538
  have htrace : WordTrace (prefixWord ++ tailWord_1623538) baseStart_1623538 baseEnd_1623538 := by
    simpa [prefixWord, tailWord_1623538, baseEnd_1623538] using wordTrace_append hprefix tailTrace_1623538
  have hstable : (prefixWord ++ tailWord_1623538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623538).length < 2 ^ (prefixWord ++ tailWord_1623538).sum := by decide
  have hdescent : baseEnd_1623538 < baseStart_1623538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623572 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 6]
def baseStart_1623572 : Nat := 118140960795 + 1623572 * 2 ^ 59
def prefixEnd_1623572 : Nat := 4983230072969 + 3 ^ 40 * 1623572 * 2
def baseEnd_1623572 : Nat := 185260625151472666840741

theorem tailTrace_1623572 : CollatzResearch.WordTrace tailWord_1623572 prefixEnd_1623572 185260625151472666840741 := by
  unfold tailWord_1623572
  simp only [CollatzResearch.WordTrace]
  refine ⟨29608267837041701433500485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39477690449388935244667313 29608267837041701433500485)
  ·
    refine ⟨5551550219445319018781341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29608267837041701433500485 5551550219445319018781341)
    ·
      refine ⟨2081831332291994632043003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5551550219445319018781341 2081831332291994632043003)
      ·
        refine ⟨3122746998437991948064505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081831332291994632043003 3122746998437991948064505)
        ·
          refine ⟨2342060248828493961048379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3122746998437991948064505 2342060248828493961048379)
          ·
            refine ⟨3513090373242740941572569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342060248828493961048379 3513090373242740941572569)
            ·
              refine ⟨2634817779932055706179427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3513090373242740941572569 2634817779932055706179427)
              ·
                refine ⟨3952226669898083559269141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634817779932055706179427 3952226669898083559269141)
                ·
                  refine ⟨185260625151472666840741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3952226669898083559269141 185260625151472666840741)
                  ·
                    rfl

theorem cell22_1623572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_1623572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623572 prefixEnd_1623572 := by exact prefixLift 1623572
  have htrace : WordTrace (prefixWord ++ tailWord_1623572) baseStart_1623572 baseEnd_1623572 := by
    simpa [prefixWord, tailWord_1623572, baseEnd_1623572] using wordTrace_append hprefix tailTrace_1623572
  have hstable : (prefixWord ++ tailWord_1623572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623572).length < 2 ^ (prefixWord ++ tailWord_1623572).sum := by decide
  have hdescent : baseEnd_1623572 < baseStart_1623572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623587 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 1, 5]
def baseStart_1623587 : Nat := 118140960795 + 1623587 * 2 ^ 59
def prefixEnd_1623587 : Nat := 4983230072969 + 3 ^ 40 * 1623587 * 2
def baseEnd_1623587 : Nat := 555787010260962961397177

theorem tailTrace_1623587 : CollatzResearch.WordTrace tailWord_1623587 prefixEnd_1623587 555787010260962961397177 := by
  unfold tailWord_1623587
  simp only [CollatzResearch.WordTrace]
  refine ⟨59217082769029060428797015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39478055179352706952531343 59217082769029060428797015)
  ·
    refine ⟨88825624153543590643195523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59217082769029060428797015 88825624153543590643195523)
    ·
      refine ⟨133238436230315385964793285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88825624153543590643195523 133238436230315385964793285)
      ·
        refine ⟨24982206793184134868398741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133238436230315385964793285 24982206793184134868398741)
        ·
          refine ⟨1171040943430506321956191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24982206793184134868398741 1171040943430506321956191)
          ·
            refine ⟨1756561415145759482934287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171040943430506321956191 1756561415145759482934287)
            ·
              refine ⟨2634842122718639224401431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756561415145759482934287 2634842122718639224401431)
              ·
                refine ⟨3952263184077958836602147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634842122718639224401431 3952263184077958836602147)
                ·
                  refine ⟨5928394776116938254903221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3952263184077958836602147 5928394776116938254903221)
                  ·
                    refine ⟨555787010260962961397177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5928394776116938254903221 555787010260962961397177)
                    ·
                      rfl

theorem cell22_1623587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 5].length) (baseStart_1623587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623587 prefixEnd_1623587 := by exact prefixLift 1623587
  have htrace : WordTrace (prefixWord ++ tailWord_1623587) baseStart_1623587 baseEnd_1623587 := by
    simpa [prefixWord, tailWord_1623587, baseEnd_1623587] using wordTrace_append hprefix tailTrace_1623587
  have hstable : (prefixWord ++ tailWord_1623587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623587).length < 2 ^ (prefixWord ++ tailWord_1623587).sum := by decide
  have hdescent : baseEnd_1623587 < baseStart_1623587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623606 : List Nat := [5, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_1623606 : Nat := 118140960795 + 1623606 * 2 ^ 59
def prefixEnd_1623606 : Nat := 4983230072969 + 3 ^ 40 * 1623606 * 2
def baseEnd_1623606 : Nat := 185264504783084415057373

theorem tailTrace_1623606 : CollatzResearch.WordTrace tailWord_1623606 prefixEnd_1623606 185264504783084415057373 := by
  unfold tailWord_1623606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3701110984747514167108667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39478517170640151115825781 3701110984747514167108667)
  ·
    refine ⟨5551666477121271250663001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3701110984747514167108667 5551666477121271250663001)
    ·
      refine ⟨4163749857840953437997251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5551666477121271250663001 4163749857840953437997251)
      ·
        refine ⟨6245624786761430156995877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4163749857840953437997251 6245624786761430156995877)
        ·
          refine ⟨1171054647517768154436727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6245624786761430156995877 1171054647517768154436727)
          ·
            refine ⟨1756581971276652231655091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171054647517768154436727 1756581971276652231655091)
            ·
              refine ⟨2634872956914978347482637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756581971276652231655091 2634872956914978347482637)
              ·
                refine ⟨988077358843116880305989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2634872956914978347482637 988077358843116880305989)
                ·
                  refine ⟨185264504783084415057373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 988077358843116880305989 185264504783084415057373)
                  ·
                    rfl

theorem cell22_1623606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_1623606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623606 prefixEnd_1623606 := by exact prefixLift 1623606
  have htrace : WordTrace (prefixWord ++ tailWord_1623606) baseStart_1623606 baseEnd_1623606 := by
    simpa [prefixWord, tailWord_1623606, baseEnd_1623606] using wordTrace_append hprefix tailTrace_1623606
  have hstable : (prefixWord ++ tailWord_1623606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623606).length < 2 ^ (prefixWord ++ tailWord_1623606).sum := by decide
  have hdescent : baseEnd_1623606 < baseStart_1623606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623628 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 7]
def baseStart_1623628 : Nat := 118140960795 + 1623628 * 2 ^ 59
def prefixEnd_1623628 : Nat := 4983230072969 + 3 ^ 40 * 1623628 * 2
def baseEnd_1623628 : Nat := 185267015132950840374017

theorem tailTrace_1623628 : CollatzResearch.WordTrace tailWord_1623628 prefixEnd_1623628 185267015132950840374017 := by
  unfold tailWord_1623628
  simp only [CollatzResearch.WordTrace]
  refine ⟨29609289080940262215519769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39479052107920349620693025 29609289080940262215519769)
  ·
    refine ⟨22206966810705196661639827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29609289080940262215519769 22206966810705196661639827)
    ·
      refine ⟨33310450216057794992459741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22206966810705196661639827 33310450216057794992459741)
      ·
        refine ⟨12491418831021673122172403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33310450216057794992459741 12491418831021673122172403)
        ·
          refine ⟨18737128246532509683258605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12491418831021673122172403 18737128246532509683258605)
          ·
            refine ⟨7026423092449691131221977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18737128246532509683258605 7026423092449691131221977)
            ·
              refine ⟨5269817319337268348416483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7026423092449691131221977 5269817319337268348416483)
              ·
                refine ⟨7904725979005902522624725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5269817319337268348416483 7904725979005902522624725)
                ·
                  refine ⟨185267015132950840374017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7904725979005902522624725 185267015132950840374017)
                  ·
                    rfl

theorem cell22_1623628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_1623628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623628 prefixEnd_1623628 := by exact prefixLift 1623628
  have htrace : WordTrace (prefixWord ++ tailWord_1623628) baseStart_1623628 baseEnd_1623628 := by
    simpa [prefixWord, tailWord_1623628, baseEnd_1623628] using wordTrace_append hprefix tailTrace_1623628
  have hstable : (prefixWord ++ tailWord_1623628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623628).length < 2 ^ (prefixWord ++ tailWord_1623628).sum := by decide
  have hdescent : baseEnd_1623628 < baseStart_1623628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623756 : List Nat := [2, 2, 1, 5, 2, 1, 3, 1, 2, 3]
def baseStart_1623756 : Nat := 118140960795 + 1623756 * 2 ^ 59
def prefixEnd_1623756 : Nat := 4983230072969 + 3 ^ 40 * 1623756 * 2
def baseEnd_1623756 : Nat := 555844862414702853921659

theorem tailTrace_1623756 : CollatzResearch.WordTrace tailWord_1623756 prefixEnd_1623756 555844862414702853921659 := by
  unfold tailWord_1623756
  simp only [CollatzResearch.WordTrace]
  refine ⟨29611623352708401145849561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39482164470277868194466081 29611623352708401145849561)
  ·
    refine ⟨22208717514531300859387171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29611623352708401145849561 22208717514531300859387171)
    ·
      refine ⟨33313076271796951289080757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22208717514531300859387171 33313076271796951289080757)
      ·
        refine ⟨3123100900480964183351321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33313076271796951289080757 3123100900480964183351321)
        ·
          refine ⟨2342325675360723137513491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3123100900480964183351321 2342325675360723137513491)
          ·
            refine ⟨3513488513041084706270237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342325675360723137513491 3513488513041084706270237)
            ·
              refine ⟨1317558192390406764851339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3513488513041084706270237 1317558192390406764851339)
              ·
                refine ⟨1976337288585610147277009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1317558192390406764851339 1976337288585610147277009)
                ·
                  refine ⟨1482252966439207610457757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1976337288585610147277009 1482252966439207610457757)
                  ·
                    refine ⟨555844862414702853921659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1482252966439207610457757 555844862414702853921659)
                    ·
                      rfl

theorem cell22_1623756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_1623756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623756 prefixEnd_1623756 := by exact prefixLift 1623756
  have htrace : WordTrace (prefixWord ++ tailWord_1623756) baseStart_1623756 baseEnd_1623756 := by
    simpa [prefixWord, tailWord_1623756, baseEnd_1623756] using wordTrace_append hprefix tailTrace_1623756
  have hstable : (prefixWord ++ tailWord_1623756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623756).length < 2 ^ (prefixWord ++ tailWord_1623756).sum := by decide
  have hdescent : baseEnd_1623756 < baseStart_1623756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623859 : List Nat := [1, 1, 1, 2, 7, 1, 1, 4, 4]
def baseStart_1623859 : Nat := 118140960795 + 1623859 * 2 ^ 59
def prefixEnd_1623859 : Nat := 4983230072969 + 3 ^ 40 * 1623859 * 2
def baseEnd_1623859 : Nat := 185293373806548306198781

theorem tailTrace_1623859 : CollatzResearch.WordTrace tailWord_1623859 prefixEnd_1623859 185293373806548306198781 := by
  unfold tailWord_1623859
  simp only [CollatzResearch.WordTrace]
  refine ⟨59227003424043650882698631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39484668949362433921799087 59227003424043650882698631)
  ·
    refine ⟨88840505136065476324047947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59227003424043650882698631 88840505136065476324047947)
    ·
      refine ⟨133260757704098214486071921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88840505136065476324047947 133260757704098214486071921)
      ·
        refine ⟨99945568278073660864553941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133260757704098214486071921 99945568278073660864553941)
        ·
          refine ⟨2342474256517351426512983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 99945568278073660864553941 2342474256517351426512983)
          ·
            refine ⟨3513711384776027139769475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342474256517351426512983 3513711384776027139769475)
            ·
              refine ⟨5270567077164040709654213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3513711384776027139769475 5270567077164040709654213)
              ·
                refine ⟨988231326968257633060165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5270567077164040709654213 988231326968257633060165)
                ·
                  refine ⟨185293373806548306198781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 988231326968257633060165 185293373806548306198781)
                  ·
                    rfl

theorem cell22_1623859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 4].length) (baseStart_1623859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623859 prefixEnd_1623859 := by exact prefixLift 1623859
  have htrace : WordTrace (prefixWord ++ tailWord_1623859) baseStart_1623859 baseEnd_1623859 := by
    simpa [prefixWord, tailWord_1623859, baseEnd_1623859] using wordTrace_append hprefix tailTrace_1623859
  have hstable : (prefixWord ++ tailWord_1623859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623859).length < 2 ^ (prefixWord ++ tailWord_1623859).sum := by decide
  have hdescent : baseEnd_1623859 < baseStart_1623859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623889 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 2, 4]
def baseStart_1623889 : Nat := 118140960795 + 1623889 * 2 ^ 59
def prefixEnd_1623889 : Nat := 4983230072969 + 3 ^ 40 * 1623889 * 2
def baseEnd_1623889 : Nat := 555890391032734840346251

theorem tailTrace_1623889 : CollatzResearch.WordTrace tailWord_1623889 prefixEnd_1623889 555890391032734840346251 := by
  unfold tailWord_1623889
  simp only [CollatzResearch.WordTrace]
  refine ⟨59228097613934966006290721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39485398409289977337527147 59228097613934966006290721)
  ·
    refine ⟨44421073210451224504718041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59228097613934966006290721 44421073210451224504718041)
    ·
      refine ⟨33315804907838418378538531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44421073210451224504718041 33315804907838418378538531)
      ·
        refine ⟨49973707361757627567807797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33315804907838418378538531 49973707361757627567807797)
        ·
          refine ⟨4685035065164777584481981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49973707361757627567807797 4685035065164777584481981)
          ·
            refine ⟨1756888149436791594180743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4685035065164777584481981 1756888149436791594180743)
            ·
              refine ⟨2635332224155187391271115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756888149436791594180743 2635332224155187391271115)
              ·
                refine ⟨3952998336232781086906673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2635332224155187391271115 3952998336232781086906673)
                ·
                  refine ⟨2964748752174585815180005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3952998336232781086906673 2964748752174585815180005)
                  ·
                    refine ⟨555890391032734840346251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2964748752174585815180005 555890391032734840346251)
                    ·
                      rfl

theorem cell22_1623889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_1623889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623889 prefixEnd_1623889 := by exact prefixLift 1623889
  have htrace : WordTrace (prefixWord ++ tailWord_1623889) baseStart_1623889 baseEnd_1623889 := by
    simpa [prefixWord, tailWord_1623889, baseEnd_1623889] using wordTrace_append hprefix tailTrace_1623889
  have hstable : (prefixWord ++ tailWord_1623889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623889).length < 2 ^ (prefixWord ++ tailWord_1623889).sum := by decide
  have hdescent : baseEnd_1623889 < baseStart_1623889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623908 : List Nat := [2, 3, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_1623908 : Nat := 118140960795 + 1623908 * 2 ^ 59
def prefixEnd_1623908 : Nat := 4983230072969 + 3 ^ 40 * 1623908 * 2
def baseEnd_1623908 : Nat := 555896895121025124121193

theorem tailTrace_1623908 : CollatzResearch.WordTrace tailWord_1623908 prefixEnd_1623908 555896895121025124121193 := by
  unfold tailWord_1623908
  simp only [CollatzResearch.WordTrace]
  refine ⟨29614395300433066125616189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39485860400577421500821585 29614395300433066125616189)
  ·
    refine ⟨11105398237662399797106071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29614395300433066125616189 11105398237662399797106071)
    ·
      refine ⟨16658097356493599695659107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11105398237662399797106071 16658097356493599695659107)
      ·
        refine ⟨24987146034740399543488661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16658097356493599695659107 24987146034740399543488661)
        ·
          refine ⟨1171272470378456228601031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24987146034740399543488661 1171272470378456228601031)
          ·
            refine ⟨1756908705567684342901547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171272470378456228601031 1756908705567684342901547)
            ·
              refine ⟨2635363058351526514352321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756908705567684342901547 2635363058351526514352321)
              ·
                refine ⟨1976522293763644885764241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2635363058351526514352321 1976522293763644885764241)
                ·
                  refine ⟨1482391720322733664323181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1976522293763644885764241 1482391720322733664323181)
                  ·
                    refine ⟨555896895121025124121193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1482391720322733664323181 555896895121025124121193)
                    ·
                      rfl

theorem cell22_1623908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_1623908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623908 prefixEnd_1623908 := by exact prefixLift 1623908
  have htrace : WordTrace (prefixWord ++ tailWord_1623908) baseStart_1623908 baseEnd_1623908 := by
    simpa [prefixWord, tailWord_1623908, baseEnd_1623908] using wordTrace_append hprefix tailTrace_1623908
  have hstable : (prefixWord ++ tailWord_1623908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623908).length < 2 ^ (prefixWord ++ tailWord_1623908).sum := by decide
  have hdescent : baseEnd_1623908 < baseStart_1623908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623970 : List Nat := [3, 3, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_1623970 : Nat := 118140960795 + 1623970 * 2 ^ 59
def prefixEnd_1623970 : Nat := 4983230072969 + 3 ^ 40 * 1623970 * 2
def baseEnd_1623970 : Nat := 555918118988077629071003

theorem tailTrace_1623970 : CollatzResearch.WordTrace tailWord_1623970 prefixEnd_1623970 555918118988077629071003 := by
  unfold tailWord_1623970
  simp only [CollatzResearch.WordTrace]
  refine ⟨14807762981660379209997341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39487367951094344559992909 14807762981660379209997341)
  ·
    refine ⟨5552911118122642203749003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14807762981660379209997341 5552911118122642203749003)
    ·
      refine ⟨8329366677183963305623505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5552911118122642203749003 8329366677183963305623505)
      ·
        refine ⟨6247025007887972479217629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8329366677183963305623505 6247025007887972479217629)
        ·
          refine ⟨2342634377957989679706611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6247025007887972479217629 2342634377957989679706611)
          ·
            refine ⟨3513951566936984519559917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342634377957989679706611 3513951566936984519559917)
            ·
              refine ⟨1317731837601369194834969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3513951566936984519559917 1317731837601369194834969)
              ·
                refine ⟨988298878201026896126227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1317731837601369194834969 988298878201026896126227)
                ·
                  refine ⟨1482448317301540344189341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 988298878201026896126227 1482448317301540344189341)
                  ·
                    refine ⟨555918118988077629071003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1482448317301540344189341 555918118988077629071003)
                    ·
                      rfl

theorem cell22_1623970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_1623970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623970 prefixEnd_1623970 := by exact prefixLift 1623970
  have htrace : WordTrace (prefixWord ++ tailWord_1623970) baseStart_1623970 baseEnd_1623970 := by
    simpa [prefixWord, tailWord_1623970, baseEnd_1623970] using wordTrace_append hprefix tailTrace_1623970
  have hstable : (prefixWord ++ tailWord_1623970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623970).length < 2 ^ (prefixWord ++ tailWord_1623970).sum := by decide
  have hdescent : baseEnd_1623970 < baseStart_1623970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623992 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 1, 5]
def baseStart_1623992 : Nat := 118140960795 + 1623992 * 2 ^ 59
def prefixEnd_1623992 : Nat := 4983230072969 + 3 ^ 40 * 1623992 * 2
def baseEnd_1623992 : Nat := 555925650037676905020935

theorem tailTrace_1623992 : CollatzResearch.WordTrace tailWord_1623992 prefixEnd_1623992 555925650037676905020935 := by
  unfold tailWord_1623992
  simp only [CollatzResearch.WordTrace]
  refine ⟨29615927166280907298645115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39487902888374543064860153 29615927166280907298645115)
  ·
    refine ⟨44423890749421360947967673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29615927166280907298645115 44423890749421360947967673)
    ·
      refine ⟨33317918062066020710975755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44423890749421360947967673 33317918062066020710975755)
      ·
        refine ⟨49976877093099031066463633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33317918062066020710975755 49976877093099031066463633)
        ·
          refine ⟨37482657819824273299847725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49976877093099031066463633 37482657819824273299847725)
          ·
            refine ⟨14055996682434102487442897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37482657819824273299847725 14055996682434102487442897)
            ·
              refine ⟨10541997511825576865582173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14055996682434102487442897 10541997511825576865582173)
              ·
                refine ⟨3953249066934591324593315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10541997511825576865582173 3953249066934591324593315)
                ·
                  refine ⟨5929873600401886986889973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3953249066934591324593315 5929873600401886986889973)
                  ·
                    refine ⟨555925650037676905020935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5929873600401886986889973 555925650037676905020935)
                    ·
                      rfl

theorem cell22_1623992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_1623992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623992 prefixEnd_1623992 := by exact prefixLift 1623992
  have htrace : WordTrace (prefixWord ++ tailWord_1623992) baseStart_1623992 baseEnd_1623992 := by
    simpa [prefixWord, tailWord_1623992, baseEnd_1623992] using wordTrace_append hprefix tailTrace_1623992
  have hstable : (prefixWord ++ tailWord_1623992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623992).length < 2 ^ (prefixWord ++ tailWord_1623992).sum := by decide
  have hdescent : baseEnd_1623992 < baseStart_1623992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623996 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 3, 4]
def baseStart_1623996 : Nat := 118140960795 + 1623996 * 2 ^ 59
def prefixEnd_1623996 : Nat := 4983230072969 + 3 ^ 40 * 1623996 * 2
def baseEnd_1623996 : Nat := 555927019319422227920923

theorem tailTrace_1623996 : CollatzResearch.WordTrace tailWord_1623996 prefixEnd_1623996 555927019319422227920923 := by
  unfold tailWord_1623996
  simp only [CollatzResearch.WordTrace]
  refine ⟨29616000112273661640217921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39488000149698215520290561 29616000112273661640217921)
  ·
    refine ⟨22212000084205246230163441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29616000112273661640217921 22212000084205246230163441)
    ·
      refine ⟨16659000063153934672622581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22212000084205246230163441 16659000063153934672622581)
      ·
        refine ⟨1561781255920681375558367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16659000063153934672622581 1561781255920681375558367)
        ·
          refine ⟨2342671883881022063337551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1561781255920681375558367 2342671883881022063337551)
          ·
            refine ⟨3514007825821533095006327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342671883881022063337551 3514007825821533095006327)
            ·
              refine ⟨5271011738732299642509491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514007825821533095006327 5271011738732299642509491)
              ·
                refine ⟨7906517608098449463764237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271011738732299642509491 7906517608098449463764237)
                ·
                  refine ⟨2964944103036918548911589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7906517608098449463764237 2964944103036918548911589)
                  ·
                    refine ⟨555927019319422227920923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2964944103036918548911589 555927019319422227920923)
                    ·
                      rfl

theorem cell22_1623996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_1623996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623996 prefixEnd_1623996 := by exact prefixLift 1623996
  have htrace : WordTrace (prefixWord ++ tailWord_1623996) baseStart_1623996 baseEnd_1623996 := by
    simpa [prefixWord, tailWord_1623996, baseEnd_1623996] using wordTrace_append hprefix tailTrace_1623996
  have hstable : (prefixWord ++ tailWord_1623996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623996).length < 2 ^ (prefixWord ++ tailWord_1623996).sum := by decide
  have hdescent : baseEnd_1623996 < baseStart_1623996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624101 : List Nat := [1, 3, 1, 2, 2, 4, 3, 1, 5]
def baseStart_1624101 : Nat := 118140960795 + 1624101 * 2 ^ 59
def prefixEnd_1624101 : Nat := 4983230072969 + 3 ^ 40 * 1624101 * 2
def baseEnd_1624101 : Nat := 185320987655078984681867

theorem tailTrace_1624101 : CollatzResearch.WordTrace tailWord_1624101 prefixEnd_1624101 185320987655078984681867 := by
  unfold tailWord_1624101
  simp only [CollatzResearch.WordTrace]
  refine ⟨59235829889166926213008157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39490553259444617475338771 59235829889166926213008157)
  ·
    refine ⟨22213436208437597329878059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59235829889166926213008157 22213436208437597329878059)
    ·
      refine ⟨33320154312656395994817089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22213436208437597329878059 33320154312656395994817089)
      ·
        refine ⟨24990115734492296996112817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33320154312656395994817089 24990115734492296996112817)
        ·
          refine ⟨18742586800869222747084613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24990115734492296996112817 18742586800869222747084613)
          ·
            refine ⟨3514235025162979265078365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18742586800869222747084613 3514235025162979265078365)
            ·
              refine ⟨1317838134436117224404387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3514235025162979265078365 1317838134436117224404387)
              ·
                refine ⟨1976757201654175836606581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1317838134436117224404387 1976757201654175836606581)
                ·
                  refine ⟨185320987655078984681867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1976757201654175836606581 185320987655078984681867)
                  ·
                    rfl

theorem cell22_1624101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_1624101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624101 prefixEnd_1624101 := by exact prefixLift 1624101
  have htrace : WordTrace (prefixWord ++ tailWord_1624101) baseStart_1624101 baseEnd_1624101 := by
    simpa [prefixWord, tailWord_1624101, baseEnd_1624101] using wordTrace_append hprefix tailTrace_1624101
  have hstable : (prefixWord ++ tailWord_1624101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624101).length < 2 ^ (prefixWord ++ tailWord_1624101).sum := by decide
  have hdescent : baseEnd_1624101 < baseStart_1624101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624174 : List Nat := [4, 1, 2, 2, 1, 1, 1, 10]
def baseStart_1624174 : Nat := 118140960795 + 1624174 * 2 ^ 59
def prefixEnd_1624174 : Nat := 4983230072969 + 3 ^ 40 * 1624174 * 2
def baseEnd_1624174 : Nat := 61776439150787677441153

theorem tailTrace_1624174 : CollatzResearch.WordTrace tailWord_1624174 prefixEnd_1624174 61776439150787677441153 := by
  unfold tailWord_1624174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7404811552237807460051947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39492328278601639786943717 7404811552237807460051947)
  ·
    refine ⟨11107217328356711190077921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7404811552237807460051947 11107217328356711190077921)
    ·
      refine ⟨8330412996267533392558441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11107217328356711190077921 8330412996267533392558441)
      ·
        refine ⟨6247809747200650044418831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8330412996267533392558441 6247809747200650044418831)
        ·
          refine ⟨9371714620800975066628247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6247809747200650044418831 9371714620800975066628247)
          ·
            refine ⟨14057571931201462599942371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9371714620800975066628247 14057571931201462599942371)
            ·
              refine ⟨21086357896802193899913557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14057571931201462599942371 21086357896802193899913557)
              ·
                refine ⟨61776439150787677441153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21086357896802193899913557 61776439150787677441153)
                ·
                  rfl

theorem cell22_1624174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_1624174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624174 prefixEnd_1624174 := by exact prefixLift 1624174
  have htrace : WordTrace (prefixWord ++ tailWord_1624174) baseStart_1624174 baseEnd_1624174 := by
    simpa [prefixWord, tailWord_1624174, baseEnd_1624174] using wordTrace_append hprefix tailTrace_1624174
  have hstable : (prefixWord ++ tailWord_1624174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624174).length < 2 ^ (prefixWord ++ tailWord_1624174).sum := by decide
  have hdescent : baseEnd_1624174 < baseStart_1624174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624176 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 2, 4]
def baseStart_1624176 : Nat := 118140960795 + 1624176 * 2 ^ 59
def prefixEnd_1624176 : Nat := 4983230072969 + 3 ^ 40 * 1624176 * 2
def baseEnd_1624176 : Nat := 555988636997961758420371

theorem tailTrace_1624176 : CollatzResearch.WordTrace tailWord_1624176 prefixEnd_1624176 555988636997961758420371 := by
  unfold tailWord_1624176
  simp only [CollatzResearch.WordTrace]
  refine ⟨29619282681947607010994191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39492376909263476014658921 29619282681947607010994191)
  ·
    refine ⟨44428924022921410516491287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29619282681947607010994191 44428924022921410516491287)
    ·
      refine ⟨66643386034382115774736931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44428924022921410516491287 66643386034382115774736931)
      ·
        refine ⟨99965079051573173662105397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66643386034382115774736931 99965079051573173662105397)
        ·
          refine ⟨9371726161084985030822381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99965079051573173662105397 9371726161084985030822381)
          ·
            refine ⟨3514397310406869386558393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9371726161084985030822381 3514397310406869386558393)
            ·
              refine ⟨2635797982805152039918795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3514397310406869386558393 2635797982805152039918795)
              ·
                refine ⟨3953696974207728059878193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2635797982805152039918795 3953696974207728059878193)
                ·
                  refine ⟨2965272730655796044908645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3953696974207728059878193 2965272730655796044908645)
                  ·
                    refine ⟨555988636997961758420371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2965272730655796044908645 555988636997961758420371)
                    ·
                      rfl

theorem cell22_1624176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_1624176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624176 prefixEnd_1624176 := by exact prefixLift 1624176
  have htrace : WordTrace (prefixWord ++ tailWord_1624176) baseStart_1624176 baseEnd_1624176 := by
    simpa [prefixWord, tailWord_1624176, baseEnd_1624176] using wordTrace_append hprefix tailTrace_1624176
  have hstable : (prefixWord ++ tailWord_1624176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624176).length < 2 ^ (prefixWord ++ tailWord_1624176).sum := by decide
  have hdescent : baseEnd_1624176 < baseStart_1624176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624219 : List Nat := [1, 1, 1, 1, 1, 1, 2, 9, 5]
def baseStart_1624219 : Nat := 118140960795 + 1624219 * 2 ^ 59
def prefixEnd_1624219 : Nat := 4983230072969 + 3 ^ 40 * 1624219 * 2
def baseEnd_1624219 : Nat := 185334452258907993198413

theorem tailTrace_1624219 : CollatzResearch.WordTrace tailWord_1624219 prefixEnd_1624219 185334452258907993198413 := by
  unfold tailWord_1624219
  simp only [CollatzResearch.WordTrace]
  refine ⟨59240133702739432365803711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39493422468492954910535807 59240133702739432365803711)
  ·
    refine ⟨88860200554109148548705567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59240133702739432365803711 88860200554109148548705567)
    ·
      refine ⟨133290300831163722823058351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88860200554109148548705567 133290300831163722823058351)
      ·
        refine ⟨199935451246745584234587527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133290300831163722823058351 199935451246745584234587527)
        ·
          refine ⟨299903176870118376351881291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199935451246745584234587527 299903176870118376351881291)
          ·
            refine ⟨449854765305177564527821937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299903176870118376351881291 449854765305177564527821937)
            ·
              refine ⟨337391073978883173395866453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449854765305177564527821937 337391073978883173395866453)
              ·
                refine ⟨1976900824095018594116405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 337391073978883173395866453 1976900824095018594116405)
                ·
                  refine ⟨185334452258907993198413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1976900824095018594116405 185334452258907993198413)
                  ·
                    rfl

theorem cell22_1624219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 5].length) (baseStart_1624219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624219 prefixEnd_1624219 := by exact prefixLift 1624219
  have htrace : WordTrace (prefixWord ++ tailWord_1624219) baseStart_1624219 baseEnd_1624219 := by
    simpa [prefixWord, tailWord_1624219, baseEnd_1624219] using wordTrace_append hprefix tailTrace_1624219
  have hstable : (prefixWord ++ tailWord_1624219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624219).length < 2 ^ (prefixWord ++ tailWord_1624219).sum := by decide
  have hdescent : baseEnd_1624219 < baseStart_1624219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624223 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 3, 3]
def baseStart_1624223 : Nat := 118140960795 + 1624223 * 2 ^ 59
def prefixEnd_1624223 : Nat := 4983230072969 + 3 ^ 40 * 1624223 * 2
def baseEnd_1624223 : Nat := 556004726058469302495227

theorem tailTrace_1624223 : CollatzResearch.WordTrace tailWord_1624223 prefixEnd_1624223 556004726058469302495227 := by
  unfold tailWord_1624223
  simp only [CollatzResearch.WordTrace]
  refine ⟨59240279594724941048949323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39493519729816627365966215 59240279594724941048949323)
  ·
    refine ⟨88860419392087411573423985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59240279594724941048949323 88860419392087411573423985)
    ·
      refine ⟨66645314544065558680067989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88860419392087411573423985 66645314544065558680067989)
      ·
        refine ⟨3123999119253073063128187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66645314544065558680067989 3123999119253073063128187)
        ·
          refine ⟨4685998678879609594692281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3123999119253073063128187 4685998678879609594692281)
          ·
            refine ⟨3514499009159707196019211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4685998678879609594692281 3514499009159707196019211)
            ·
              refine ⟨5271748513739560794028817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514499009159707196019211 5271748513739560794028817)
              ·
                refine ⟨3953811385304670595521613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5271748513739560794028817 3953811385304670595521613)
                ·
                  refine ⟨1482679269489251473320605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3953811385304670595521613 1482679269489251473320605)
                  ·
                    refine ⟨556004726058469302495227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1482679269489251473320605 556004726058469302495227)
                    ·
                      rfl

theorem cell22_1624223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 3].length) (baseStart_1624223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624223 prefixEnd_1624223 := by exact prefixLift 1624223
  have htrace : WordTrace (prefixWord ++ tailWord_1624223) baseStart_1624223 baseEnd_1624223 := by
    simpa [prefixWord, tailWord_1624223, baseEnd_1624223] using wordTrace_append hprefix tailTrace_1624223
  have hstable : (prefixWord ++ tailWord_1624223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624223).length < 2 ^ (prefixWord ++ tailWord_1624223).sum := by decide
  have hdescent : baseEnd_1624223 < baseStart_1624223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624330 : List Nat := [3, 1, 2, 2, 1, 1, 6, 1, 2, 3]
def baseStart_1624330 : Nat := 118140960795 + 1624330 * 2 ^ 59
def prefixEnd_1624330 : Nat := 4983230072969 + 3 ^ 40 * 1624330 * 2
def baseEnd_1624330 : Nat := 556041354345156690069899

theorem tailTrace_1624330 : CollatzResearch.WordTrace tailWord_1624330 prefixEnd_1624330 556041354345156690069899 := by
  unfold tailWord_1624330
  simp only [CollatzResearch.WordTrace]
  refine ⟨14811045551334324580773611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39496121470224865548729629 14811045551334324580773611)
  ·
    refine ⟨22216568327001486871160417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14811045551334324580773611 22216568327001486871160417)
    ·
      refine ⟨16662426245251115153370313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22216568327001486871160417 16662426245251115153370313)
      ·
        refine ⟨12496819683938336365027735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16662426245251115153370313 12496819683938336365027735)
        ·
          refine ⟨18745229525907504547541603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12496819683938336365027735 18745229525907504547541603)
          ·
            refine ⟨28117844288861256821312405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18745229525907504547541603 28117844288861256821312405)
            ·
              refine ⟨1318023951040371413499019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28117844288861256821312405 1318023951040371413499019)
              ·
                refine ⟨1977035926560557120248529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318023951040371413499019 1977035926560557120248529)
                ·
                  refine ⟨1482776944920417840186397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1977035926560557120248529 1482776944920417840186397)
                  ·
                    refine ⟨556041354345156690069899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1482776944920417840186397 556041354345156690069899)
                    ·
                      rfl

theorem cell22_1624330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_1624330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624330 prefixEnd_1624330 := by exact prefixLift 1624330
  have htrace : WordTrace (prefixWord ++ tailWord_1624330) baseStart_1624330 baseEnd_1624330 := by
    simpa [prefixWord, tailWord_1624330, baseEnd_1624330] using wordTrace_append hprefix tailTrace_1624330
  have hstable : (prefixWord ++ tailWord_1624330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624330).length < 2 ^ (prefixWord ++ tailWord_1624330).sum := by decide
  have hdescent : baseEnd_1624330 < baseStart_1624330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624366 : List Nat := [4, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_1624366 : Nat := 118140960795 + 1624366 * 2 ^ 59
def prefixEnd_1624366 : Nat := 4983230072969 + 3 ^ 40 * 1624366 * 2
def baseEnd_1624366 : Nat := 185351225960288198723263

theorem tailTrace_1624366 : CollatzResearch.WordTrace tailWord_1624366 prefixEnd_1624366 185351225960288198723263 := by
  unfold tailWord_1624366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7405686904150859558925619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39496996822137917647603301 7405686904150859558925619)
  ·
    refine ⟨11108530356226289338388429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7405686904150859558925619 11108530356226289338388429)
    ·
      refine ⟨4165698883584858501895661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11108530356226289338388429 4165698883584858501895661)
      ·
        refine ⟨1562137081344321938210873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4165698883584858501895661 1562137081344321938210873)
        ·
          refine ⟨1171602811008241453658155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1562137081344321938210873 1171602811008241453658155)
          ·
            refine ⟨1757404216512362180487233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171602811008241453658155 1757404216512362180487233)
            ·
              refine ⟨1318053162384271635365425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757404216512362180487233 1318053162384271635365425)
              ·
                refine ⟨988539871788203726524069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318053162384271635365425 988539871788203726524069)
                ·
                  refine ⟨185351225960288198723263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 988539871788203726524069 185351225960288198723263)
                  ·
                    rfl

theorem cell22_1624366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_1624366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624366 prefixEnd_1624366 := by exact prefixLift 1624366
  have htrace : WordTrace (prefixWord ++ tailWord_1624366) baseStart_1624366 baseEnd_1624366 := by
    simpa [prefixWord, tailWord_1624366, baseEnd_1624366] using wordTrace_append hprefix tailTrace_1624366
  have hstable : (prefixWord ++ tailWord_1624366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624366).length < 2 ^ (prefixWord ++ tailWord_1624366).sum := by decide
  have hdescent : baseEnd_1624366 < baseStart_1624366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624510 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_1624510 : Nat := 118140960795 + 1624510 * 2 ^ 59
def prefixEnd_1624510 : Nat := 4983230072969 + 3 ^ 40 * 1624510 * 2
def baseEnd_1624510 : Nat := 556102972023696220569347

theorem tailTrace_1624510 : CollatzResearch.WordTrace tailWord_1624510 prefixEnd_1624510 556102972023696220569347 := by
  unfold tailWord_1624510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7406343418085648633080873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39500498229790126043097989 7406343418085648633080873)
  ·
    refine ⟨5554757563564236474810655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7406343418085648633080873 5554757563564236474810655)
    ·
      refine ⟨8332136345346354712215983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5554757563564236474810655 8332136345346354712215983)
      ·
        refine ⟨12498204518019532068323975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8332136345346354712215983 12498204518019532068323975)
        ·
          refine ⟨18747306777029298102485963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12498204518019532068323975 18747306777029298102485963)
          ·
            refine ⟨28120960165543947153728945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18747306777029298102485963 28120960165543947153728945)
            ·
              refine ⟨21090720124157960365296709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28120960165543947153728945 21090720124157960365296709)
              ·
                refine ⟨3954510023279617568493133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21090720124157960365296709 3954510023279617568493133)
                ·
                  refine ⟨1482941258729856588184925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3954510023279617568493133 1482941258729856588184925)
                  ·
                    refine ⟨556102972023696220569347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1482941258729856588184925 556102972023696220569347)
                    ·
                      rfl

theorem cell22_1624510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_1624510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624510 prefixEnd_1624510 := by exact prefixLift 1624510
  have htrace : WordTrace (prefixWord ++ tailWord_1624510) baseStart_1624510 baseEnd_1624510 := by
    simpa [prefixWord, tailWord_1624510, baseEnd_1624510] using wordTrace_append hprefix tailTrace_1624510
  have hstable : (prefixWord ++ tailWord_1624510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624510).length < 2 ^ (prefixWord ++ tailWord_1624510).sum := by decide
  have hdescent : baseEnd_1624510 < baseStart_1624510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624538 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_1624538 : Nat := 118140960795 + 1624538 * 2 ^ 59
def prefixEnd_1624538 : Nat := 4983230072969 + 3 ^ 40 * 1624538 * 2
def baseEnd_1624538 : Nat := 556112556995913480869261

theorem tailTrace_1624538 : CollatzResearch.WordTrace tailWord_1624538 prefixEnd_1624538 556112556995913480869261 := by
  unfold tailWord_1624538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14812942147145937461666567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39501179059055833231110845 14812942147145937461666567)
  ·
    refine ⟨22219413220718906192499851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14812942147145937461666567 22219413220718906192499851)
    ·
      refine ⟨33329119831078359288749777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22219413220718906192499851 33329119831078359288749777)
      ·
        refine ⟨24996839873308769466562333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33329119831078359288749777 24996839873308769466562333)
        ·
          refine ⟨9373814952490788549960875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24996839873308769466562333 9373814952490788549960875)
          ·
            refine ⟨14060722428736182824941313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9373814952490788549960875 14060722428736182824941313)
            ·
              refine ⟨10545541821552137118705985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14060722428736182824941313 10545541821552137118705985)
              ·
                refine ⟨7909156366164102839029489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10545541821552137118705985 7909156366164102839029489)
                ·
                  refine ⟨5931867274623077129272117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7909156366164102839029489 5931867274623077129272117)
                  ·
                    refine ⟨556112556995913480869261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5931867274623077129272117 556112556995913480869261)
                    ·
                      rfl

theorem cell22_1624538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_1624538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624538 prefixEnd_1624538 := by exact prefixLift 1624538
  have htrace : WordTrace (prefixWord ++ tailWord_1624538) baseStart_1624538 baseEnd_1624538 := by
    simpa [prefixWord, tailWord_1624538, baseEnd_1624538] using wordTrace_append hprefix tailTrace_1624538
  have hstable : (prefixWord ++ tailWord_1624538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624538).length < 2 ^ (prefixWord ++ tailWord_1624538).sum := by decide
  have hdescent : baseEnd_1624538 < baseStart_1624538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624568 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 6]
def baseStart_1624568 : Nat := 118140960795 + 1624568 * 2 ^ 59
def prefixEnd_1624568 : Nat := 4983230072969 + 3 ^ 40 * 1624568 * 2
def baseEnd_1624568 : Nat := 185374275536334467539723

theorem tailTrace_1624568 : CollatzResearch.WordTrace tailWord_1624568 prefixEnd_1624568 185374275536334467539723 := by
  unfold tailWord_1624568
  simp only [CollatzResearch.WordTrace]
  refine ⟨29626431389237532485129179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39501908518983376646838905 29626431389237532485129179)
  ·
    refine ⟨44439647083856298727693769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29626431389237532485129179 44439647083856298727693769)
    ·
      refine ⟨33329735312892224045770327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44439647083856298727693769 33329735312892224045770327)
      ·
        refine ⟨49994602969338336068655491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33329735312892224045770327 49994602969338336068655491)
        ·
          refine ⟨74991904454007504102983237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49994602969338336068655491 74991904454007504102983237)
          ·
            refine ⟨14060982085126407019309357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74991904454007504102983237 14060982085126407019309357)
            ·
              refine ⟨5272868281922402632241009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14060982085126407019309357 5272868281922402632241009)
              ·
                refine ⟨3954651211441801974180757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5272868281922402632241009 3954651211441801974180757)
                ·
                  refine ⟨185374275536334467539723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3954651211441801974180757 185374275536334467539723)
                  ·
                    rfl

theorem cell22_1624568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_1624568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624568 prefixEnd_1624568 := by exact prefixLift 1624568
  have htrace : WordTrace (prefixWord ++ tailWord_1624568) baseStart_1624568 baseEnd_1624568 := by
    simpa [prefixWord, tailWord_1624568, baseEnd_1624568] using wordTrace_append hprefix tailTrace_1624568
  have hstable : (prefixWord ++ tailWord_1624568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624568).length < 2 ^ (prefixWord ++ tailWord_1624568).sum := by decide
  have hdescent : baseEnd_1624568 < baseStart_1624568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624587 : List Nat := [1, 1, 1, 1, 7, 1, 4, 1, 1, 4]
def baseStart_1624587 : Nat := 118140960795 + 1624587 * 2 ^ 59
def prefixEnd_1624587 : Nat := 4983230072969 + 3 ^ 40 * 1624587 * 2
def baseEnd_1624587 : Nat := 556129330697293686394111

theorem tailTrace_1624587 : CollatzResearch.WordTrace tailWord_1624587 prefixEnd_1624587 556129330697293686394111 := by
  unfold tailWord_1624587
  simp only [CollatzResearch.WordTrace]
  refine ⟨59253555765406231215200015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39502370510270820810133343 59253555765406231215200015)
  ·
    refine ⟨88880333648109346822800023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59253555765406231215200015 88880333648109346822800023)
    ·
      refine ⟨133320500472164020234200035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88880333648109346822800023 133320500472164020234200035)
      ·
        refine ⟨199980750708246030351300053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133320500472164020234200035 199980750708246030351300053)
        ·
          refine ⟨4687048844724516336358595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 199980750708246030351300053 4687048844724516336358595)
          ·
            refine ⟨7030573267086774504537893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4687048844724516336358595 7030573267086774504537893)
            ·
              refine ⟨1318232487578770219600855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7030573267086774504537893 1318232487578770219600855)
              ·
                refine ⟨1977348731368155329401283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318232487578770219600855 1977348731368155329401283)
                ·
                  refine ⟨2966023097052232994101925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977348731368155329401283 2966023097052232994101925)
                  ·
                    refine ⟨556129330697293686394111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2966023097052232994101925 556129330697293686394111)
                    ·
                      rfl

theorem cell22_1624587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 1, 4].length) (baseStart_1624587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624587 prefixEnd_1624587 := by exact prefixLift 1624587
  have htrace : WordTrace (prefixWord ++ tailWord_1624587) baseStart_1624587 baseEnd_1624587 := by
    simpa [prefixWord, tailWord_1624587, baseEnd_1624587] using wordTrace_append hprefix tailTrace_1624587
  have hstable : (prefixWord ++ tailWord_1624587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624587).length < 2 ^ (prefixWord ++ tailWord_1624587).sum := by decide
  have hdescent : baseEnd_1624587 < baseStart_1624587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624668 : List Nat := [2, 2, 4, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1624668 : Nat := 118140960795 + 1624668 * 2 ^ 59
def prefixEnd_1624668 : Nat := 4983230072969 + 3 ^ 40 * 1624668 * 2
def baseEnd_1624668 : Nat := 556157058652636475118863

theorem tailTrace_1624668 : CollatzResearch.WordTrace tailWord_1624668 prefixEnd_1624668 556157058652636475118863 := by
  unfold tailWord_1624668
  simp only [CollatzResearch.WordTrace]
  refine ⟨29628255039056391024449329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39504340052075188032599105 29628255039056391024449329)
  ·
    refine ⟨22221191279292293268336997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29628255039056391024449329 22221191279292293268336997)
    ·
      refine ⟨4166473364867304987813187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22221191279292293268336997 4166473364867304987813187)
      ·
        refine ⟨6249710047300957481719781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4166473364867304987813187 6249710047300957481719781)
        ·
          refine ⟨1171820633868929527822459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6249710047300957481719781 1171820633868929527822459)
          ·
            refine ⟨1757730950803394291733689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171820633868929527822459 1757730950803394291733689)
            ·
              refine ⟨1318298213102545718800267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757730950803394291733689 1318298213102545718800267)
              ·
                refine ⟨1977447319653818578200401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318298213102545718800267 1977447319653818578200401)
                ·
                  refine ⟨1483085489740363933650301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1977447319653818578200401 1483085489740363933650301)
                  ·
                    refine ⟨556157058652636475118863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1483085489740363933650301 556157058652636475118863)
                    ·
                      rfl

theorem cell22_1624668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1624668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624668 prefixEnd_1624668 := by exact prefixLift 1624668
  have htrace : WordTrace (prefixWord ++ tailWord_1624668) baseStart_1624668 baseEnd_1624668 := by
    simpa [prefixWord, tailWord_1624668, baseEnd_1624668] using wordTrace_append hprefix tailTrace_1624668
  have hstable : (prefixWord ++ tailWord_1624668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624668).length < 2 ^ (prefixWord ++ tailWord_1624668).sum := by decide
  have hdescent : baseEnd_1624668 < baseStart_1624668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624675 : List Nat := [1, 1, 1, 5, 1, 2, 3, 3, 5]
def baseStart_1624675 : Nat := 118140960795 + 1624675 * 2 ^ 59
def prefixEnd_1624675 : Nat := 4983230072969 + 3 ^ 40 * 1624675 * 2
def baseEnd_1624675 : Nat := 185386484965230263397947

theorem tailTrace_1624675 : CollatzResearch.WordTrace tailWord_1624675 prefixEnd_1624675 185386484965230263397947 := by
  unfold tailWord_1624675
  simp only [CollatzResearch.WordTrace]
  refine ⟨59256765389087422244403479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39504510259391614829602319 59256765389087422244403479)
  ·
    refine ⟨88885148083631133366605219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59256765389087422244403479 88885148083631133366605219)
    ·
      refine ⟨133327722125446700049907829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88885148083631133366605219 133327722125446700049907829)
      ·
        refine ⟨12499473949260628129678859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133327722125446700049907829 12499473949260628129678859)
        ·
          refine ⟨18749210923890942194518289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12499473949260628129678859 18749210923890942194518289)
          ·
            refine ⟨14061908192918206645888717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18749210923890942194518289 14061908192918206645888717)
            ·
              refine ⟨5273215572344327492208269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14061908192918206645888717 5273215572344327492208269)
              ·
                refine ⟨1977455839629122809578101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5273215572344327492208269 1977455839629122809578101)
                ·
                  refine ⟨185386484965230263397947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1977455839629122809578101 185386484965230263397947)
                  ·
                    rfl

theorem cell22_1624675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 5].length) (baseStart_1624675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624675 prefixEnd_1624675 := by exact prefixLift 1624675
  have htrace : WordTrace (prefixWord ++ tailWord_1624675) baseStart_1624675 baseEnd_1624675 := by
    simpa [prefixWord, tailWord_1624675, baseEnd_1624675] using wordTrace_append hprefix tailTrace_1624675
  have hstable : (prefixWord ++ tailWord_1624675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624675).length < 2 ^ (prefixWord ++ tailWord_1624675).sum := by decide
  have hdescent : baseEnd_1624675 < baseStart_1624675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624703 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 10]
def baseStart_1624703 : Nat := 118140960795 + 1624703 * 2 ^ 59
def prefixEnd_1624703 : Nat := 4983230072969 + 3 ^ 40 * 1624703 * 2
def baseEnd_1624703 : Nat := 185389679955969350164585

theorem tailTrace_1624703 : CollatzResearch.WordTrace tailWord_1624703 prefixEnd_1624703 185389679955969350164585 := by
  unfold tailWord_1624703
  simp only [CollatzResearch.WordTrace]
  refine ⟨59257786632985983026422763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39505191088657322017615175 59257786632985983026422763)
  ·
    refine ⟨88886679949478974539634145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59257786632985983026422763 88886679949478974539634145)
    ·
      refine ⟨66665009962109230904725609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88886679949478974539634145 66665009962109230904725609)
      ·
        refine ⟨49998757471581923178544207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66665009962109230904725609 49998757471581923178544207)
        ·
          refine ⟨74998136207372884767816311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49998757471581923178544207 74998136207372884767816311)
          ·
            refine ⟨112497204311059327151724467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74998136207372884767816311 112497204311059327151724467)
            ·
              refine ⟨168745806466588990727586701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112497204311059327151724467 168745806466588990727586701)
              ·
                refine ⟨63279677424970871522845013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168745806466588990727586701 63279677424970871522845013)
                ·
                  refine ⟨185389679955969350164585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 63279677424970871522845013 185389679955969350164585)
                  ·
                    rfl

theorem cell22_1624703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 10].length) (baseStart_1624703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624703 prefixEnd_1624703 := by exact prefixLift 1624703
  have htrace : WordTrace (prefixWord ++ tailWord_1624703) baseStart_1624703 baseEnd_1624703 := by
    simpa [prefixWord, tailWord_1624703, baseEnd_1624703] using wordTrace_append hprefix tailTrace_1624703
  have hstable : (prefixWord ++ tailWord_1624703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624703).length < 2 ^ (prefixWord ++ tailWord_1624703).sum := by decide
  have hdescent : baseEnd_1624703 < baseStart_1624703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624722 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1624722 : Nat := 118140960795 + 1624722 * 2 ^ 59
def prefixEnd_1624722 : Nat := 4983230072969 + 3 ^ 40 * 1624722 * 2
def baseEnd_1624722 : Nat := 556175543956198334268697

theorem tailTrace_1624722 : CollatzResearch.WordTrace tailWord_1624722 prefixEnd_1624722 556175543956198334268697 := by
  unfold tailWord_1624722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14814619904979287317841105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39505653079944766180909613 14814619904979287317841105)
  ·
    refine ⟨11110964928734465488380829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14814619904979287317841105 11110964928734465488380829)
    ·
      refine ⟨4166611848275424558142811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11110964928734465488380829 4166611848275424558142811)
      ·
        refine ⟨6249917772413136837214217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4166611848275424558142811 6249917772413136837214217)
        ·
          refine ⟨4687438329309852627910663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6249917772413136837214217 4687438329309852627910663)
          ·
            refine ⟨7031157493964778941865995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4687438329309852627910663 7031157493964778941865995)
            ·
              refine ⟨10546736240947168412798993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7031157493964778941865995 10546736240947168412798993)
              ·
                refine ⟨7910052180710376309599245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10546736240947168412798993 7910052180710376309599245)
                ·
                  refine ⟨2966269567766391116099717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7910052180710376309599245 2966269567766391116099717)
                  ·
                    refine ⟨556175543956198334268697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2966269567766391116099717 556175543956198334268697)
                    ·
                      rfl

theorem cell22_1624722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1624722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624722 prefixEnd_1624722 := by exact prefixLift 1624722
  have htrace : WordTrace (prefixWord ++ tailWord_1624722) baseStart_1624722 baseEnd_1624722 := by
    simpa [prefixWord, tailWord_1624722, baseEnd_1624722] using wordTrace_append hprefix tailTrace_1624722
  have hstable : (prefixWord ++ tailWord_1624722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624722).length < 2 ^ (prefixWord ++ tailWord_1624722).sum := by decide
  have hdescent : baseEnd_1624722 < baseStart_1624722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624737 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 6]
def baseStart_1624737 : Nat := 118140960795 + 1624737 * 2 ^ 59
def prefixEnd_1624737 : Nat := 4983230072969 + 3 ^ 40 * 1624737 * 2
def baseEnd_1624737 : Nat := 185393559587581098381217

theorem tailTrace_1624737 : CollatzResearch.WordTrace tailWord_1624737 prefixEnd_1624737 185393559587581098381217 := by
  unfold tailWord_1624737
  simp only [CollatzResearch.WordTrace]
  refine ⟨59259026714862806833160465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39506017809908537888773643 59259026714862806833160465)
  ·
    refine ⟨44444270036147105124870349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59259026714862806833160465 44444270036147105124870349)
    ·
      refine ⟨16666601263555164421826381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44444270036147105124870349 16666601263555164421826381)
      ·
        refine ⟨6249975473833186658184893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16666601263555164421826381 6249975473833186658184893)
        ·
          refine ⟨2343740802687444996819335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6249975473833186658184893 2343740802687444996819335)
          ·
            refine ⟨3515611204031167495229003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343740802687444996819335 3515611204031167495229003)
            ·
              refine ⟨5273416806046751242843505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3515611204031167495229003 5273416806046751242843505)
              ·
                refine ⟨3955062604535063432132629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5273416806046751242843505 3955062604535063432132629)
                ·
                  refine ⟨185393559587581098381217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3955062604535063432132629 185393559587581098381217)
                  ·
                    rfl

theorem cell22_1624737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 6].length) (baseStart_1624737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624737 prefixEnd_1624737 := by exact prefixLift 1624737
  have htrace : WordTrace (prefixWord ++ tailWord_1624737) baseStart_1624737 baseEnd_1624737 := by
    simpa [prefixWord, tailWord_1624737, baseEnd_1624737] using wordTrace_append hprefix tailTrace_1624737
  have hstable : (prefixWord ++ tailWord_1624737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624737).length < 2 ^ (prefixWord ++ tailWord_1624737).sum := by decide
  have hdescent : baseEnd_1624737 < baseStart_1624737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624765 : List Nat := [1, 4, 1, 2, 1, 4, 9]
def baseStart_1624765 : Nat := 118140960795 + 1624765 * 2 ^ 59
def prefixEnd_1624765 : Nat := 4983230072969 + 3 ^ 40 * 1624765 * 2
def baseEnd_1624765 : Nat := 20599639397591131683095

theorem tailTrace_1624765 : CollatzResearch.WordTrace tailWord_1624765 prefixEnd_1624765 20599639397591131683095 := by
  unfold tailWord_1624765
  simp only [CollatzResearch.WordTrace]
  refine ⟨59260047958761367615179749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39506698639174245076786499 59260047958761367615179749)
  ·
    refine ⟨11111258992267756427846203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59260047958761367615179749 11111258992267756427846203)
    ·
      refine ⟨16666888488401634641769305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11111258992267756427846203 16666888488401634641769305)
      ·
        refine ⟨12500166366301225981326979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16666888488401634641769305 12500166366301225981326979)
        ·
          refine ⟨18750249549451838971990469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12500166366301225981326979 18750249549451838971990469)
          ·
            refine ⟨3515671790522219807248213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18750249549451838971990469 3515671790522219807248213)
            ·
              refine ⟨20599639397591131683095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3515671790522219807248213 20599639397591131683095)
              ·
                rfl

theorem cell22_1624765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 9].length) (baseStart_1624765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624765 prefixEnd_1624765 := by exact prefixLift 1624765
  have htrace : WordTrace (prefixWord ++ tailWord_1624765) baseStart_1624765 baseEnd_1624765 := by
    simpa [prefixWord, tailWord_1624765, baseEnd_1624765] using wordTrace_append hprefix tailTrace_1624765
  have hstable : (prefixWord ++ tailWord_1624765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624765).length < 2 ^ (prefixWord ++ tailWord_1624765).sum := by decide
  have hdescent : baseEnd_1624765 < baseStart_1624765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624786 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_1624786 : Nat := 118140960795 + 1624786 * 2 ^ 59
def prefixEnd_1624786 : Nat := 4983230072969 + 3 ^ 40 * 1624786 * 2
def baseEnd_1624786 : Nat := 556197452464123500668501

theorem tailTrace_1624786 : CollatzResearch.WordTrace tailWord_1624786 prefixEnd_1624786 556197452464123500668501 := by
  unfold tailWord_1624786
  simp only [CollatzResearch.WordTrace]
  refine ⟨14815203472921322050423553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39507209261123525467796141 14815203472921322050423553)
  ·
    refine ⟨11111402604690991537817665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14815203472921322050423553 11111402604690991537817665)
    ·
      refine ⟨8333551953518243653363249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11111402604690991537817665 8333551953518243653363249)
      ·
        refine ⟨6250163965138682740022437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8333551953518243653363249 6250163965138682740022437)
        ·
          refine ⟨1171905743463503013754207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6250163965138682740022437 1171905743463503013754207)
          ·
            refine ⟨1757858615195254520631311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171905743463503013754207 1757858615195254520631311)
            ·
              refine ⟨2636787922792881780946967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1757858615195254520631311 2636787922792881780946967)
              ·
                refine ⟨3955181884189322671420451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636787922792881780946967 3955181884189322671420451)
                ·
                  refine ⟨5932772826283984007130677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955181884189322671420451 5932772826283984007130677)
                  ·
                    refine ⟨556197452464123500668501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5932772826283984007130677 556197452464123500668501)
                    ·
                      rfl

theorem cell22_1624786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_1624786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624786 prefixEnd_1624786 := by exact prefixLift 1624786
  have htrace : WordTrace (prefixWord ++ tailWord_1624786) baseStart_1624786 baseEnd_1624786 := by
    simpa [prefixWord, tailWord_1624786, baseEnd_1624786] using wordTrace_append hprefix tailTrace_1624786
  have hstable : (prefixWord ++ tailWord_1624786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624786).length < 2 ^ (prefixWord ++ tailWord_1624786).sum := by decide
  have hdescent : baseEnd_1624786 < baseStart_1624786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624825 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 4, 5]
def baseStart_1624825 : Nat := 118140960795 + 1624825 * 2 ^ 59
def prefixEnd_1624825 : Nat := 4983230072969 + 3 ^ 40 * 1624825 * 2
def baseEnd_1624825 : Nat := 556210802961140398943381

theorem tailTrace_1624825 : CollatzResearch.WordTrace tailWord_1624825 prefixEnd_1624825 556210802961140398943381 := by
  unfold tailWord_1624825
  simp only [CollatzResearch.WordTrace]
  refine ⟨59262236338543997862363929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39508157559029331908242619 59262236338543997862363929)
  ·
    refine ⟨44446677253907998396772947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59262236338543997862363929 44446677253907998396772947)
    ·
      refine ⟨66670015880861997595159421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44446677253907998396772947 66670015880861997595159421)
      ·
        refine ⟨25001255955323249098184783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66670015880861997595159421 25001255955323249098184783)
        ·
          refine ⟨37501883932984873647277175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25001255955323249098184783 37501883932984873647277175)
          ·
            refine ⟨56252825899477310470915763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37501883932984873647277175 56252825899477310470915763)
            ·
              refine ⟨84379238849215965706373645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56252825899477310470915763 84379238849215965706373645)
              ·
                refine ⟨31642214568455987139890117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84379238849215965706373645 31642214568455987139890117)
                ·
                  refine ⟨5932915231585497588729397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31642214568455987139890117 5932915231585497588729397)
                  ·
                    refine ⟨556210802961140398943381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5932915231585497588729397 556210802961140398943381)
                    ·
                      rfl

theorem cell22_1624825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_1624825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624825 prefixEnd_1624825 := by exact prefixLift 1624825
  have htrace : WordTrace (prefixWord ++ tailWord_1624825) baseStart_1624825 baseEnd_1624825 := by
    simpa [prefixWord, tailWord_1624825, baseEnd_1624825] using wordTrace_append hprefix tailTrace_1624825
  have hstable : (prefixWord ++ tailWord_1624825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624825).length < 2 ^ (prefixWord ++ tailWord_1624825).sum := by decide
  have hdescent : baseEnd_1624825 < baseStart_1624825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624857 : List Nat := [1, 2, 1, 2, 1, 1, 1, 8, 1, 4]
def baseStart_1624857 : Nat := 118140960795 + 1624857 * 2 ^ 59
def prefixEnd_1624857 : Nat := 4983230072969 + 3 ^ 40 * 1624857 * 2
def baseEnd_1624857 : Nat := 556221757215102982143283

theorem tailTrace_1624857 : CollatzResearch.WordTrace tailWord_1624857 prefixEnd_1624857 556221757215102982143283 := by
  unfold tailWord_1624857
  simp only [CollatzResearch.WordTrace]
  refine ⟨59263403474428067327528825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39508935649618711551685883 59263403474428067327528825)
  ·
    refine ⟨44447552605821050495646619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59263403474428067327528825 44447552605821050495646619)
    ·
      refine ⟨66671328908731575743469929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44447552605821050495646619 66671328908731575743469929)
      ·
        refine ⟨50003496681548681807602447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66671328908731575743469929 50003496681548681807602447)
        ·
          refine ⟨75005245022323022711403671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50003496681548681807602447 75005245022323022711403671)
          ·
            refine ⟨112507867533484534067105507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75005245022323022711403671 112507867533484534067105507)
            ·
              refine ⟨168761801300226801100658261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112507867533484534067105507 168761801300226801100658261)
              ·
                refine ⟨1977677358987032825398339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 168761801300226801100658261 1977677358987032825398339)
                ·
                  refine ⟨2966516038480549238097509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977677358987032825398339 2966516038480549238097509)
                  ·
                    refine ⟨556221757215102982143283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2966516038480549238097509 556221757215102982143283)
                    ·
                      rfl

theorem cell22_1624857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_1624857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624857 prefixEnd_1624857 := by exact prefixLift 1624857
  have htrace : WordTrace (prefixWord ++ tailWord_1624857) baseStart_1624857 baseEnd_1624857 := by
    simpa [prefixWord, tailWord_1624857, baseEnd_1624857] using wordTrace_append hprefix tailTrace_1624857
  have hstable : (prefixWord ++ tailWord_1624857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624857).length < 2 ^ (prefixWord ++ tailWord_1624857).sum := by decide
  have hdescent : baseEnd_1624857 < baseStart_1624857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624904 : List Nat := [2, 1, 3, 1, 1, 3, 1, 5, 2, 3]
def baseStart_1624904 : Nat := 118140960795 + 1624904 * 2 ^ 59
def prefixEnd_1624904 : Nat := 4983230072969 + 3 ^ 40 * 1624904 * 2
def baseEnd_1624904 : Nat := 556237846275610526218139

theorem tailTrace_1624904 : CollatzResearch.WordTrace tailWord_1624904 prefixEnd_1624904 556237846275610526218139 := by
  unfold tailWord_1624904
  simp only [CollatzResearch.WordTrace]
  refine ⟨29632558852628897177244883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39510078470171862902993177 29632558852628897177244883)
  ·
    refine ⟨44448838278943345765867325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29632558852628897177244883 44448838278943345765867325)
    ·
      refine ⟨16668314354603754662200247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44448838278943345765867325 16668314354603754662200247)
      ·
        refine ⟨25002471531905631993300371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16668314354603754662200247 25002471531905631993300371)
        ·
          refine ⟨37503707297858447989950557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25002471531905631993300371 37503707297858447989950557)
          ·
            refine ⟨14063890236696917996231459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37503707297858447989950557 14063890236696917996231459)
            ·
              refine ⟨21095835355045376994347189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14063890236696917996231459 21095835355045376994347189)
              ·
                refine ⟨1977734564535504093220049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21095835355045376994347189 1977734564535504093220049)
                ·
                  refine ⟨1483300923401628069915037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1977734564535504093220049 1483300923401628069915037)
                  ·
                    refine ⟨556237846275610526218139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1483300923401628069915037 556237846275610526218139)
                    ·
                      rfl

theorem cell22_1624904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_1624904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624904 prefixEnd_1624904 := by exact prefixLift 1624904
  have htrace : WordTrace (prefixWord ++ tailWord_1624904) baseStart_1624904 baseEnd_1624904 := by
    simpa [prefixWord, tailWord_1624904, baseEnd_1624904] using wordTrace_append hprefix tailTrace_1624904
  have hstable : (prefixWord ++ tailWord_1624904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624904).length < 2 ^ (prefixWord ++ tailWord_1624904).sum := by decide
  have hdescent : baseEnd_1624904 < baseStart_1624904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624919 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 2, 4]
def baseStart_1624919 : Nat := 118140960795 + 1624919 * 2 ^ 59
def prefixEnd_1624919 : Nat := 4983230072969 + 3 ^ 40 * 1624919 * 2
def baseEnd_1624919 : Nat := 556242981082155487093093

theorem tailTrace_1624919 : CollatzResearch.WordTrace tailWord_1624919 prefixEnd_1624919 556242981082155487093093 := by
  unfold tailWord_1624919
  simp only [CollatzResearch.WordTrace]
  refine ⟨59265664800203451916285811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39510443200135634610857207 59265664800203451916285811)
  ·
    refine ⟨88898497200305177874428717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59265664800203451916285811 88898497200305177874428717)
    ·
      refine ⟨33336936450114441702910769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88898497200305177874428717 33336936450114441702910769)
      ·
        refine ⟨25002702337585831277183077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33336936450114441702910769 25002702337585831277183077)
        ·
          refine ⟨4688006688297343364471827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25002702337585831277183077 4688006688297343364471827)
          ·
            refine ⟨7032010032446015046707741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4688006688297343364471827 7032010032446015046707741)
            ·
              refine ⟨2637003762167255642515403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7032010032446015046707741 2637003762167255642515403)
              ·
                refine ⟨3955505643250883463773105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637003762167255642515403 3955505643250883463773105)
                ·
                  refine ⟨2966629232438162597829829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3955505643250883463773105 2966629232438162597829829)
                  ·
                    refine ⟨556242981082155487093093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2966629232438162597829829 556242981082155487093093)
                    ·
                      rfl

theorem cell22_1624919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_1624919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1624919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1624919 prefixEnd_1624919 := by exact prefixLift 1624919
  have htrace : WordTrace (prefixWord ++ tailWord_1624919) baseStart_1624919 baseEnd_1624919 := by
    simpa [prefixWord, tailWord_1624919, baseEnd_1624919] using wordTrace_append hprefix tailTrace_1624919
  have hstable : (prefixWord ++ tailWord_1624919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624919).length < 2 ^ (prefixWord ++ tailWord_1624919).sum := by decide
  have hdescent : baseEnd_1624919 < baseStart_1624919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625007 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 6]
def baseStart_1625007 : Nat := 118140960795 + 1625007 * 2 ^ 59
def prefixEnd_1625007 : Nat := 4983230072969 + 3 ^ 40 * 1625007 * 2
def baseEnd_1625007 : Nat := 185424368426850863630941

theorem tailTrace_1625007 : CollatzResearch.WordTrace tailWord_1625007 prefixEnd_1625007 185424368426850863630941 := by
  unfold tailWord_1625007
  simp only [CollatzResearch.WordTrace]
  refine ⟨59268874423884642945489275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39512582949256428630326183 59268874423884642945489275)
  ·
    refine ⟨88903311635826964418233913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59268874423884642945489275 88903311635826964418233913)
    ·
      refine ⟨66677483726870223313675435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88903311635826964418233913 66677483726870223313675435)
      ·
        refine ⟨100016225590305334970513153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66677483726870223313675435 100016225590305334970513153)
        ·
          refine ⟨75012169192729001227884865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100016225590305334970513153 75012169192729001227884865)
          ·
            refine ⟨56259126894546750920913649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75012169192729001227884865 56259126894546750920913649)
            ·
              refine ⟨42194345170910063190685237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56259126894546750920913649 42194345170910063190685237)
              ·
                refine ⟨3955719859772818424126741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42194345170910063190685237 3955719859772818424126741)
                ·
                  refine ⟨185424368426850863630941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3955719859772818424126741 185424368426850863630941)
                  ·
                    rfl

theorem cell22_1625007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 6].length) (baseStart_1625007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625007 prefixEnd_1625007 := by exact prefixLift 1625007
  have htrace : WordTrace (prefixWord ++ tailWord_1625007) baseStart_1625007 baseEnd_1625007 := by
    simpa [prefixWord, tailWord_1625007, baseEnd_1625007] using wordTrace_append hprefix tailTrace_1625007
  have hstable : (prefixWord ++ tailWord_1625007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625007).length < 2 ^ (prefixWord ++ tailWord_1625007).sum := by decide
  have hdescent : baseEnd_1625007 < baseStart_1625007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625039 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 1, 5]
def baseStart_1625039 : Nat := 118140960795 + 1625039 * 2 ^ 59
def prefixEnd_1625039 : Nat := 4983230072969 + 3 ^ 40 * 1625039 * 2
def baseEnd_1625039 : Nat := 556284059534515174092725

theorem tailTrace_1625039 : CollatzResearch.WordTrace tailWord_1625039 prefixEnd_1625039 556284059534515174092725 := by
  unfold tailWord_1625039
  simp only [CollatzResearch.WordTrace]
  refine ⟨59270041559768712410654171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39513361039845808273769447 59270041559768712410654171)
  ·
    refine ⟨88905062339653068615981257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59270041559768712410654171 88905062339653068615981257)
    ·
      refine ⟨66678796754739801461985943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88905062339653068615981257 66678796754739801461985943)
      ·
        refine ⟨100018195132109702192978915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66678796754739801461985943 100018195132109702192978915)
        ·
          refine ⟨150027292698164553289468373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100018195132109702192978915 150027292698164553289468373)
          ·
            refine ⟨3516264672613231717721915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 150027292698164553289468373 3516264672613231717721915)
            ·
              refine ⟨5274397008919847576582873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3516264672613231717721915 5274397008919847576582873)
              ·
                refine ⟨3955797756689885682437155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5274397008919847576582873 3955797756689885682437155)
                ·
                  refine ⟨5933696635034828523655733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955797756689885682437155 5933696635034828523655733)
                  ·
                    refine ⟨556284059534515174092725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5933696635034828523655733 556284059534515174092725)
                    ·
                      rfl

theorem cell22_1625039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_1625039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625039 prefixEnd_1625039 := by exact prefixLift 1625039
  have htrace : WordTrace (prefixWord ++ tailWord_1625039) baseStart_1625039 baseEnd_1625039 := by
    simpa [prefixWord, tailWord_1625039, baseEnd_1625039] using wordTrace_append hprefix tailTrace_1625039
  have hstable : (prefixWord ++ tailWord_1625039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625039).length < 2 ^ (prefixWord ++ tailWord_1625039).sum := by decide
  have hdescent : baseEnd_1625039 < baseStart_1625039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625067 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 4, 7]
def baseStart_1625067 : Nat := 118140960795 + 1625067 * 2 ^ 59
def prefixEnd_1625067 : Nat := 4983230072969 + 3 ^ 40 * 1625067 * 2
def baseEnd_1625067 : Nat := 556293644506732434392639

theorem tailTrace_1625067 : CollatzResearch.WordTrace tailWord_1625067 prefixEnd_1625067 556293644506732434392639 := by
  unfold tailWord_1625067
  simp only [CollatzResearch.WordTrace]
  refine ⟨59271062803667273192673455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39514041869111515461782303 59271062803667273192673455)
  ·
    refine ⟨88906594205500909789010183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59271062803667273192673455 88906594205500909789010183)
    ·
      refine ⟨133359891308251364683515275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88906594205500909789010183 133359891308251364683515275)
      ·
        refine ⟨200039836962377047025272913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133359891308251364683515275 200039836962377047025272913)
        ·
          refine ⟨150029877721782785268954685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200039836962377047025272913 150029877721782785268954685)
          ·
            refine ⟨56261204145668544475858007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150029877721782785268954685 56261204145668544475858007)
            ·
              refine ⟨84391806218502816713787011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56261204145668544475858007 84391806218502816713787011)
              ·
                refine ⟨126587709327754225070680517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84391806218502816713787011 126587709327754225070680517)
                ·
                  refine ⟨23735195498953917200752597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126587709327754225070680517 23735195498953917200752597)
                  ·
                    refine ⟨556293644506732434392639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23735195498953917200752597 556293644506732434392639)
                    ·
                      rfl

theorem cell22_1625067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_1625067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625067 prefixEnd_1625067 := by exact prefixLift 1625067
  have htrace : WordTrace (prefixWord ++ tailWord_1625067) baseStart_1625067 baseEnd_1625067 := by
    simpa [prefixWord, tailWord_1625067, baseEnd_1625067] using wordTrace_append hprefix tailTrace_1625067
  have hstable : (prefixWord ++ tailWord_1625067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625067).length < 2 ^ (prefixWord ++ tailWord_1625067).sum := by decide
  have hdescent : baseEnd_1625067 < baseStart_1625067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625114 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 7]
def baseStart_1625114 : Nat := 118140960795 + 1625114 * 2 ^ 59
def prefixEnd_1625114 : Nat := 4983230072969 + 3 ^ 40 * 1625114 * 2
def baseEnd_1625114 : Nat := 185436577855746659489165

theorem tailTrace_1625114 : CollatzResearch.WordTrace tailWord_1625114 prefixEnd_1625114 185436577855746659489165 := by
  unfold tailWord_1625114
  simp only [CollatzResearch.WordTrace]
  refine ⟨14818194258624250054908599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39515184689664666813089597 14818194258624250054908599)
  ·
    refine ⟨22227291387936375082362899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14818194258624250054908599 22227291387936375082362899)
    ·
      refine ⟨33340937081904562623544349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22227291387936375082362899 33340937081904562623544349)
      ·
        refine ⟨12502851405714210983829131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33340937081904562623544349 12502851405714210983829131)
        ·
          refine ⟨18754277108571316475743697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12502851405714210983829131 18754277108571316475743697)
          ·
            refine ⟨14065707831428487356807773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18754277108571316475743697 14065707831428487356807773)
            ·
              refine ⟨5274640436785682758802915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14065707831428487356807773 5274640436785682758802915)
              ·
                refine ⟨7911960655178524138204373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5274640436785682758802915 7911960655178524138204373)
                ·
                  refine ⟨185436577855746659489165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7911960655178524138204373 185436577855746659489165)
                  ·
                    rfl

theorem cell22_1625114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_1625114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625114 prefixEnd_1625114 := by exact prefixLift 1625114
  have htrace : WordTrace (prefixWord ++ tailWord_1625114) baseStart_1625114 baseEnd_1625114 := by
    simpa [prefixWord, tailWord_1625114, baseEnd_1625114] using wordTrace_append hprefix tailTrace_1625114
  have hstable : (prefixWord ++ tailWord_1625114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625114).length < 2 ^ (prefixWord ++ tailWord_1625114).sum := by decide
  have hdescent : baseEnd_1625114 < baseStart_1625114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625131 : List Nat := [1, 1, 1, 1, 2, 1, 9, 1, 5]
def baseStart_1625131 : Nat := 118140960795 + 1625131 * 2 ^ 59
def prefixEnd_1625131 : Nat := 4983230072969 + 3 ^ 40 * 1625131 * 2
def baseEnd_1625131 : Nat := 185438517671552533597481

theorem tailTrace_1625131 : CollatzResearch.WordTrace tailWord_1625131 prefixEnd_1625131 185438517671552533597481 := by
  unfold tailWord_1625131
  simp only [CollatzResearch.WordTrace]
  refine ⟨59273397075435412123003247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39515598050290274748668831 59273397075435412123003247)
  ·
    refine ⟨88910095613153118184504871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59273397075435412123003247 88910095613153118184504871)
    ·
      refine ⟨133365143419729677276757307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88910095613153118184504871 133365143419729677276757307)
      ·
        refine ⟨200047715129594515915135961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133365143419729677276757307 200047715129594515915135961)
        ·
          refine ⟨150035786347195886936351971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200047715129594515915135961 150035786347195886936351971)
          ·
            refine ⟨225053679520793830404527957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150035786347195886936351971 225053679520793830404527957)
            ·
              refine ⟨1318673903442151350026531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 225053679520793830404527957 1318673903442151350026531)
              ·
                refine ⟨1978010855163227025039797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318673903442151350026531 1978010855163227025039797)
                ·
                  refine ⟨185438517671552533597481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1978010855163227025039797 185438517671552533597481)
                  ·
                    rfl

theorem cell22_1625131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 5].length) (baseStart_1625131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625131 prefixEnd_1625131 := by exact prefixLift 1625131
  have htrace : WordTrace (prefixWord ++ tailWord_1625131) baseStart_1625131 baseEnd_1625131 := by
    simpa [prefixWord, tailWord_1625131, baseEnd_1625131] using wordTrace_append hprefix tailTrace_1625131
  have hstable : (prefixWord ++ tailWord_1625131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625131).length < 2 ^ (prefixWord ++ tailWord_1625131).sum := by decide
  have hdescent : baseEnd_1625131 < baseStart_1625131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625182 : List Nat := [4, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1625182 : Nat := 118140960795 + 1625182 * 2 ^ 59
def prefixEnd_1625182 : Nat := 4983230072969 + 3 ^ 40 * 1625182 * 2
def baseEnd_1625182 : Nat := 185444337118970155922429

theorem tailTrace_1625182 : CollatzResearch.WordTrace tailWord_1625182 prefixEnd_1625182 185444337118970155922429 := by
  unfold tailWord_1625182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7409407149781330979138725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39516838132167098555406533 7409407149781330979138725)
  ·
    refine ⟨1389263840583999558588511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7409407149781330979138725 1389263840583999558588511)
    ·
      refine ⟨2083895760875999337882767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1389263840583999558588511 2083895760875999337882767)
      ·
        refine ⟨3125843641313999006824151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2083895760875999337882767 3125843641313999006824151)
        ·
          refine ⟨4688765461970998510236227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125843641313999006824151 4688765461970998510236227)
          ·
            refine ⟨7033148192956497765354341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4688765461970998510236227 7033148192956497765354341)
            ·
              refine ⟨1318715286179343331003939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7033148192956497765354341 1318715286179343331003939)
              ·
                refine ⟨1978072929269014996505909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318715286179343331003939 1978072929269014996505909)
                ·
                  refine ⟨185444337118970155922429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1978072929269014996505909 185444337118970155922429)
                  ·
                    rfl

theorem cell22_1625182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1625182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625182 prefixEnd_1625182 := by exact prefixLift 1625182
  have htrace : WordTrace (prefixWord ++ tailWord_1625182) baseStart_1625182 baseEnd_1625182 := by
    simpa [prefixWord, tailWord_1625182, baseEnd_1625182] using wordTrace_append hprefix tailTrace_1625182
  have hstable : (prefixWord ++ tailWord_1625182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625182).length < 2 ^ (prefixWord ++ tailWord_1625182).sum := by decide
  have hdescent : baseEnd_1625182 < baseStart_1625182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625221 : List Nat := [1, 3, 1, 1, 7, 9]
def baseStart_1625221 : Nat := 118140960795 + 1625221 * 2 ^ 59
def prefixEnd_1625221 : Nat := 4983230072969 + 3 ^ 40 * 1625221 * 2
def baseEnd_1625221 : Nat := 6868473603134905753607

theorem tailTrace_1625221 : CollatzResearch.WordTrace tailWord_1625221 prefixEnd_1625221 6868473603134905753607 := by
  unfold tailWord_1625221
  simp only [CollatzResearch.WordTrace]
  refine ⟨59276679645109357493779517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39517786430072904995853011 59276679645109357493779517)
  ·
    refine ⟨22228754866916009060167319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59276679645109357493779517 22228754866916009060167319)
    ·
      refine ⟨33343132300374013590250979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22228754866916009060167319 33343132300374013590250979)
      ·
        refine ⟨50014698450561020385376469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33343132300374013590250979 50014698450561020385376469)
        ·
          refine ⟨1172219494935023915282261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 50014698450561020385376469 1172219494935023915282261)
          ·
            refine ⟨6868473603134905753607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1172219494935023915282261 6868473603134905753607)
            ·
              rfl

theorem cell22_1625221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 9].length) (baseStart_1625221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625221 prefixEnd_1625221 := by exact prefixLift 1625221
  have htrace : WordTrace (prefixWord ++ tailWord_1625221) baseStart_1625221 baseEnd_1625221 := by
    simpa [prefixWord, tailWord_1625221, baseEnd_1625221] using wordTrace_append hprefix tailTrace_1625221
  have hstable : (prefixWord ++ tailWord_1625221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625221).length < 2 ^ (prefixWord ++ tailWord_1625221).sum := by decide
  have hdescent : baseEnd_1625221 < baseStart_1625221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625253 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 3, 3]
def baseStart_1625253 : Nat := 118140960795 + 1625253 * 2 ^ 59
def prefixEnd_1625253 : Nat := 4983230072969 + 3 ^ 40 * 1625253 * 2
def baseEnd_1625253 : Nat := 556357316107889949242069

theorem tailTrace_1625253 : CollatzResearch.WordTrace tailWord_1625253 prefixEnd_1625253 556357316107889949242069 := by
  unfold tailWord_1625253
  simp only [CollatzResearch.WordTrace]
  refine ⟨59277846780993426958944413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39518564520662284639296275 59277846780993426958944413)
  ·
    refine ⟨22229192542872535109604155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59277846780993426958944413 22229192542872535109604155)
    ·
      refine ⟨33343788814308802664406233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22229192542872535109604155 33343788814308802664406233)
      ·
        refine ⟨25007841610731601998304675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33343788814308802664406233 25007841610731601998304675)
        ·
          refine ⟨37511762416097402997457013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25007841610731601998304675 37511762416097402997457013)
          ·
            refine ⟨3516727726509131531011595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37511762416097402997457013 3516727726509131531011595)
            ·
              refine ⟨5275091589763697296517393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3516727726509131531011595 5275091589763697296517393)
              ·
                refine ⟨3956318692322772972388045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5275091589763697296517393 3956318692322772972388045)
                ·
                  refine ⟨1483619509621039864645517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3956318692322772972388045 1483619509621039864645517)
                  ·
                    refine ⟨556357316107889949242069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1483619509621039864645517 556357316107889949242069)
                    ·
                      rfl

theorem cell22_1625253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_1625253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625253 prefixEnd_1625253 := by exact prefixLift 1625253
  have htrace : WordTrace (prefixWord ++ tailWord_1625253) baseStart_1625253 baseEnd_1625253 := by
    simpa [prefixWord, tailWord_1625253, baseEnd_1625253] using wordTrace_append hprefix tailTrace_1625253
  have hstable : (prefixWord ++ tailWord_1625253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625253).length < 2 ^ (prefixWord ++ tailWord_1625253).sum := by decide
  have hdescent : baseEnd_1625253 < baseStart_1625253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625311 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 6]
def baseStart_1625311 : Nat := 118140960795 + 1625311 * 2 ^ 59
def prefixEnd_1625311 : Nat := 4983230072969 + 3 ^ 40 * 1625311 * 2
def baseEnd_1625311 : Nat := 185459056897732377097297

theorem tailTrace_1625311 : CollatzResearch.WordTrace tailWord_1625311 prefixEnd_1625311 185459056897732377097297 := by
  unfold tailWord_1625311
  simp only [CollatzResearch.WordTrace]
  refine ⟨59279962214783302864555787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39519974809855535243037191 59279962214783302864555787)
  ·
    refine ⟨88919943322174954296833681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59279962214783302864555787 88919943322174954296833681)
    ·
      refine ⟨66689957491631215722625261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88919943322174954296833681 66689957491631215722625261)
      ·
        refine ⟨25008734059361705895984473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66689957491631215722625261 25008734059361705895984473)
        ·
          refine ⟨18756550544521279421988355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25008734059361705895984473 18756550544521279421988355)
          ·
            refine ⟨28134825816781919132982533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18756550544521279421988355 28134825816781919132982533)
            ·
              refine ⟨5275279840646609837434225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28134825816781919132982533 5275279840646609837434225)
              ·
                refine ⟨3956459880484957378075669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5275279840646609837434225 3956459880484957378075669)
                ·
                  refine ⟨185459056897732377097297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3956459880484957378075669 185459056897732377097297)
                  ·
                    rfl

theorem cell22_1625311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 6].length) (baseStart_1625311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625311 prefixEnd_1625311 := by exact prefixLift 1625311
  have htrace : WordTrace (prefixWord ++ tailWord_1625311) baseStart_1625311 baseEnd_1625311 := by
    simpa [prefixWord, tailWord_1625311, baseEnd_1625311] using wordTrace_append hprefix tailTrace_1625311
  have hstable : (prefixWord ++ tailWord_1625311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625311).length < 2 ^ (prefixWord ++ tailWord_1625311).sum := by decide
  have hdescent : baseEnd_1625311 < baseStart_1625311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625313 : List Nat := [1, 2, 3, 1, 3, 2, 1, 4, 1, 4]
def baseStart_1625313 : Nat := 118140960795 + 1625313 * 2 ^ 59
def prefixEnd_1625313 : Nat := 4983230072969 + 3 ^ 40 * 1625313 * 2
def baseEnd_1625313 : Nat := 556377855334069792741885

theorem tailTrace_1625313 : CollatzResearch.WordTrace tailWord_1625313 prefixEnd_1625313 556377855334069792741885 := by
  unfold tailWord_1625313
  simp only [CollatzResearch.WordTrace]
  refine ⟨59280035160776057206128593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39520023440517371470752395 59280035160776057206128593)
  ·
    refine ⟨44460026370582042904596445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59280035160776057206128593 44460026370582042904596445)
    ·
      refine ⟨16672509888968266089223667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44460026370582042904596445 16672509888968266089223667)
      ·
        refine ⟨25008764833452399133835501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16672509888968266089223667 25008764833452399133835501)
        ·
          refine ⟨9378286812544649675188313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25008764833452399133835501 9378286812544649675188313)
          ·
            refine ⟨7033715109408487256391235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9378286812544649675188313 7033715109408487256391235)
            ·
              refine ⟨10550572664112730884586853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7033715109408487256391235 10550572664112730884586853)
              ·
                refine ⟨1978232374521137040860035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10550572664112730884586853 1978232374521137040860035)
                ·
                  refine ⟨2967348561781705561290053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978232374521137040860035 2967348561781705561290053)
                  ·
                    refine ⟨556377855334069792741885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2967348561781705561290053 556377855334069792741885)
                    ·
                      rfl

theorem cell22_1625313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_1625313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625313 prefixEnd_1625313 := by exact prefixLift 1625313
  have htrace : WordTrace (prefixWord ++ tailWord_1625313) baseStart_1625313 baseEnd_1625313 := by
    simpa [prefixWord, tailWord_1625313, baseEnd_1625313] using wordTrace_append hprefix tailTrace_1625313
  have hstable : (prefixWord ++ tailWord_1625313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625313).length < 2 ^ (prefixWord ++ tailWord_1625313).sum := by decide
  have hdescent : baseEnd_1625313 < baseStart_1625313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625343 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 4, 3]
def baseStart_1625343 : Nat := 118140960795 + 1625343 * 2 ^ 59
def prefixEnd_1625343 : Nat := 4983230072969 + 3 ^ 40 * 1625343 * 2
def baseEnd_1625343 : Nat := 556388124947159714491793

theorem tailTrace_1625343 : CollatzResearch.WordTrace tailWord_1625343 prefixEnd_1625343 556388124947159714491793 := by
  unfold tailWord_1625343
  simp only [CollatzResearch.WordTrace]
  refine ⟨59281129350667372329720683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39520752900444914886480455 59281129350667372329720683)
  ·
    refine ⟨88921694026001058494581025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59281129350667372329720683 88921694026001058494581025)
    ·
      refine ⟨66691270519500793870935769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88921694026001058494581025 66691270519500793870935769)
      ·
        refine ⟨50018452889625595403201827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66691270519500793870935769 50018452889625595403201827)
        ·
          refine ⟨75027679334438393104802741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50018452889625595403201827 75027679334438393104802741)
          ·
            refine ⟨7033844937603599353575257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75027679334438393104802741 7033844937603599353575257)
            ·
              refine ⟨5275383703202699515181443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7033844937603599353575257 5275383703202699515181443)
              ·
                refine ⟨7913075554804049272772165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5275383703202699515181443 7913075554804049272772165)
                ·
                  refine ⟨1483701666525759238644781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7913075554804049272772165 1483701666525759238644781)
                  ·
                    refine ⟨556388124947159714491793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1483701666525759238644781 556388124947159714491793)
                    ·
                      rfl

theorem cell22_1625343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 3].length) (baseStart_1625343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625343 prefixEnd_1625343 := by exact prefixLift 1625343
  have htrace : WordTrace (prefixWord ++ tailWord_1625343) baseStart_1625343 baseEnd_1625343 := by
    simpa [prefixWord, tailWord_1625343, baseEnd_1625343] using wordTrace_append hprefix tailTrace_1625343
  have hstable : (prefixWord ++ tailWord_1625343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625343).length < 2 ^ (prefixWord ++ tailWord_1625343).sum := by decide
  have hdescent : baseEnd_1625343 < baseStart_1625343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625356 : List Nat := [2, 2, 1, 2, 2, 3, 1, 9]
def baseStart_1625356 : Nat := 118140960795 + 1625356 * 2 ^ 59
def prefixEnd_1625356 : Nat := 4983230072969 + 3 ^ 40 * 1625356 * 2
def baseEnd_1625356 : Nat := 61821397234759112657417

theorem tailTrace_1625356 : CollatzResearch.WordTrace tailWord_1625356 prefixEnd_1625356 61821397234759112657417 := by
  unfold tailWord_1625356
  simp only [CollatzResearch.WordTrace]
  refine ⟨29640801749810137774971961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39521068999746850366629281 29640801749810137774971961)
  ·
    refine ⟨22230601312357603331228971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29640801749810137774971961 22230601312357603331228971)
    ·
      refine ⟨33345901968536404996843457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22230601312357603331228971 33345901968536404996843457)
      ·
        refine ⟨25009426476402303747632593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33345901968536404996843457 25009426476402303747632593)
        ·
          refine ⟨18757069857301727810724445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25009426476402303747632593 18757069857301727810724445)
          ·
            refine ⟨7033901196488147929021667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18757069857301727810724445 7033901196488147929021667)
            ·
              refine ⟨10550851794732221893532501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7033901196488147929021667 10550851794732221893532501)
              ·
                refine ⟨61821397234759112657417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10550851794732221893532501 61821397234759112657417)
                ·
                  rfl

theorem cell22_1625356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 9].length) (baseStart_1625356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625356 prefixEnd_1625356 := by exact prefixLift 1625356
  have htrace : WordTrace (prefixWord ++ tailWord_1625356) baseStart_1625356 baseEnd_1625356 := by
    simpa [prefixWord, tailWord_1625356, baseEnd_1625356] using wordTrace_append hprefix tailTrace_1625356
  have hstable : (prefixWord ++ tailWord_1625356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625356).length < 2 ^ (prefixWord ++ tailWord_1625356).sum := by decide
  have hdescent : baseEnd_1625356 < baseStart_1625356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625373 : List Nat := [1, 4, 2, 3, 1, 1, 2, 8]
def baseStart_1625373 : Nat := 118140960795 + 1625373 * 2 ^ 59
def prefixEnd_1625373 : Nat := 4983230072969 + 3 ^ 40 * 1625373 * 2
def baseEnd_1625373 : Nat := 61822043840027737360189

theorem tailTrace_1625373 : CollatzResearch.WordTrace tailWord_1625373 prefixEnd_1625373 61822043840027737360189 := by
  unfold tailWord_1625373
  simp only [CollatzResearch.WordTrace]
  refine ⟨59282223540558687453312773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39521482360372458302208515 59282223540558687453312773)
  ·
    refine ⟨11115416913854753897496145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59282223540558687453312773 11115416913854753897496145)
    ·
      refine ⟨8336562685391065423122109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11115416913854753897496145 8336562685391065423122109)
      ·
        refine ⟨3126211007021649533670791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8336562685391065423122109 3126211007021649533670791)
        ·
          refine ⟨4689316510532474300506187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126211007021649533670791 4689316510532474300506187)
          ·
            refine ⟨7033974765798711450759281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689316510532474300506187 7033974765798711450759281)
            ·
              refine ⟨5275481074349033588069461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7033974765798711450759281 5275481074349033588069461)
              ·
                refine ⟨61822043840027737360189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5275481074349033588069461 61822043840027737360189)
                ·
                  rfl

theorem cell22_1625373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 8].length) (baseStart_1625373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625373 prefixEnd_1625373 := by exact prefixLift 1625373
  have htrace : WordTrace (prefixWord ++ tailWord_1625373) baseStart_1625373 baseEnd_1625373 := by
    simpa [prefixWord, tailWord_1625373, baseEnd_1625373] using wordTrace_append hprefix tailTrace_1625373
  have hstable : (prefixWord ++ tailWord_1625373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625373).length < 2 ^ (prefixWord ++ tailWord_1625373).sum := by decide
  have hdescent : baseEnd_1625373 < baseStart_1625373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625375 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 2, 4]
def baseStart_1625375 : Nat := 118140960795 + 1625375 * 2 ^ 59
def prefixEnd_1625375 : Nat := 4983230072969 + 3 ^ 40 * 1625375 * 2
def baseEnd_1625375 : Nat := 556399079201122297691695

theorem tailTrace_1625375 : CollatzResearch.WordTrace tailWord_1625375 prefixEnd_1625375 556399079201122297691695 := by
  unfold tailWord_1625375
  simp only [CollatzResearch.WordTrace]
  refine ⟨59282296486551441794885579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39521530991034294529923719 59282296486551441794885579)
  ·
    refine ⟨88923444729827162692328369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59282296486551441794885579 88923444729827162692328369)
    ·
      refine ⟨66692583547370372019246277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88923444729827162692328369 66692583547370372019246277)
      ·
        refine ⟨12504859415131944753608677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66692583547370372019246277 12504859415131944753608677)
        ·
          refine ⟨2344661140337239641301627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12504859415131944753608677 2344661140337239641301627)
          ·
            refine ⟨3516991710505859461952441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2344661140337239641301627 3516991710505859461952441)
            ·
              refine ⟨2637743782879394596464331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3516991710505859461952441 2637743782879394596464331)
              ·
                refine ⟨3956615674319091894696497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637743782879394596464331 3956615674319091894696497)
                ·
                  refine ⟨2967461755739318921022373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3956615674319091894696497 2967461755739318921022373)
                  ·
                    refine ⟨556399079201122297691695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2967461755739318921022373 556399079201122297691695)
                    ·
                      rfl

theorem cell22_1625375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_1625375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625375 prefixEnd_1625375 := by exact prefixLift 1625375
  have htrace : WordTrace (prefixWord ++ tailWord_1625375) baseStart_1625375 baseEnd_1625375 := by
    simpa [prefixWord, tailWord_1625375, baseEnd_1625375] using wordTrace_append hprefix tailTrace_1625375
  have hstable : (prefixWord ++ tailWord_1625375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625375).length < 2 ^ (prefixWord ++ tailWord_1625375).sum := by decide
  have hdescent : baseEnd_1625375 < baseStart_1625375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625463 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 6]
def baseStart_1625463 : Nat := 118140960795 + 1625463 * 2 ^ 59
def prefixEnd_1625463 : Nat := 4983230072969 + 3 ^ 40 * 1625463 * 2
def baseEnd_1625463 : Nat := 185476401133173133830475

theorem tailTrace_1625463 : CollatzResearch.WordTrace tailWord_1625463 prefixEnd_1625463 185476401133173133830475 := by
  unfold tailWord_1625463
  simp only [CollatzResearch.WordTrace]
  refine ⟨59285506110232632824089043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39523670740155088549392695 59285506110232632824089043)
  ·
    refine ⟨88928259165348949236133565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59285506110232632824089043 88928259165348949236133565)
    ·
      refine ⟨33348097187005855963550087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88928259165348949236133565 33348097187005855963550087)
      ·
        refine ⟨50022145780508783945325131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33348097187005855963550087 50022145780508783945325131)
        ·
          refine ⟨75033218670763175917987697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50022145780508783945325131 75033218670763175917987697)
          ·
            refine ⟨56274914003072381938490773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75033218670763175917987697 56274914003072381938490773)
            ·
              refine ⟨2637886593894017903366755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56274914003072381938490773 2637886593894017903366755)
              ·
                refine ⟨3956829890841026855050133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637886593894017903366755 3956829890841026855050133)
                ·
                  refine ⟨185476401133173133830475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3956829890841026855050133 185476401133173133830475)
                  ·
                    rfl

theorem cell22_1625463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 6].length) (baseStart_1625463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625463 prefixEnd_1625463 := by exact prefixLift 1625463
  have htrace : WordTrace (prefixWord ++ tailWord_1625463) baseStart_1625463 baseEnd_1625463 := by
    simpa [prefixWord, tailWord_1625463, baseEnd_1625463] using wordTrace_append hprefix tailTrace_1625463
  have hstable : (prefixWord ++ tailWord_1625463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625463).length < 2 ^ (prefixWord ++ tailWord_1625463).sum := by decide
  have hdescent : baseEnd_1625463 < baseStart_1625463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625493 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_1625493 : Nat := 118140960795 + 1625493 * 2 ^ 59
def prefixEnd_1625493 : Nat := 4983230072969 + 3 ^ 40 * 1625493 * 2
def baseEnd_1625493 : Nat := 556439473012609323241333

theorem tailTrace_1625493 : CollatzResearch.WordTrace tailWord_1625493 prefixEnd_1625493 556439473012609323241333 := by
  unfold tailWord_1625493
  simp only [CollatzResearch.WordTrace]
  refine ⟨59286600300123947947681133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39524400200082631965120755 59286600300123947947681133)
  ·
    refine ⟨22232475112546480480380425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59286600300123947947681133 22232475112546480480380425)
    ·
      refine ⟨16674356334409860360285319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22232475112546480480380425 16674356334409860360285319)
      ·
        refine ⟨25011534501614790540427979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16674356334409860360285319 25011534501614790540427979)
        ·
          refine ⟨37517301752422185810641969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25011534501614790540427979 37517301752422185810641969)
          ·
            refine ⟨28137976314316639357981477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37517301752422185810641969 28137976314316639357981477)
            ·
              refine ⟨5275870558934369879621527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28137976314316639357981477 5275870558934369879621527)
              ·
                refine ⟨7913805838401554819432291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5275870558934369879621527 7913805838401554819432291)
                ·
                  refine ⟨11870708757602332229148437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7913805838401554819432291 11870708757602332229148437)
                  ·
                    refine ⟨556439473012609323241333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11870708757602332229148437 556439473012609323241333)
                    ·
                      rfl

theorem cell22_1625493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_1625493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625493 prefixEnd_1625493 := by exact prefixLift 1625493
  have htrace : WordTrace (prefixWord ++ tailWord_1625493) baseStart_1625493 baseEnd_1625493 := by
    simpa [prefixWord, tailWord_1625493, baseEnd_1625493] using wordTrace_append hprefix tailTrace_1625493
  have hstable : (prefixWord ++ tailWord_1625493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625493).length < 2 ^ (prefixWord ++ tailWord_1625493).sum := by decide
  have hdescent : baseEnd_1625493 < baseStart_1625493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625497 : List Nat := [1, 2, 1, 2, 1, 7, 1, 3, 4]
def baseStart_1625497 : Nat := 118140960795 + 1625497 * 2 ^ 59
def prefixEnd_1625497 : Nat := 4983230072969 + 3 ^ 40 * 1625497 * 2
def baseEnd_1625497 : Nat := 185480280764784882047107

theorem tailTrace_1625497 : CollatzResearch.WordTrace tailWord_1625497 prefixEnd_1625497 185480280764784882047107 := by
  unfold tailWord_1625497
  simp only [CollatzResearch.WordTrace]
  refine ⟨59286746192109456630826745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39524497461406304420551163 59286746192109456630826745)
  ·
    refine ⟨44465059644082092473120059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59286746192109456630826745 44465059644082092473120059)
    ·
      refine ⟨66697589466123138709680089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44465059644082092473120059 66697589466123138709680089)
      ·
        refine ⟨50023192099592354032260067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66697589466123138709680089 50023192099592354032260067)
        ·
          refine ⟨75034788149388531048390101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50023192099592354032260067 75034788149388531048390101)
          ·
            refine ⟨1758627847251293696446643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 75034788149388531048390101 1758627847251293696446643)
            ·
              refine ⟨2637941770876940544669965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1758627847251293696446643 2637941770876940544669965)
              ·
                refine ⟨989228164078852704251237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2637941770876940544669965 989228164078852704251237)
                ·
                  refine ⟨185480280764784882047107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 989228164078852704251237 185480280764784882047107)
                  ·
                    rfl

theorem cell22_1625497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 4].length) (baseStart_1625497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625497 prefixEnd_1625497 := by exact prefixLift 1625497
  have htrace : WordTrace (prefixWord ++ tailWord_1625497) baseStart_1625497 baseEnd_1625497 := by
    simpa [prefixWord, tailWord_1625497, baseEnd_1625497] using wordTrace_append hprefix tailTrace_1625497
  have hstable : (prefixWord ++ tailWord_1625497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625497).length < 2 ^ (prefixWord ++ tailWord_1625497).sum := by decide
  have hdescent : baseEnd_1625497 < baseStart_1625497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625525 : List Nat := [1, 3, 3, 2, 2, 2, 2, 7]
def baseStart_1625525 : Nat := 118140960795 + 1625525 * 2 ^ 59
def prefixEnd_1625525 : Nat := 4983230072969 + 3 ^ 40 * 1625525 * 2
def baseEnd_1625525 : Nat := 61827825251841322937915

theorem tailTrace_1625525 : CollatzResearch.WordTrace tailWord_1625525 prefixEnd_1625525 61827825251841322937915 := by
  unfold tailWord_1625525
  simp only [CollatzResearch.WordTrace]
  refine ⟨59287767436008017412846029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39525178290672011608564019 59287767436008017412846029)
  ·
    refine ⟨22232912788503006529817261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59287767436008017412846029 22232912788503006529817261)
    ·
      refine ⟨8337342295688627448681473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22232912788503006529817261 8337342295688627448681473)
      ·
        refine ⟨6253006721766470586511105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8337342295688627448681473 6253006721766470586511105)
        ·
          refine ⟨4689755041324852939883329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6253006721766470586511105 4689755041324852939883329)
          ·
            refine ⟨3517316280993639704912497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4689755041324852939883329 3517316280993639704912497)
            ·
              refine ⟨2637987210745229778684373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3517316280993639704912497 2637987210745229778684373)
              ·
                refine ⟨61827825251841322937915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2637987210745229778684373 61827825251841322937915)
                ·
                  rfl

theorem cell22_1625525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 7].length) (baseStart_1625525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625525 prefixEnd_1625525 := by exact prefixLift 1625525
  have htrace : WordTrace (prefixWord ++ tailWord_1625525) baseStart_1625525 baseEnd_1625525 := by
    simpa [prefixWord, tailWord_1625525, baseEnd_1625525] using wordTrace_append hprefix tailTrace_1625525
  have hstable : (prefixWord ++ tailWord_1625525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625525).length < 2 ^ (prefixWord ++ tailWord_1625525).sum := by decide
  have hdescent : baseEnd_1625525 < baseStart_1625525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625585 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 2, 5]
def baseStart_1625585 : Nat := 118140960795 + 1625585 * 2 ^ 59
def prefixEnd_1625585 : Nat := 4983230072969 + 3 ^ 40 * 1625585 * 2
def baseEnd_1625585 : Nat := 556470966492751749941051

theorem tailTrace_1625585 : CollatzResearch.WordTrace tailWord_1625585 prefixEnd_1625585 556470966492751749941051 := by
  unfold tailWord_1625585
  simp only [CollatzResearch.WordTrace]
  refine ⟨59289955815790647660030209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39526637210527098440020139 59289955815790647660030209)
  ·
    refine ⟨44467466861842985745022657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59289955815790647660030209 44467466861842985745022657)
    ·
      refine ⟨33350600146382239308766993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44467466861842985745022657 33350600146382239308766993)
      ·
        refine ⟨25012950109786679481575245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33350600146382239308766993 25012950109786679481575245)
        ·
          refine ⟨9379856291170004805590717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25012950109786679481575245 9379856291170004805590717)
          ·
            refine ⟨3517446109188751802096519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9379856291170004805590717 3517446109188751802096519)
            ·
              refine ⟨5276169163783127703144779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517446109188751802096519 5276169163783127703144779)
              ·
                refine ⟨7914253745674691554717169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5276169163783127703144779 7914253745674691554717169)
                ·
                  refine ⟨5935690309256018666037877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7914253745674691554717169 5935690309256018666037877)
                  ·
                    refine ⟨556470966492751749941051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5935690309256018666037877 556470966492751749941051)
                    ·
                      rfl

theorem cell22_1625585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_1625585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625585 prefixEnd_1625585 := by exact prefixLift 1625585
  have htrace : WordTrace (prefixWord ++ tailWord_1625585) baseStart_1625585 baseEnd_1625585 := by
    simpa [prefixWord, tailWord_1625585, baseEnd_1625585] using wordTrace_append hprefix tailTrace_1625585
  have hstable : (prefixWord ++ tailWord_1625585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625585).length < 2 ^ (prefixWord ++ tailWord_1625585).sum := by decide
  have hdescent : baseEnd_1625585 < baseStart_1625585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625632 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 6]
def baseStart_1625632 : Nat := 118140960795 + 1625632 * 2 ^ 59
def prefixEnd_1625632 : Nat := 4983230072969 + 3 ^ 40 * 1625632 * 2
def baseEnd_1625632 : Nat := 185495685184419764671969

theorem tailTrace_1625632 : CollatzResearch.WordTrace tailWord_1625632 prefixEnd_1625632 185495685184419764671969 := by
  unfold tailWord_1625632
  simp only [CollatzResearch.WordTrace]
  refine ⟨29645835023310187343495575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39527780031080249791327433 29645835023310187343495575)
  ·
    refine ⟨44468752534965281015243363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29645835023310187343495575 44468752534965281015243363)
    ·
      refine ⟨66703128802447921522865045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44468752534965281015243363 66703128802447921522865045)
      ·
        refine ⟨3126709162614746321384299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66703128802447921522865045 3126709162614746321384299)
        ·
          refine ⟨4690063743922119482076449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126709162614746321384299 4690063743922119482076449)
          ·
            refine ⟨3517547807941589611557337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4690063743922119482076449 3517547807941589611557337)
            ·
              refine ⟨2638160855956192208668003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3517547807941589611557337 2638160855956192208668003)
              ·
                refine ⟨3957241283934288313002005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2638160855956192208668003 3957241283934288313002005)
                ·
                  refine ⟨185495685184419764671969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3957241283934288313002005 185495685184419764671969)
                  ·
                    rfl

theorem cell22_1625632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 6].length) (baseStart_1625632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625632 prefixEnd_1625632 := by exact prefixLift 1625632
  have htrace : WordTrace (prefixWord ++ tailWord_1625632) baseStart_1625632 baseEnd_1625632 := by
    simpa [prefixWord, tailWord_1625632, baseEnd_1625632] using wordTrace_append hprefix tailTrace_1625632
  have hstable : (prefixWord ++ tailWord_1625632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625632).length < 2 ^ (prefixWord ++ tailWord_1625632).sum := by decide
  have hdescent : baseEnd_1625632 < baseStart_1625632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625752 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 3, 4]
def baseStart_1625752 : Nat := 118140960795 + 1625752 * 2 ^ 59
def prefixEnd_1625752 : Nat := 4983230072969 + 3 ^ 40 * 1625752 * 2
def baseEnd_1625752 : Nat := 556528134005618981015539

theorem tailTrace_1625752 : CollatzResearch.WordTrace tailWord_1625752 prefixEnd_1625752 556528134005618981015539 := by
  unfold tailWord_1625752
  simp only [CollatzResearch.WordTrace]
  refine ⟨29648023403092817590679755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39530697870790423454239673 29648023403092817590679755)
  ·
    refine ⟨44472035104639226386019633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29648023403092817590679755 44472035104639226386019633)
    ·
      refine ⟨33354026328479419789514725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44472035104639226386019633 33354026328479419789514725)
      ·
        refine ⟨6253879936589891210534011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33354026328479419789514725 6253879936589891210534011)
        ·
          refine ⟨9380819904884836815801017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6253879936589891210534011 9380819904884836815801017)
          ·
            refine ⟨7035614928663627611850763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9380819904884836815801017 7035614928663627611850763)
            ·
              refine ⟨10553422392995441417776145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7035614928663627611850763 10553422392995441417776145)
              ·
                refine ⟨7915066794746581063332109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10553422392995441417776145 7915066794746581063332109)
                ·
                  refine ⟨2968150048029967898749541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7915066794746581063332109 2968150048029967898749541)
                  ·
                    refine ⟨556528134005618981015539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2968150048029967898749541 556528134005618981015539)
                    ·
                      rfl

theorem cell22_1625752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_1625752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625752 prefixEnd_1625752 := by exact prefixLift 1625752
  have htrace : WordTrace (prefixWord ++ tailWord_1625752) baseStart_1625752 baseEnd_1625752 := by
    simpa [prefixWord, tailWord_1625752, baseEnd_1625752] using wordTrace_append hprefix tailTrace_1625752
  have hstable : (prefixWord ++ tailWord_1625752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625752).length < 2 ^ (prefixWord ++ tailWord_1625752).sum := by decide
  have hdescent : baseEnd_1625752 < baseStart_1625752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625786 : List Nat := [3, 1, 1, 1, 2, 6, 2, 1, 1, 4]
def baseStart_1625786 : Nat := 118140960795 + 1625786 * 2 ^ 59
def prefixEnd_1625786 : Nat := 4983230072969 + 3 ^ 40 * 1625786 * 2
def baseEnd_1625786 : Nat := 556539772900454225665435

theorem tailTrace_1625786 : CollatzResearch.WordTrace tailWord_1625786 prefixEnd_1625786 556539772900454225665435 := by
  unfold tailWord_1625786
  simp only [CollatzResearch.WordTrace]
  refine ⟨14824321722015614747024303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39531524592041639325398141 14824321722015614747024303)
  ·
    refine ⟨22236482583023422120536455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14824321722015614747024303 22236482583023422120536455)
    ·
      refine ⟨33354723874535133180804683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22236482583023422120536455 33354723874535133180804683)
      ·
        refine ⟨50032085811802699771207025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33354723874535133180804683 50032085811802699771207025)
        ·
          refine ⟨37524064358852024828405269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50032085811802699771207025 37524064358852024828405269)
          ·
            refine ⟨1758940516821188663831497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37524064358852024828405269 1758940516821188663831497)
            ·
              refine ⟨1319205387615891497873623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1758940516821188663831497 1319205387615891497873623)
              ·
                refine ⟨1978808081423837246810435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319205387615891497873623 1978808081423837246810435)
                ·
                  refine ⟨2968212122135755870215653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978808081423837246810435 2968212122135755870215653)
                  ·
                    refine ⟨556539772900454225665435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2968212122135755870215653 556539772900454225665435)
                    ·
                      rfl

theorem cell22_1625786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_1625786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625786 prefixEnd_1625786 := by exact prefixLift 1625786
  have htrace : WordTrace (prefixWord ++ tailWord_1625786) baseStart_1625786 baseEnd_1625786 := by
    simpa [prefixWord, tailWord_1625786, baseEnd_1625786] using wordTrace_append hprefix tailTrace_1625786
  have hstable : (prefixWord ++ tailWord_1625786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625786).length < 2 ^ (prefixWord ++ tailWord_1625786).sum := by decide
  have hdescent : baseEnd_1625786 < baseStart_1625786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625816 : List Nat := [2, 1, 2, 2, 3, 1, 5, 1, 2, 3]
def baseStart_1625816 : Nat := 118140960795 + 1625816 * 2 ^ 59
def prefixEnd_1625816 : Nat := 4983230072969 + 3 ^ 40 * 1625816 * 2
def baseEnd_1625816 : Nat := 556550042513544147415343

theorem tailTrace_1625816 : CollatzResearch.WordTrace tailWord_1625816 prefixEnd_1625816 556550042513544147415343 := by
  unfold tailWord_1625816
  simp only [CollatzResearch.WordTrace]
  refine ⟨29649190538976887055844651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39532254051969182741126201 29649190538976887055844651)
  ·
    refine ⟨44473785808465330583766977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29649190538976887055844651 44473785808465330583766977)
    ·
      refine ⟨33355339356348997937825233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44473785808465330583766977 33355339356348997937825233)
      ·
        refine ⟨25016504517261748453368925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33355339356348997937825233 25016504517261748453368925)
        ·
          refine ⟨9381189193973155670013347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25016504517261748453368925 9381189193973155670013347)
          ·
            refine ⟨14071783790959733505020021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9381189193973155670013347 14071783790959733505020021)
            ·
              refine ⟨1319229730402475016095627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14071783790959733505020021 1319229730402475016095627)
              ·
                refine ⟨1978844595603712524143441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319229730402475016095627 1978844595603712524143441)
                ·
                  refine ⟨1484133446702784393107581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1978844595603712524143441 1484133446702784393107581)
                  ·
                    refine ⟨556550042513544147415343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1484133446702784393107581 556550042513544147415343)
                    ·
                      rfl

theorem cell22_1625816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_1625816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625816 prefixEnd_1625816 := by exact prefixLift 1625816
  have htrace : WordTrace (prefixWord ++ tailWord_1625816) baseStart_1625816 baseEnd_1625816 := by
    simpa [prefixWord, tailWord_1625816, baseEnd_1625816] using wordTrace_append hprefix tailTrace_1625816
  have hstable : (prefixWord ++ tailWord_1625816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625816).length < 2 ^ (prefixWord ++ tailWord_1625816).sum := by decide
  have hdescent : baseEnd_1625816 < baseStart_1625816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625857 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 7]
def baseStart_1625857 : Nat := 118140960795 + 1625857 * 2 ^ 59
def prefixEnd_1625857 : Nat := 4983230072969 + 3 ^ 40 * 1625857 * 2
def baseEnd_1625857 : Nat := 185521359217144569046739

theorem tailTrace_1625857 : CollatzResearch.WordTrace tailWord_1625857 prefixEnd_1625857 185521359217144569046739 := by
  unfold tailWord_1625857
  simp only [CollatzResearch.WordTrace]
  refine ⟨59299876470805238113931825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39533250980536825409287883 59299876470805238113931825)
  ·
    refine ⟨44474907353103928585448869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59299876470805238113931825 44474907353103928585448869)
    ·
      refine ⟨8339045128706986609771663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44474907353103928585448869 8339045128706986609771663)
      ·
        refine ⟨12508567693060479914657495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8339045128706986609771663 12508567693060479914657495)
        ·
          refine ⟨18762851539590719871986243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12508567693060479914657495 18762851539590719871986243)
          ·
            refine ⟨28144277309386079807979365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18762851539590719871986243 28144277309386079807979365)
            ·
              refine ⟨5277051995509889963996131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28144277309386079807979365 5277051995509889963996131)
              ·
                refine ⟨7915577993264834945994197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5277051995509889963996131 7915577993264834945994197)
                ·
                  refine ⟨185521359217144569046739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7915577993264834945994197 185521359217144569046739)
                  ·
                    rfl

theorem cell22_1625857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_1625857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625857 prefixEnd_1625857 := by exact prefixLift 1625857
  have htrace : WordTrace (prefixWord ++ tailWord_1625857) baseStart_1625857 baseEnd_1625857 := by
    simpa [prefixWord, tailWord_1625857, baseEnd_1625857] using wordTrace_append hprefix tailTrace_1625857
  have hstable : (prefixWord ++ tailWord_1625857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625857).length < 2 ^ (prefixWord ++ tailWord_1625857).sum := by decide
  have hdescent : baseEnd_1625857 < baseStart_1625857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625934 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_1625934 : Nat := 118140960795 + 1625934 * 2 ^ 59
def prefixEnd_1625934 : Nat := 4983230072969 + 3 ^ 40 * 1625934 * 2
def baseEnd_1625934 : Nat := 556590436325031172964981

theorem tailTrace_1625934 : CollatzResearch.WordTrace tailWord_1625934 prefixEnd_1625934 556590436325031172964981 := by
  unfold tailWord_1625934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7412835611440785033060607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39535123261017520176323237 7412835611440785033060607)
  ·
    refine ⟨11119253417161177549590911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7412835611440785033060607 11119253417161177549590911)
    ·
      refine ⟨16678880125741766324386367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11119253417161177549590911 16678880125741766324386367)
      ·
        refine ⟨25018320188612649486579551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16678880125741766324386367 25018320188612649486579551)
        ·
          refine ⟨37527480282918974229869327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25018320188612649486579551 37527480282918974229869327)
          ·
            refine ⟨56291220424378461344803991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37527480282918974229869327 56291220424378461344803991)
            ·
              refine ⟨84436830636567692017205987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56291220424378461344803991 84436830636567692017205987)
              ·
                refine ⟨126655245954851538025808981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84436830636567692017205987 126655245954851538025808981)
                ·
                  refine ⟨1484241163533416461239949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 126655245954851538025808981 1484241163533416461239949)
                  ·
                    refine ⟨556590436325031172964981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1484241163533416461239949 556590436325031172964981)
                    ·
                      rfl

theorem cell22_1625934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_1625934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625934 prefixEnd_1625934 := by exact prefixLift 1625934
  have htrace : WordTrace (prefixWord ++ tailWord_1625934) baseStart_1625934 baseEnd_1625934 := by
    simpa [prefixWord, tailWord_1625934, baseEnd_1625934] using wordTrace_append hprefix tailTrace_1625934
  have hstable : (prefixWord ++ tailWord_1625934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625934).length < 2 ^ (prefixWord ++ tailWord_1625934).sum := by decide
  have hdescent : baseEnd_1625934 < baseStart_1625934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625955 : List Nat := [1, 1, 1, 5, 5, 1, 2, 1, 1, 4]
def baseStart_1625955 : Nat := 118140960795 + 1625955 * 2 ^ 59
def prefixEnd_1625955 : Nat := 4983230072969 + 3 ^ 40 * 1625955 * 2
def baseEnd_1625955 : Nat := 556597625054194118189917

theorem tailTrace_1625955 : CollatzResearch.WordTrace tailWord_1625955 prefixEnd_1625955 556597625054194118189917 := by
  unfold tailWord_1625955
  simp only [CollatzResearch.WordTrace]
  refine ⟨59303450824450200850999319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39535633882966800567332879 59303450824450200850999319)
  ·
    refine ⟨88955176236675301276498979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59303450824450200850999319 88955176236675301276498979)
    ·
      refine ⟨133432764355012951914748469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88955176236675301276498979 133432764355012951914748469)
      ·
        refine ⟨12509321658282464242007669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133432764355012951914748469 12509321658282464242007669)
        ·
          refine ⟨1172748905463981022688219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12509321658282464242007669 1172748905463981022688219)
          ·
            refine ⟨1759123358195971534032329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172748905463981022688219 1759123358195971534032329)
            ·
              refine ⟨1319342518646978650524247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1759123358195971534032329 1319342518646978650524247)
              ·
                refine ⟨1979013777970467975786371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319342518646978650524247 1979013777970467975786371)
                ·
                  refine ⟨2968520666955701963679557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1979013777970467975786371 2968520666955701963679557)
                  ·
                    refine ⟨556597625054194118189917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2968520666955701963679557 556597625054194118189917)
                    ·
                      rfl

theorem cell22_1625955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 1, 4].length) (baseStart_1625955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625955 prefixEnd_1625955 := by exact prefixLift 1625955
  have htrace : WordTrace (prefixWord ++ tailWord_1625955) baseStart_1625955 baseEnd_1625955 := by
    simpa [prefixWord, tailWord_1625955, baseEnd_1625955] using wordTrace_append hprefix tailTrace_1625955
  have hstable : (prefixWord ++ tailWord_1625955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625955).length < 2 ^ (prefixWord ++ tailWord_1625955).sum := by decide
  have hdescent : baseEnd_1625955 < baseStart_1625955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625985 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 1, 5]
def baseStart_1625985 : Nat := 118140960795 + 1625985 * 2 ^ 59
def prefixEnd_1625985 : Nat := 4983230072969 + 3 ^ 40 * 1625985 * 2
def baseEnd_1625985 : Nat := 556607894667284039939825

theorem tailTrace_1625985 : CollatzResearch.WordTrace tailWord_1625985 prefixEnd_1625985 556607894667284039939825 := by
  unfold tailWord_1625985
  simp only [CollatzResearch.WordTrace]
  refine ⟨59304545014341515974591409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39536363342894343983060939 59304545014341515974591409)
  ·
    refine ⟨44478408760756136980943557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59304545014341515974591409 44478408760756136980943557)
    ·
      refine ⟨8339701642641775683926917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44478408760756136980943557 8339701642641775683926917)
      ·
        refine ⟨1563694057995332940736297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8339701642641775683926917 1563694057995332940736297)
        ·
          refine ⟨1172770543496499705552223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1563694057995332940736297 1172770543496499705552223)
          ·
            refine ⟨1759155815244749558328335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172770543496499705552223 1759155815244749558328335)
            ·
              refine ⟨2638733722867124337492503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759155815244749558328335 2638733722867124337492503)
              ·
                refine ⟨3958100584300686506238755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2638733722867124337492503 3958100584300686506238755)
                ·
                  refine ⟨5937150876451029759358133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958100584300686506238755 5937150876451029759358133)
                  ·
                    refine ⟨556607894667284039939825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5937150876451029759358133 556607894667284039939825)
                    ·
                      rfl

theorem cell22_1625985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_1625985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1625985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1625985 prefixEnd_1625985 := by exact prefixLift 1625985
  have htrace : WordTrace (prefixWord ++ tailWord_1625985) baseStart_1625985 baseEnd_1625985 := by
    simpa [prefixWord, tailWord_1625985, baseEnd_1625985] using wordTrace_append hprefix tailTrace_1625985
  have hstable : (prefixWord ++ tailWord_1625985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625985).length < 2 ^ (prefixWord ++ tailWord_1625985).sum := by decide
  have hdescent : baseEnd_1625985 < baseStart_1625985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626039 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 3, 4]
def baseStart_1626039 : Nat := 118140960795 + 1626039 * 2 ^ 59
def prefixEnd_1626039 : Nat := 4983230072969 + 3 ^ 40 * 1626039 * 2
def baseEnd_1626039 : Nat := 556626379970845899089659

theorem tailTrace_1626039 : CollatzResearch.WordTrace tailWord_1626039 prefixEnd_1626039 556626379970845899089659 := by
  unfold tailWord_1626039
  simp only [CollatzResearch.WordTrace]
  refine ⟨59306514556145883197057171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39537676370763922131371447 59306514556145883197057171)
  ·
    refine ⟨88959771834218824795585757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59306514556145883197057171 88959771834218824795585757)
    ·
      refine ⟨33359914437832059298344659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88959771834218824795585757 33359914437832059298344659)
      ·
        refine ⟨50039871656748088947516989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33359914437832059298344659 50039871656748088947516989)
        ·
          refine ⟨18764951871280533355318871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50039871656748088947516989 18764951871280533355318871)
          ·
            refine ⟨28147427806920800032978307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18764951871280533355318871 28147427806920800032978307)
            ·
              refine ⟨42221141710381200049467461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28147427806920800032978307 42221141710381200049467461)
              ·
                refine ⟨7916464070696475009275149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42221141710381200049467461 7916464070696475009275149)
                ·
                  refine ⟨2968674026511178128478181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7916464070696475009275149 2968674026511178128478181)
                  ·
                    refine ⟨556626379970845899089659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2968674026511178128478181 556626379970845899089659)
                    ·
                      rfl

theorem cell22_1626039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_1626039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626039 prefixEnd_1626039 := by exact prefixLift 1626039
  have htrace : WordTrace (prefixWord ++ tailWord_1626039) baseStart_1626039 baseEnd_1626039 := by
    simpa [prefixWord, tailWord_1626039, baseEnd_1626039] using wordTrace_append hprefix tailTrace_1626039
  have hstable : (prefixWord ++ tailWord_1626039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626039).length < 2 ^ (prefixWord ++ tailWord_1626039).sum := by decide
  have hdescent : baseEnd_1626039 < baseStart_1626039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626056 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 3, 4]
def baseStart_1626056 : Nat := 118140960795 + 1626056 * 2 ^ 59
def prefixEnd_1626056 : Nat := 4983230072969 + 3 ^ 40 * 1626056 * 2
def baseEnd_1626056 : Nat := 556632199418263521414607

theorem tailTrace_1626056 : CollatzResearch.WordTrace tailWord_1626056 prefixEnd_1626056 556632199418263521414607 := by
  unfold tailWord_1626056
  simp only [CollatzResearch.WordTrace]
  refine ⟨29653567298542147550213011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39538089731389530066950681 29653567298542147550213011)
  ·
    refine ⟨44480350947813221325319517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29653567298542147550213011 44480350947813221325319517)
    ·
      refine ⟨16680131605429957996994819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44480350947813221325319517 16680131605429957996994819)
      ·
        refine ⟨25020197408144936995492229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16680131605429957996994819 25020197408144936995492229)
        ·
          refine ⟨4691287014027175686654793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25020197408144936995492229 4691287014027175686654793)
          ·
            refine ⟨3518465260520381764991095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4691287014027175686654793 3518465260520381764991095)
            ·
              refine ⟨5277697890780572647486643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3518465260520381764991095 5277697890780572647486643)
              ·
                refine ⟨7916546836170858971229965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5277697890780572647486643 7916546836170858971229965)
                ·
                  refine ⟨2968705063564072114211237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7916546836170858971229965 2968705063564072114211237)
                  ·
                    refine ⟨556632199418263521414607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2968705063564072114211237 556632199418263521414607)
                    ·
                      rfl

theorem cell22_1626056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_1626056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626056 prefixEnd_1626056 := by exact prefixLift 1626056
  have htrace : WordTrace (prefixWord ++ tailWord_1626056) baseStart_1626056 baseEnd_1626056 := by
    simpa [prefixWord, tailWord_1626056, baseEnd_1626056] using wordTrace_append hprefix tailTrace_1626056
  have hstable : (prefixWord ++ tailWord_1626056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626056).length < 2 ^ (prefixWord ++ tailWord_1626056).sum := by decide
  have hdescent : baseEnd_1626056 < baseStart_1626056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626071 : List Nat := [1, 1, 3, 2, 1, 1, 4, 5, 4]
def baseStart_1626071 : Nat := 118140960795 + 1626071 * 2 ^ 59
def prefixEnd_1626071 : Nat := 4983230072969 + 3 ^ 40 * 1626071 * 2
def baseEnd_1626071 : Nat := 185545778074936160763187

theorem tailTrace_1626071 : CollatzResearch.WordTrace tailWord_1626071 prefixEnd_1626071 185545778074936160763187 := by
  unfold tailWord_1626071
  simp only [CollatzResearch.WordTrace]
  refine ⟨59307681692029952662222067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39538454461353301774814711 59307681692029952662222067)
  ·
    refine ⟨88961522538044928993333101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59307681692029952662222067 88961522538044928993333101)
    ·
      refine ⟨33360570951766848372499913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88961522538044928993333101 33360570951766848372499913)
      ·
        refine ⟨25020428213825136279374935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33360570951766848372499913 25020428213825136279374935)
        ·
          refine ⟨37530642320737704419062403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25020428213825136279374935 37530642320737704419062403)
          ·
            refine ⟨56295963481106556628593605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37530642320737704419062403 56295963481106556628593605)
            ·
              refine ⟨10555493152707479367861301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56295963481106556628593605 10555493152707479367861301)
              ·
                refine ⟨989577483066326190736997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10555493152707479367861301 989577483066326190736997)
                ·
                  refine ⟨185545778074936160763187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 989577483066326190736997 185545778074936160763187)
                  ·
                    rfl

theorem cell22_1626071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 4].length) (baseStart_1626071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626071 prefixEnd_1626071 := by exact prefixLift 1626071
  have htrace : WordTrace (prefixWord ++ tailWord_1626071) baseStart_1626071 baseEnd_1626071 := by
    simpa [prefixWord, tailWord_1626071, baseEnd_1626071] using wordTrace_append hprefix tailTrace_1626071
  have hstable : (prefixWord ++ tailWord_1626071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626071).length < 2 ^ (prefixWord ++ tailWord_1626071).sum := by decide
  have hdescent : baseEnd_1626071 < baseStart_1626071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626159 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 1, 7]
def baseStart_1626159 : Nat := 118140960795 + 1626159 * 2 ^ 59
def prefixEnd_1626159 : Nat := 4983230072969 + 3 ^ 40 * 1626159 * 2
def baseEnd_1626159 : Nat := 556667458423205586089291

theorem tailTrace_1626159 : CollatzResearch.WordTrace tailWord_1626159 prefixEnd_1626159 556667458423205586089291 := by
  unfold tailWord_1626159
  simp only [CollatzResearch.WordTrace]
  refine ⟨59310891315711143691425531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39540594210474095794283687 59310891315711143691425531)
  ·
    refine ⟨88966336973566715537138297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59310891315711143691425531 88966336973566715537138297)
    ·
      refine ⟨66724752730175036652853723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88966336973566715537138297 66724752730175036652853723)
      ·
        refine ⟨100087129095262554979280585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66724752730175036652853723 100087129095262554979280585)
        ·
          refine ⟨75065346821446916234460439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100087129095262554979280585 75065346821446916234460439)
          ·
            refine ⟨112598020232170374351690659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75065346821446916234460439 112598020232170374351690659)
            ·
              refine ⟨168897030348255561527535989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112598020232170374351690659 168897030348255561527535989)
              ·
                refine ⟨15834096595148958893206499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168897030348255561527535989 15834096595148958893206499)
                ·
                  refine ⟨23751144892723438339809749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15834096595148958893206499 23751144892723438339809749)
                  ·
                    refine ⟨556667458423205586089291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23751144892723438339809749 556667458423205586089291)
                    ·
                      rfl

theorem cell22_1626159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_1626159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626159 prefixEnd_1626159 := by exact prefixLift 1626159
  have htrace : WordTrace (prefixWord ++ tailWord_1626159) baseStart_1626159 baseEnd_1626159 := by
    simpa [prefixWord, tailWord_1626159, baseEnd_1626159] using wordTrace_append hprefix tailTrace_1626159
  have hstable : (prefixWord ++ tailWord_1626159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626159).length < 2 ^ (prefixWord ++ tailWord_1626159).sum := by decide
  have hdescent : baseEnd_1626159 < baseStart_1626159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626285 : List Nat := [1, 5, 2, 1, 2, 2, 3, 6]
def baseStart_1626285 : Nat := 118140960795 + 1626285 * 2 ^ 59
def prefixEnd_1626285 : Nat := 4983230072969 + 3 ^ 40 * 1626285 * 2
def baseEnd_1626285 : Nat := 61856732310909250826545

theorem tailTrace_1626285 : CollatzResearch.WordTrace tailWord_1626285 prefixEnd_1626285 61856732310909250826545 := by
  unfold tailWord_1626285
  simp only [CollatzResearch.WordTrace]
  refine ⟨59315486913254667210512309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39543657942169778140341539 59315486913254667210512309)
  ·
    refine ⟨5560826898117625050985529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59315486913254667210512309 5560826898117625050985529)
    ·
      refine ⟨4170620173588218788239147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5560826898117625050985529 4170620173588218788239147)
      ·
        refine ⟨6255930260382328182358721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170620173588218788239147 6255930260382328182358721)
        ·
          refine ⟨4691947695286746136769041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6255930260382328182358721 4691947695286746136769041)
          ·
            refine ⟨3518960771465059602576781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4691947695286746136769041 3518960771465059602576781)
            ·
              refine ⟨1319610289299397350966293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3518960771465059602576781 1319610289299397350966293)
              ·
                refine ⟨61856732310909250826545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1319610289299397350966293 61856732310909250826545)
                ·
                  rfl

theorem cell22_1626285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 6].length) (baseStart_1626285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626285 prefixEnd_1626285 := by exact prefixLift 1626285
  have htrace : WordTrace (prefixWord ++ tailWord_1626285) baseStart_1626285 baseEnd_1626285 := by
    simpa [prefixWord, tailWord_1626285, baseEnd_1626285] using wordTrace_append hprefix tailTrace_1626285
  have hstable : (prefixWord ++ tailWord_1626285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626285).length < 2 ^ (prefixWord ++ tailWord_1626285).sum := by decide
  have hdescent : baseEnd_1626285 < baseStart_1626285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626296 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 7]
def baseStart_1626296 : Nat := 118140960795 + 1626296 * 2 ^ 59
def prefixEnd_1626296 : Nat := 4983230072969 + 3 ^ 40 * 1626296 * 2
def baseEnd_1626296 : Nat := 185571452107660965137957

theorem tailTrace_1626296 : CollatzResearch.WordTrace tailWord_1626296 prefixEnd_1626296 185571452107660965137957 := by
  unfold tailWord_1626296
  simp only [CollatzResearch.WordTrace]
  refine ⟨29657944058107408044581371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39543925410809877392775161 29657944058107408044581371)
  ·
    refine ⟨44486916087161112066872057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29657944058107408044581371 44486916087161112066872057)
    ·
      refine ⟨33365187065370834050154043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44486916087161112066872057 33365187065370834050154043)
      ·
        refine ⟨50047780598056251075231065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33365187065370834050154043 50047780598056251075231065)
        ·
          refine ⟨37535835448542188306423299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50047780598056251075231065 37535835448542188306423299)
          ·
            refine ⟨56303753172813282459634949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37535835448542188306423299 56303753172813282459634949)
            ·
              refine ⟨10556953719902490461181553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56303753172813282459634949 10556953719902490461181553)
              ·
                refine ⟨7917715289926867845886165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10556953719902490461181553 7917715289926867845886165)
                ·
                  refine ⟨185571452107660965137957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7917715289926867845886165 185571452107660965137957)
                  ·
                    rfl

theorem cell22_1626296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_1626296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626296 prefixEnd_1626296 := by exact prefixLift 1626296
  have htrace : WordTrace (prefixWord ++ tailWord_1626296) baseStart_1626296 baseEnd_1626296 := by
    simpa [prefixWord, tailWord_1626296, baseEnd_1626296] using wordTrace_append hprefix tailTrace_1626296
  have hstable : (prefixWord ++ tailWord_1626296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626296).length < 2 ^ (prefixWord ++ tailWord_1626296).sum := by decide
  have hdescent : baseEnd_1626296 < baseStart_1626296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626306 : List Nat := [3, 5, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1626306 : Nat := 118140960795 + 1626306 * 2 ^ 59
def prefixEnd_1626306 : Nat := 4983230072969 + 3 ^ 40 * 1626306 * 2
def baseEnd_1626306 : Nat := 556717779527346202663841

theorem tailTrace_1626306 : CollatzResearch.WordTrace tailWord_1626306 prefixEnd_1626306 556717779527346202663841 := by
  unfold tailWord_1626306
  simp only [CollatzResearch.WordTrace]
  refine ⟨14829063211544646949256693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39544168564119058531351181 14829063211544646949256693)
  ·
    refine ⟨1390224676082310651492815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14829063211544646949256693 1390224676082310651492815)
    ·
      refine ⟨2085337014123465977239223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1390224676082310651492815 2085337014123465977239223)
      ·
        refine ⟨3128005521185198965858835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2085337014123465977239223 3128005521185198965858835)
        ·
          refine ⟨4692008281777798448788253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3128005521185198965858835 4692008281777798448788253)
          ·
            refine ⟨1759503105666674418295595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4692008281777798448788253 1759503105666674418295595)
            ·
              refine ⟨2639254658500011627443393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759503105666674418295595 2639254658500011627443393)
              ·
                refine ⟨1979440993875008720582545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2639254658500011627443393 1979440993875008720582545)
                ·
                  refine ⟨1484580745406256540436909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1979440993875008720582545 1484580745406256540436909)
                  ·
                    refine ⟨556717779527346202663841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1484580745406256540436909 556717779527346202663841)
                    ·
                      rfl

theorem cell22_1626306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1626306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626306 prefixEnd_1626306 := by exact prefixLift 1626306
  have htrace : WordTrace (prefixWord ++ tailWord_1626306) baseStart_1626306 baseEnd_1626306 := by
    simpa [prefixWord, tailWord_1626306, baseEnd_1626306] using wordTrace_append hprefix tailTrace_1626306
  have hstable : (prefixWord ++ tailWord_1626306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626306).length < 2 ^ (prefixWord ++ tailWord_1626306).sum := by decide
  have hdescent : baseEnd_1626306 < baseStart_1626306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626328 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 2, 5]
def baseStart_1626328 : Nat := 118140960795 + 1626328 * 2 ^ 59
def prefixEnd_1626328 : Nat := 4983230072969 + 3 ^ 40 * 1626328 * 2
def baseEnd_1626328 : Nat := 556725310576945478613773

theorem tailTrace_1626328 : CollatzResearch.WordTrace tailWord_1626328 prefixEnd_1626328 556725310576945478613773 := by
  unfold tailWord_1626328
  simp only [CollatzResearch.WordTrace]
  refine ⟨29658527626049442777163819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39544703501399257036218425 29658527626049442777163819)
  ·
    refine ⟨44487791439074164165745729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29658527626049442777163819 44487791439074164165745729)
    ·
      refine ⟨33365843579305623124309297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44487791439074164165745729 33365843579305623124309297)
      ·
        refine ⟨25024382684479217343231973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33365843579305623124309297 25024382684479217343231973)
        ·
          refine ⟨4692071753339853251855995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25024382684479217343231973 4692071753339853251855995)
          ·
            refine ⟨7038107630009779877783993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4692071753339853251855995 7038107630009779877783993)
            ·
              refine ⟨5278580722507334908337995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7038107630009779877783993 5278580722507334908337995)
              ·
                refine ⟨7917871083761002362506993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5278580722507334908337995 7917871083761002362506993)
                ·
                  refine ⟨5938403312820751771880245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7917871083761002362506993 5938403312820751771880245)
                  ·
                    refine ⟨556725310576945478613773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5938403312820751771880245 556725310576945478613773)
                    ·
                      rfl

theorem cell22_1626328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_1626328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626328 prefixEnd_1626328 := by exact prefixLift 1626328
  have htrace : WordTrace (prefixWord ++ tailWord_1626328) baseStart_1626328 baseEnd_1626328 := by
    simpa [prefixWord, tailWord_1626328, baseEnd_1626328] using wordTrace_append hprefix tailTrace_1626328
  have hstable : (prefixWord ++ tailWord_1626328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626328).length < 2 ^ (prefixWord ++ tailWord_1626328).sum := by decide
  have hdescent : baseEnd_1626328 < baseStart_1626328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626358 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_1626358 : Nat := 118140960795 + 1626358 * 2 ^ 59
def prefixEnd_1626358 : Nat := 4983230072969 + 3 ^ 40 * 1626358 * 2
def baseEnd_1626358 : Nat := 185578526730011800121227

theorem tailTrace_1626358 : CollatzResearch.WordTrace tailWord_1626358 prefixEnd_1626358 185578526730011800121227 := by
  unfold tailWord_1626358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707384340124387542369983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39545432961326800451946485 3707384340124387542369983)
  ·
    refine ⟨5561076510186581313554975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3707384340124387542369983 5561076510186581313554975)
    ·
      refine ⟨8341614765279871970332463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5561076510186581313554975 8341614765279871970332463)
      ·
        refine ⟨12512422147919807955498695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8341614765279871970332463 12512422147919807955498695)
        ·
          refine ⟨18768633221879711933248043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12512422147919807955498695 18768633221879711933248043)
          ·
            refine ⟨28152949832819567899872065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18768633221879711933248043 28152949832819567899872065)
            ·
              refine ⟨21114712374614675924904049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28152949832819567899872065 21114712374614675924904049)
              ·
                refine ⟨15836034280961006943678037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21114712374614675924904049 15836034280961006943678037)
                ·
                  refine ⟨185578526730011800121227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15836034280961006943678037 185578526730011800121227)
                  ·
                    rfl

theorem cell22_1626358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_1626358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626358 prefixEnd_1626358 := by exact prefixLift 1626358
  have htrace : WordTrace (prefixWord ++ tailWord_1626358) baseStart_1626358 baseEnd_1626358 := by
    simpa [prefixWord, tailWord_1626358, baseEnd_1626358] using wordTrace_append hprefix tailTrace_1626358
  have hstable : (prefixWord ++ tailWord_1626358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626358).length < 2 ^ (prefixWord ++ tailWord_1626358).sum := by decide
  have hdescent : baseEnd_1626358 < baseStart_1626358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626394 : List Nat := [3, 1, 1, 3, 5, 1, 1, 2, 1, 4]
def baseStart_1626394 : Nat := 118140960795 + 1626394 * 2 ^ 59
def prefixEnd_1626394 : Nat := 4983230072969 + 3 ^ 40 * 1626394 * 2
def baseEnd_1626394 : Nat := 556747903725743306463571

theorem tailTrace_1626394 : CollatzResearch.WordTrace tailWord_1626394 prefixEnd_1626394 556747903725743306463571 := by
  unfold tailWord_1626394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14829865617464944706557559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39546308313239852550820157 14829865617464944706557559)
  ·
    refine ⟨22244798426197417059836339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14829865617464944706557559 22244798426197417059836339)
    ·
      refine ⟨33367197639296125589754509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22244798426197417059836339 33367197639296125589754509)
      ·
        refine ⟨12512699114736047096157941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33367197639296125589754509 12512699114736047096157941)
        ·
          refine ⟨1173065542006504415264807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12512699114736047096157941 1173065542006504415264807)
          ·
            refine ⟨1759598313009756622897211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173065542006504415264807 1759598313009756622897211)
            ·
              refine ⟨2639397469514634934345817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759598313009756622897211 2639397469514634934345817)
              ·
                refine ⟨1979548102135976200759363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2639397469514634934345817 1979548102135976200759363)
                ·
                  refine ⟨2969322153203964301139045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1979548102135976200759363 2969322153203964301139045)
                  ·
                    refine ⟨556747903725743306463571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2969322153203964301139045 556747903725743306463571)
                    ·
                      rfl

theorem cell22_1626394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_1626394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626394 prefixEnd_1626394 := by exact prefixLift 1626394
  have htrace : WordTrace (prefixWord ++ tailWord_1626394) baseStart_1626394 baseEnd_1626394 := by
    simpa [prefixWord, tailWord_1626394, baseEnd_1626394] using wordTrace_append hprefix tailTrace_1626394
  have hstable : (prefixWord ++ tailWord_1626394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626394).length < 2 ^ (prefixWord ++ tailWord_1626394).sum := by decide
  have hdescent : baseEnd_1626394 < baseStart_1626394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626452 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_1626452 : Nat := 118140960795 + 1626452 * 2 ^ 59
def prefixEnd_1626452 : Nat := 4983230072969 + 3 ^ 40 * 1626452 * 2
def baseEnd_1626452 : Nat := 556767758311050488513393

theorem tailTrace_1626452 : CollatzResearch.WordTrace tailWord_1626452 prefixEnd_1626452 556767758311050488513393 := by
  unfold tailWord_1626452
  simp only [CollatzResearch.WordTrace]
  refine ⟨29660788951824827365920805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39547718602433103154561073 29660788951824827365920805)
  ·
    refine ⟨5561397928467155131110151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29660788951824827365920805 5561397928467155131110151)
    ·
      refine ⟨8342096892700732696665227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5561397928467155131110151 8342096892700732696665227)
      ·
        refine ⟨12513145339051099044997841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8342096892700732696665227 12513145339051099044997841)
        ·
          refine ⟨9384859004288324283748381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12513145339051099044997841 9384859004288324283748381)
          ·
            refine ⟨3519322126608121606405643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9384859004288324283748381 3519322126608121606405643)
            ·
              refine ⟨5278983189912182409608465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3519322126608121606405643 5278983189912182409608465)
              ·
                refine ⟨3959237392434136807206349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5278983189912182409608465 3959237392434136807206349)
                ·
                  refine ⟨1484714022162801302702381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3959237392434136807206349 1484714022162801302702381)
                  ·
                    refine ⟨556767758311050488513393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1484714022162801302702381 556767758311050488513393)
                    ·
                      rfl

theorem cell22_1626452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_1626452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626452 prefixEnd_1626452 := by exact prefixLift 1626452
  have htrace : WordTrace (prefixWord ++ tailWord_1626452) baseStart_1626452 baseEnd_1626452 := by
    simpa [prefixWord, tailWord_1626452, baseEnd_1626452] using wordTrace_append hprefix tailTrace_1626452
  have hstable : (prefixWord ++ tailWord_1626452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626452).length < 2 ^ (prefixWord ++ tailWord_1626452).sum := by decide
  have hdescent : baseEnd_1626452 < baseStart_1626452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626462 : List Nat := [4, 4, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1626462 : Nat := 118140960795 + 1626462 * 2 ^ 59
def prefixEnd_1626462 : Nat := 4983230072969 + 3 ^ 40 * 1626462 * 2
def baseEnd_1626462 : Nat := 556771181515413795763363

theorem tailTrace_1626462 : CollatzResearch.WordTrace tailWord_1626462 prefixEnd_1626462 556771181515413795763363 := by
  unfold tailWord_1626462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7415242829201678304963205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39547961755742284293137093 7415242829201678304963205)
  ·
    refine ⟨1390358030475314682180601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7415242829201678304963205 1390358030475314682180601)
    ·
      refine ⟨1042768522856486011635451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1390358030475314682180601 1042768522856486011635451)
      ·
        refine ⟨1564152784284729017453177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042768522856486011635451 1564152784284729017453177)
        ·
          refine ⟨1173114588213546763089883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1564152784284729017453177 1173114588213546763089883)
          ·
            refine ⟨1759671882320320144634825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173114588213546763089883 1759671882320320144634825)
            ·
              refine ⟨1319753911740240108476119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1759671882320320144634825 1319753911740240108476119)
              ·
                refine ⟨1979630867610360162714179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319753911740240108476119 1979630867610360162714179)
                ·
                  refine ⟨2969446301415540244071269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1979630867610360162714179 2969446301415540244071269)
                  ·
                    refine ⟨556771181515413795763363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2969446301415540244071269 556771181515413795763363)
                    ·
                      rfl

theorem cell22_1626462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1626462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626462 prefixEnd_1626462 := by exact prefixLift 1626462
  have htrace : WordTrace (prefixWord ++ tailWord_1626462) baseStart_1626462 baseEnd_1626462 := by
    simpa [prefixWord, tailWord_1626462, baseEnd_1626462] using wordTrace_append hprefix tailTrace_1626462
  have hstable : (prefixWord ++ tailWord_1626462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626462).length < 2 ^ (prefixWord ++ tailWord_1626462).sum := by decide
  have hdescent : baseEnd_1626462 < baseStart_1626462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626469 : List Nat := [1, 3, 1, 3, 1, 4, 2, 3, 1, 3]
def baseStart_1626469 : Nat := 118140960795 + 1626469 * 2 ^ 59
def prefixEnd_1626469 : Nat := 4983230072969 + 3 ^ 40 * 1626469 * 2
def baseEnd_1626469 : Nat := 556773577758468110838341

theorem tailTrace_1626469 : CollatzResearch.WordTrace tailWord_1626469 prefixEnd_1626469 556773577758468110838341 := by
  unfold tailWord_1626469
  simp only [CollatzResearch.WordTrace]
  refine ⟨59322197944588066635210461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39548131963058711090140307 59322197944588066635210461)
  ·
    refine ⟨22245824229220524988203923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59322197944588066635210461 22245824229220524988203923)
    ·
      refine ⟨33368736343830787482305885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22245824229220524988203923 33368736343830787482305885)
      ·
        refine ⟨12513276128936545305864707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33368736343830787482305885 12513276128936545305864707)
        ·
          refine ⟨18769914193404817958797061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12513276128936545305864707 18769914193404817958797061)
          ·
            refine ⟨3519358911263403367274449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18769914193404817958797061 3519358911263403367274449)
            ·
              refine ⟨2639519183447552525455837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3519358911263403367274449 2639519183447552525455837)
              ·
                refine ⟨989819693792832197045939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2639519183447552525455837 989819693792832197045939)
                ·
                  refine ⟨1484729540689248295568909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989819693792832197045939 1484729540689248295568909)
                  ·
                    refine ⟨556773577758468110838341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1484729540689248295568909 556773577758468110838341)
                    ·
                      rfl

theorem cell22_1626469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_1626469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626469 prefixEnd_1626469 := by exact prefixLift 1626469
  have htrace : WordTrace (prefixWord ++ tailWord_1626469) baseStart_1626469 baseEnd_1626469 := by
    simpa [prefixWord, tailWord_1626469, baseEnd_1626469] using wordTrace_append hprefix tailTrace_1626469
  have hstable : (prefixWord ++ tailWord_1626469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626469).length < 2 ^ (prefixWord ++ tailWord_1626469).sum := by decide
  have hdescent : baseEnd_1626469 < baseStart_1626469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626482 : List Nat := [3, 2, 1, 2, 1, 5, 1, 2, 5]
def baseStart_1626482 : Nat := 118140960795 + 1626482 * 2 ^ 59
def prefixEnd_1626482 : Nat := 4983230072969 + 3 ^ 40 * 1626482 * 2
def baseEnd_1626482 : Nat := 185592675974713470087767

theorem tailTrace_1626482 : CollatzResearch.WordTrace tailWord_1626482 prefixEnd_1626482 185592675974713470087767 := by
  unfold tailWord_1626482
  simp only [CollatzResearch.WordTrace]
  refine ⟨14830668023385242463858425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39548448062360646570289133 14830668023385242463858425)
  ·
    refine ⟨11123001017538931847893819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14830668023385242463858425 11123001017538931847893819)
    ·
      refine ⟨16684501526308397771840729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11123001017538931847893819 16684501526308397771840729)
      ·
        refine ⟨12513376144731298328880547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16684501526308397771840729 12513376144731298328880547)
        ·
          refine ⟨18770064217096947493320821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12513376144731298328880547 18770064217096947493320821)
          ·
            refine ⟨1759693520352838827498827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18770064217096947493320821 1759693520352838827498827)
            ·
              refine ⟨2639540280529258241248241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759693520352838827498827 2639540280529258241248241)
              ·
                refine ⟨1979655210396943680936181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2639540280529258241248241 1979655210396943680936181)
                ·
                  refine ⟨185592675974713470087767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1979655210396943680936181 185592675974713470087767)
                  ·
                    rfl

theorem cell22_1626482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_1626482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626482 prefixEnd_1626482 := by exact prefixLift 1626482
  have htrace : WordTrace (prefixWord ++ tailWord_1626482) baseStart_1626482 baseEnd_1626482 := by
    simpa [prefixWord, tailWord_1626482, baseEnd_1626482] using wordTrace_append hprefix tailTrace_1626482
  have hstable : (prefixWord ++ tailWord_1626482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626482).length < 2 ^ (prefixWord ++ tailWord_1626482).sum := by decide
  have hdescent : baseEnd_1626482 < baseStart_1626482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626486 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_1626486 : Nat := 118140960795 + 1626486 * 2 ^ 59
def prefixEnd_1626486 : Nat := 4983230072969 + 3 ^ 40 * 1626486 * 2
def baseEnd_1626486 : Nat := 556779397205885733163289

theorem tailTrace_1626486 : CollatzResearch.WordTrace tailWord_1626486 prefixEnd_1626486 556779397205885733163289 := by
  unfold tailWord_1626486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707676124095404908661207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39548545323684319025719541 3707676124095404908661207)
  ·
    refine ⟨5561514186143107362991811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3707676124095404908661207 5561514186143107362991811)
    ·
      refine ⟨8342271279214661044487717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5561514186143107362991811 8342271279214661044487717)
      ·
        refine ⟨1564175864852748945841447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8342271279214661044487717 1564175864852748945841447)
        ·
          refine ⟨2346263797279123418762171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564175864852748945841447 2346263797279123418762171)
          ·
            refine ⟨3519395695918685128143257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2346263797279123418762171 3519395695918685128143257)
            ·
              refine ⟨2639546771939013846107443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3519395695918685128143257 2639546771939013846107443)
              ·
                refine ⟨3959320157908520769161165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639546771939013846107443 3959320157908520769161165)
                ·
                  refine ⟨1484745059215695288435437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3959320157908520769161165 1484745059215695288435437)
                  ·
                    refine ⟨556779397205885733163289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1484745059215695288435437 556779397205885733163289)
                    ·
                      rfl

theorem cell22_1626486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_1626486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626486 prefixEnd_1626486 := by exact prefixLift 1626486
  have htrace : WordTrace (prefixWord ++ tailWord_1626486) baseStart_1626486 baseEnd_1626486 := by
    simpa [prefixWord, tailWord_1626486, baseEnd_1626486] using wordTrace_append hprefix tailTrace_1626486
  have hstable : (prefixWord ++ tailWord_1626486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626486).length < 2 ^ (prefixWord ++ tailWord_1626486).sum := by decide
  have hdescent : baseEnd_1626486 < baseStart_1626486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626604 : List Nat := [2, 2, 1, 1, 2, 1, 5, 4, 1, 3]
def baseStart_1626604 : Nat := 118140960795 + 1626604 * 2 ^ 59
def prefixEnd_1626604 : Nat := 4983230072969 + 3 ^ 40 * 1626604 * 2
def baseEnd_1626604 : Nat := 556819791017372758712927

theorem tailTrace_1626604 : CollatzResearch.WordTrace tailWord_1626604 prefixEnd_1626604 556819791017372758712927 := by
  unfold tailWord_1626604
  simp only [CollatzResearch.WordTrace]
  refine ⟨29663560899549492345687433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39551414532732656460916577 29663560899549492345687433)
  ·
    refine ⟨22247670674662119259265575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29663560899549492345687433 22247670674662119259265575)
    ·
      refine ⟨33371506011993178888898363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22247670674662119259265575 33371506011993178888898363)
      ·
        refine ⟨50057259017989768333347545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33371506011993178888898363 50057259017989768333347545)
        ·
          refine ⟨37542944263492326250010659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50057259017989768333347545 37542944263492326250010659)
          ·
            refine ⟨56314416395238489375015989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37542944263492326250010659 56314416395238489375015989)
            ·
              refine ⟨5279476537053608378907749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56314416395238489375015989 5279476537053608378907749)
              ·
                refine ⟨989901850697551571045203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5279476537053608378907749 989901850697551571045203)
                ·
                  refine ⟨1484852776046327356567805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989901850697551571045203 1484852776046327356567805)
                  ·
                    refine ⟨556819791017372758712927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1484852776046327356567805 556819791017372758712927)
                    ·
                      rfl

theorem cell22_1626604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_1626604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626604 prefixEnd_1626604 := by exact prefixLift 1626604
  have htrace : WordTrace (prefixWord ++ tailWord_1626604) baseStart_1626604 baseEnd_1626604 := by
    simpa [prefixWord, tailWord_1626604, baseEnd_1626604] using wordTrace_append hprefix tailTrace_1626604
  have hstable : (prefixWord ++ tailWord_1626604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626604).length < 2 ^ (prefixWord ++ tailWord_1626604).sum := by decide
  have hdescent : baseEnd_1626604 < baseStart_1626604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626645 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 8]
def baseStart_1626645 : Nat := 118140960795 + 1626645 * 2 ^ 59
def prefixEnd_1626645 : Nat := 4983230072969 + 3 ^ 40 * 1626645 * 2
def baseEnd_1626645 : Nat := 185611275385087439479267

theorem tailTrace_1626645 : CollatzResearch.WordTrace tailWord_1626645 prefixEnd_1626645 185611275385087439479267 := by
  unfold tailWord_1626645
  simp only [CollatzResearch.WordTrace]
  refine ⟨59328617191950448693617389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39552411461300299129078259 59328617191950448693617389)
  ·
    refine ⟨22248231446981418260106521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59328617191950448693617389 22248231446981418260106521)
    ·
      refine ⟨16686173585236063695079891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22248231446981418260106521 16686173585236063695079891)
      ·
        refine ⟨25029260377854095542619837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16686173585236063695079891 25029260377854095542619837)
        ·
          refine ⟨9385972641695285828482439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25029260377854095542619837 9385972641695285828482439)
          ·
            refine ⟨14078958962542928742723659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9385972641695285828482439 14078958962542928742723659)
            ·
              refine ⟨21118438443814393114085489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14078958962542928742723659 21118438443814393114085489)
              ·
                refine ⟨15838828832860794835564117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21118438443814393114085489 15838828832860794835564117)
                ·
                  refine ⟨185611275385087439479267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15838828832860794835564117 185611275385087439479267)
                  ·
                    rfl

theorem cell22_1626645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_1626645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626645 prefixEnd_1626645 := by exact prefixLift 1626645
  have htrace : WordTrace (prefixWord ++ tailWord_1626645) baseStart_1626645 baseEnd_1626645 := by
    simpa [prefixWord, tailWord_1626645, baseEnd_1626645] using wordTrace_append hprefix tailTrace_1626645
  have hstable : (prefixWord ++ tailWord_1626645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626645).length < 2 ^ (prefixWord ++ tailWord_1626645).sum := by decide
  have hdescent : baseEnd_1626645 < baseStart_1626645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626675 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 3, 6]
def baseStart_1626675 : Nat := 118140960795 + 1626675 * 2 ^ 59
def prefixEnd_1626675 : Nat := 4983230072969 + 3 ^ 40 * 1626675 * 2
def baseEnd_1626675 : Nat := 556844095768352240187709

theorem tailTrace_1626675 : CollatzResearch.WordTrace tailWord_1626675 prefixEnd_1626675 556844095768352240187709 := by
  unfold tailWord_1626675
  simp only [CollatzResearch.WordTrace]
  refine ⟨59329711381841763817209479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39553140921227842544806319 59329711381841763817209479)
  ·
    refine ⟨88994567072762645725814219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59329711381841763817209479 88994567072762645725814219)
    ·
      refine ⟨133491850609143968588721329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88994567072762645725814219 133491850609143968588721329)
      ·
        refine ⟨100118887956857976441540997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133491850609143968588721329 100118887956857976441540997)
        ·
          refine ⟨18772291491910870582788937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100118887956857976441540997 18772291491910870582788937)
          ·
            refine ⟨14079218618933152937091703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18772291491910870582788937 14079218618933152937091703)
            ·
              refine ⟨21118827928399729405637555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14079218618933152937091703 21118827928399729405637555)
              ·
                refine ⟨31678241892599594108456333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21118827928399729405637555 31678241892599594108456333)
                ·
                  refine ⟨11879340709724847790671125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31678241892599594108456333 11879340709724847790671125)
                  ·
                    refine ⟨556844095768352240187709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11879340709724847790671125 556844095768352240187709)
                    ·
                      rfl

theorem cell22_1626675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_1626675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626675 prefixEnd_1626675 := by exact prefixLift 1626675
  have htrace : WordTrace (prefixWord ++ tailWord_1626675) baseStart_1626675 baseEnd_1626675 := by
    simpa [prefixWord, tailWord_1626675, baseEnd_1626675] using wordTrace_append hprefix tailTrace_1626675
  have hstable : (prefixWord ++ tailWord_1626675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626675).length < 2 ^ (prefixWord ++ tailWord_1626675).sum := by decide
  have hdescent : baseEnd_1626675 < baseStart_1626675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626784 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 2, 5]
def baseStart_1626784 : Nat := 118140960795 + 1626784 * 2 ^ 59
def prefixEnd_1626784 : Nat := 4983230072969 + 3 ^ 40 * 1626784 * 2
def baseEnd_1626784 : Nat := 556881408695912289212375

theorem tailTrace_1626784 : CollatzResearch.WordTrace tailWord_1626784 prefixEnd_1626784 556881408695912289212375 := by
  unfold tailWord_1626784
  simp only [CollatzResearch.WordTrace]
  refine ⟨29666843469223437716463703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39555791292297916955284937 29666843469223437716463703)
  ·
    refine ⟨44500265203835156574695555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29666843469223437716463703 44500265203835156574695555)
    ·
      refine ⟨66750397805752734862043333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44500265203835156574695555 66750397805752734862043333)
      ·
        refine ⟨12515699588578637786633125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66750397805752734862043333 12515699588578637786633125)
        ·
          refine ⟨2346693672858494584993711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12515699588578637786633125 2346693672858494584993711)
          ·
            refine ⟨3520040509287741877490567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2346693672858494584993711 3520040509287741877490567)
            ·
              refine ⟨5280060763931612816235851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3520040509287741877490567 5280060763931612816235851)
              ·
                refine ⟨7920091145897419224353777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5280060763931612816235851 7920091145897419224353777)
                ·
                  refine ⟨5940068359423064418265333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7920091145897419224353777 5940068359423064418265333)
                  ·
                    refine ⟨556881408695912289212375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5940068359423064418265333 556881408695912289212375)
                    ·
                      rfl

theorem cell22_1626784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_1626784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626784 prefixEnd_1626784 := by exact prefixLift 1626784
  have htrace : WordTrace (prefixWord ++ tailWord_1626784) baseStart_1626784 baseEnd_1626784 := by
    simpa [prefixWord, tailWord_1626784, baseEnd_1626784] using wordTrace_append hprefix tailTrace_1626784
  have hstable : (prefixWord ++ tailWord_1626784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626784).length < 2 ^ (prefixWord ++ tailWord_1626784).sum := by decide
  have hdescent : baseEnd_1626784 < baseStart_1626784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626816 : List Nat := [2, 1, 1, 2, 4, 2, 4, 1, 1, 4]
def baseStart_1626816 : Nat := 118140960795 + 1626816 * 2 ^ 59
def prefixEnd_1626816 : Nat := 4983230072969 + 3 ^ 40 * 1626816 * 2
def baseEnd_1626816 : Nat := 556892362949874872412277

theorem tailTrace_1626816 : CollatzResearch.WordTrace tailWord_1626816 prefixEnd_1626816 556892362949874872412277 := by
  unfold tailWord_1626816
  simp only [CollatzResearch.WordTrace]
  refine ⟨29667427037165472449046151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39556569382887296598728201 29667427037165472449046151)
  ·
    refine ⟨44501140555748208673569227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29667427037165472449046151 44501140555748208673569227)
    ·
      refine ⟨66751710833622313010353841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44501140555748208673569227 66751710833622313010353841)
      ·
        refine ⟨50063783125216734757765381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66751710833622313010353841 50063783125216734757765381)
        ·
          refine ⟨9386959335978137767081009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50063783125216734757765381 9386959335978137767081009)
          ·
            refine ⟨7040219501983603325310757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9386959335978137767081009 7040219501983603325310757)
            ·
              refine ⟨1320041156621925623495767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7040219501983603325310757 1320041156621925623495767)
              ·
                refine ⟨1980061734932888435243651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320041156621925623495767 1980061734932888435243651)
                ·
                  refine ⟨2970092602399332652865477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980061734932888435243651 2970092602399332652865477)
                  ·
                    refine ⟨556892362949874872412277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2970092602399332652865477 556892362949874872412277)
                    ·
                      rfl

theorem cell22_1626816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 1, 4].length) (baseStart_1626816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626816 prefixEnd_1626816 := by exact prefixLift 1626816
  have htrace : WordTrace (prefixWord ++ tailWord_1626816) baseStart_1626816 baseEnd_1626816 := by
    simpa [prefixWord, tailWord_1626816, baseEnd_1626816] using wordTrace_append hprefix tailTrace_1626816
  have hstable : (prefixWord ++ tailWord_1626816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626816).length < 2 ^ (prefixWord ++ tailWord_1626816).sum := by decide
  have hdescent : baseEnd_1626816 < baseStart_1626816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626842 : List Nat := [3, 1, 1, 2, 2, 2, 2, 9]
def baseStart_1626842 : Nat := 118140960795 + 1626842 * 2 ^ 59
def prefixEnd_1626842 : Nat := 4983230072969 + 3 ^ 40 * 1626842 * 2
def baseEnd_1626842 : Nat := 61877918142357719029133

theorem tailTrace_1626842 : CollatzResearch.WordTrace tailWord_1626842 prefixEnd_1626842 61877918142357719029133 := by
  unfold tailWord_1626842
  simp only [CollatzResearch.WordTrace]
  refine ⟨14833950593059187834634695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39557201581491167559025853 14833950593059187834634695)
  ·
    refine ⟨22250925889588781751952043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14833950593059187834634695 22250925889588781751952043)
    ·
      refine ⟨33376388834383172627928065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22250925889588781751952043 33376388834383172627928065)
      ·
        refine ⟨25032291625787379470946049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33376388834383172627928065 25032291625787379470946049)
        ·
          refine ⟨18774218719340534603209537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25032291625787379470946049 18774218719340534603209537)
          ·
            refine ⟨14080664039505400952407153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18774218719340534603209537 14080664039505400952407153)
            ·
              refine ⟨10560498029629050714305365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14080664039505400952407153 10560498029629050714305365)
              ·
                refine ⟨61877918142357719029133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10560498029629050714305365 61877918142357719029133)
                ·
                  rfl

theorem cell22_1626842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_1626842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626842 prefixEnd_1626842 := by exact prefixLift 1626842
  have htrace : WordTrace (prefixWord ++ tailWord_1626842) baseStart_1626842 baseEnd_1626842 := by
    simpa [prefixWord, tailWord_1626842, baseEnd_1626842] using wordTrace_append hprefix tailTrace_1626842
  have hstable : (prefixWord ++ tailWord_1626842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626842).length < 2 ^ (prefixWord ++ tailWord_1626842).sum := by decide
  have hdescent : baseEnd_1626842 < baseStart_1626842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626874 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 5, 3]
def baseStart_1626874 : Nat := 118140960795 + 1626874 * 2 ^ 59
def prefixEnd_1626874 : Nat := 4983230072969 + 3 ^ 40 * 1626874 * 2
def baseEnd_1626874 : Nat := 556912217535182054462099

theorem tailTrace_1626874 : CollatzResearch.WordTrace tailWord_1626874 prefixEnd_1626874 556912217535182054462099 := by
  unfold tailWord_1626874
  simp only [CollatzResearch.WordTrace]
  refine ⟨14834242377030205200925919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39557979672080547202469117 14834242377030205200925919)
  ·
    refine ⟨22251363565545307801388879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14834242377030205200925919 22251363565545307801388879)
    ·
      refine ⟨33377045348317961702083319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22251363565545307801388879 33377045348317961702083319)
      ·
        refine ⟨50065568022476942553124979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33377045348317961702083319 50065568022476942553124979)
        ·
          refine ⟨75098352033715413829687469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50065568022476942553124979 75098352033715413829687469)
          ·
            refine ⟨28161882012643280186132801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75098352033715413829687469 28161882012643280186132801)
            ·
              refine ⟨21121411509482460139599601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28161882012643280186132801 21121411509482460139599601)
              ·
                refine ⟨15841058632111845104699701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21121411509482460139599601 15841058632111845104699701)
                ·
                  refine ⟨1485099246760485478565597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15841058632111845104699701 1485099246760485478565597)
                  ·
                    refine ⟨556912217535182054462099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1485099246760485478565597 556912217535182054462099)
                    ·
                      rfl

theorem cell22_1626874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_1626874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626874 prefixEnd_1626874 := by exact prefixLift 1626874
  have htrace : WordTrace (prefixWord ++ tailWord_1626874) baseStart_1626874 baseEnd_1626874 := by
    simpa [prefixWord, tailWord_1626874, baseEnd_1626874] using wordTrace_append hprefix tailTrace_1626874
  have hstable : (prefixWord ++ tailWord_1626874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626874).length < 2 ^ (prefixWord ++ tailWord_1626874).sum := by decide
  have hdescent : baseEnd_1626874 < baseStart_1626874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626983 : List Nat := [1, 1, 5, 1, 2, 3, 2, 3, 4]
def baseStart_1626983 : Nat := 118140960795 + 1626983 * 2 ^ 59
def prefixEnd_1626983 : Nat := 4983230072969 + 3 ^ 40 * 1626983 * 2
def baseEnd_1626983 : Nat := 185649843487580701162255

theorem tailTrace_1626983 : CollatzResearch.WordTrace tailWord_1626983 prefixEnd_1626983 185649843487580701162255 := by
  unfold tailWord_1626983
  simp only [CollatzResearch.WordTrace]
  refine ⟨59340945064725932419421603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39560630043150621612947735 59340945064725932419421603)
  ·
    refine ⟨89011417597088898629132405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59340945064725932419421603 89011417597088898629132405)
    ·
      refine ⟨8344820399727084246481163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89011417597088898629132405 8344820399727084246481163)
      ·
        refine ⟨12517230599590626369721745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8344820399727084246481163 12517230599590626369721745)
        ·
          refine ⟨9387922949692969777291309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12517230599590626369721745 9387922949692969777291309)
          ·
            refine ⟨3520471106134863666484241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9387922949692969777291309 3520471106134863666484241)
            ·
              refine ⟨2640353329601147749863181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3520471106134863666484241 2640353329601147749863181)
              ·
                refine ⟨990132498600430406198693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2640353329601147749863181 990132498600430406198693)
                ·
                  refine ⟨185649843487580701162255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 990132498600430406198693 185649843487580701162255)
                  ·
                    rfl

theorem cell22_1626983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 4].length) (baseStart_1626983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1626983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1626983 prefixEnd_1626983 := by exact prefixLift 1626983
  have htrace : WordTrace (prefixWord ++ tailWord_1626983) baseStart_1626983 baseEnd_1626983 := by
    simpa [prefixWord, tailWord_1626983, baseEnd_1626983] using wordTrace_append hprefix tailTrace_1626983
  have hstable : (prefixWord ++ tailWord_1626983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626983).length < 2 ^ (prefixWord ++ tailWord_1626983).sum := by decide
  have hdescent : baseEnd_1626983 < baseStart_1626983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627015 : List Nat := [1, 1, 4, 2, 3, 2, 3, 1, 2, 3]
def baseStart_1627015 : Nat := 118140960795 + 1627015 * 2 ^ 59
def prefixEnd_1627015 : Nat := 4983230072969 + 3 ^ 40 * 1627015 * 2
def baseEnd_1627015 : Nat := 556960484716704686686667

theorem tailTrace_1627015 : CollatzResearch.WordTrace tailWord_1627015 prefixEnd_1627015 556960484716704686686667 := by
  unfold tailWord_1627015
  simp only [CollatzResearch.WordTrace]
  refine ⟨59342112200610001884586499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39561408133740001256390999 59342112200610001884586499)
  ·
    refine ⟨89013168300915002826879749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59342112200610001884586499 89013168300915002826879749)
    ·
      refine ⟨16689969056421563030039953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89013168300915002826879749 16689969056421563030039953)
      ·
        refine ⟨12517476792316172272529965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16689969056421563030039953 12517476792316172272529965)
        ·
          refine ⟨4694053797118564602198737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12517476792316172272529965 4694053797118564602198737)
          ·
            refine ⟨3520540347838923451649053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4694053797118564602198737 3520540347838923451649053)
            ·
              refine ⟨1320202630439596294368395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3520540347838923451649053 1320202630439596294368395)
              ·
                refine ⟨1980303945659394441552593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320202630439596294368395 1980303945659394441552593)
                ·
                  refine ⟨1485227959244545831164445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1980303945659394441552593 1485227959244545831164445)
                  ·
                    refine ⟨556960484716704686686667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1485227959244545831164445 556960484716704686686667)
                    ·
                      rfl

theorem cell22_1627015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_1627015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627015 prefixEnd_1627015 := by exact prefixLift 1627015
  have htrace : WordTrace (prefixWord ++ tailWord_1627015) baseStart_1627015 baseEnd_1627015 := by
    simpa [prefixWord, tailWord_1627015, baseEnd_1627015] using wordTrace_append hprefix tailTrace_1627015
  have hstable : (prefixWord ++ tailWord_1627015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627015).length < 2 ^ (prefixWord ++ tailWord_1627015).sum := by decide
  have hdescent : baseEnd_1627015 < baseStart_1627015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627030 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1627030 : Nat := 118140960795 + 1627030 * 2 ^ 59
def prefixEnd_1627030 : Nat := 4983230072969 + 3 ^ 40 * 1627030 * 2
def baseEnd_1627030 : Nat := 556965619523249647561621

theorem tailTrace_1627030 : CollatzResearch.WordTrace tailWord_1627030 prefixEnd_1627030 556965619523249647561621 := by
  unfold tailWord_1627030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3708916205972228715398909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39561772863703772964255029 3708916205972228715398909)
  ·
    refine ⟨1390843577239585768274591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3708916205972228715398909 1390843577239585768274591)
    ·
      refine ⟨2086265365859378652411887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1390843577239585768274591 2086265365859378652411887)
      ·
        refine ⟨3129398048789067978617831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2086265365859378652411887 3129398048789067978617831)
        ·
          refine ⟨4694097073183601967926747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3129398048789067978617831 4694097073183601967926747)
          ·
            refine ⟨7041145609775402951890121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4694097073183601967926747 7041145609775402951890121)
            ·
              refine ⟨5280859207331552213917591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7041145609775402951890121 5280859207331552213917591)
              ·
                refine ⟨7921288810997328320876387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5280859207331552213917591 7921288810997328320876387)
                ·
                  refine ⟨11881933216495992481314581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7921288810997328320876387 11881933216495992481314581)
                  ·
                    refine ⟨556965619523249647561621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11881933216495992481314581 556965619523249647561621)
                    ·
                      rfl

theorem cell22_1627030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1627030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627030 prefixEnd_1627030 := by exact prefixLift 1627030
  have htrace : WordTrace (prefixWord ++ tailWord_1627030) baseStart_1627030 baseEnd_1627030 := by
    simpa [prefixWord, tailWord_1627030, baseEnd_1627030] using wordTrace_append hprefix tailTrace_1627030
  have hstable : (prefixWord ++ tailWord_1627030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627030).length < 2 ^ (prefixWord ++ tailWord_1627030).sum := by decide
  have hdescent : baseEnd_1627030 < baseStart_1627030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627062 : List Nat := [5, 1, 4, 1, 1, 1, 2, 7]
def baseStart_1627062 : Nat := 118140960795 + 1627062 * 2 ^ 59
def prefixEnd_1627062 : Nat := 4983230072969 + 3 ^ 40 * 1627062 * 2
def baseEnd_1627062 : Nat := 61886285975245803417947

theorem tailTrace_1627062 : CollatzResearch.WordTrace tailWord_1627062 prefixEnd_1627062 61886285975245803417947 := by
  unfold tailWord_1627062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3708989151964983056971715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39562550954293152607698293 3708989151964983056971715)
  ·
    refine ⟨5563483727947474585457573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3708989151964983056971715 5563483727947474585457573)
    ·
      refine ⟨1043153198990151484773295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5563483727947474585457573 1043153198990151484773295)
      ·
        refine ⟨1564729798485227227159943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1043153198990151484773295 1564729798485227227159943)
        ·
          refine ⟨2347094697727840840739915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564729798485227227159943 2347094697727840840739915)
          ·
            refine ⟨3520642046591761261109873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347094697727840840739915 3520642046591761261109873)
            ·
              refine ⟨2640481534943820945832405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3520642046591761261109873 2640481534943820945832405)
              ·
                refine ⟨61886285975245803417947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2640481534943820945832405 61886285975245803417947)
                ·
                  rfl

theorem cell22_1627062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_1627062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627062 prefixEnd_1627062 := by exact prefixLift 1627062
  have htrace : WordTrace (prefixWord ++ tailWord_1627062) baseStart_1627062 baseEnd_1627062 := by
    simpa [prefixWord, tailWord_1627062, baseEnd_1627062] using wordTrace_append hprefix tailTrace_1627062
  have hstable : (prefixWord ++ tailWord_1627062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627062).length < 2 ^ (prefixWord ++ tailWord_1627062).sum := by decide
  have hdescent : baseEnd_1627062 < baseStart_1627062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627148 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_1627148 : Nat := 118140960795 + 1627148 * 2 ^ 59
def prefixEnd_1627148 : Nat := 4983230072969 + 3 ^ 40 * 1627148 * 2
def baseEnd_1627148 : Nat := 557006013334736673111259

theorem tailTrace_1627148 : CollatzResearch.WordTrace tailWord_1627148 prefixEnd_1627148 557006013334736673111259 := by
  unfold tailWord_1627148
  simp only [CollatzResearch.WordTrace]
  refine ⟨29673481554564082799589049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39564642072752110399452065 29673481554564082799589049)
  ·
    refine ⟨22255111165923062099691787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29673481554564082799589049 22255111165923062099691787)
    ·
      refine ⟨33382666748884593149537681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22255111165923062099691787 33382666748884593149537681)
      ·
        refine ⟨25037000061663444862153261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33382666748884593149537681 25037000061663444862153261)
        ·
          refine ⟨9388875023123791823307473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25037000061663444862153261 9388875023123791823307473)
          ·
            refine ⟨7041656267342843867480605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9388875023123791823307473 7041656267342843867480605)
            ·
              refine ⟨2640621100253566450305227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7041656267342843867480605 2640621100253566450305227)
              ·
                refine ⟨3960931650380349675457841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2640621100253566450305227 3960931650380349675457841)
                ·
                  refine ⟨2970698737785262256593381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3960931650380349675457841 2970698737785262256593381)
                  ·
                    refine ⟨557006013334736673111259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2970698737785262256593381 557006013334736673111259)
                    ·
                      rfl

theorem cell22_1627148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_1627148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627148 prefixEnd_1627148 := by exact prefixLift 1627148
  have htrace : WordTrace (prefixWord ++ tailWord_1627148) baseStart_1627148 baseEnd_1627148 := by
    simpa [prefixWord, tailWord_1627148, baseEnd_1627148] using wordTrace_append hprefix tailTrace_1627148
  have hstable : (prefixWord ++ tailWord_1627148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627148).length < 2 ^ (prefixWord ++ tailWord_1627148).sum := by decide
  have hdescent : baseEnd_1627148 < baseStart_1627148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627154 : List Nat := [3, 2, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1627154 : Nat := 118140960795 + 1627154 * 2 ^ 59
def prefixEnd_1627154 : Nat := 4983230072969 + 3 ^ 40 * 1627154 * 2
def baseEnd_1627154 : Nat := 557008067257354657461241

theorem tailTrace_1627154 : CollatzResearch.WordTrace tailWord_1627154 prefixEnd_1627154 557008067257354657461241 := by
  unfold tailWord_1627154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14836795486776607155974129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39564787964737619082597677 14836795486776607155974129)
  ·
    refine ⟨11127596615082455366980597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14836795486776607155974129 11127596615082455366980597)
    ·
      refine ⟨1043212182663980190654431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11127596615082455366980597 1043212182663980190654431)
      ·
        refine ⟨1564818273995970285981647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1043212182663980190654431 1564818273995970285981647)
        ·
          refine ⟨2347227410993955428972471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564818273995970285981647 2347227410993955428972471)
          ·
            refine ⟨3520841116490933143458707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347227410993955428972471 3520841116490933143458707)
            ·
              refine ⟨5281261674736399715188061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3520841116490933143458707 5281261674736399715188061)
              ·
                refine ⟨1980473128026149893195523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5281261674736399715188061 1980473128026149893195523)
                ·
                  refine ⟨2970709692039224839793285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980473128026149893195523 2970709692039224839793285)
                  ·
                    refine ⟨557008067257354657461241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2970709692039224839793285 557008067257354657461241)
                    ·
                      rfl

theorem cell22_1627154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1627154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627154 prefixEnd_1627154 := by exact prefixLift 1627154
  have htrace : WordTrace (prefixWord ++ tailWord_1627154) baseStart_1627154 baseEnd_1627154 := by
    simpa [prefixWord, tailWord_1627154, baseEnd_1627154] using wordTrace_append hprefix tailTrace_1627154
  have hstable : (prefixWord ++ tailWord_1627154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627154).length < 2 ^ (prefixWord ++ tailWord_1627154).sum := by decide
  have hdescent : baseEnd_1627154 < baseStart_1627154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627229 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1627229 : Nat := 118140960795 + 1627229 * 2 ^ 59
def prefixEnd_1627229 : Nat := 4983230072969 + 3 ^ 40 * 1627229 * 2
def baseEnd_1627229 : Nat := 557033741290079461836011

theorem tailTrace_1627229 : CollatzResearch.WordTrace tailWord_1627229 prefixEnd_1627229 557033741290079461836011 := by
  unfold tailWord_1627229
  simp only [CollatzResearch.WordTrace]
  refine ⟨59349917421834716432876741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39566611614556477621917827 59349917421834716432876741)
  ·
    refine ⟨11128109516594009331164389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59349917421834716432876741 11128109516594009331164389)
    ·
      refine ⟨2086520534361376749593323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11128109516594009331164389 2086520534361376749593323)
      ·
        refine ⟨3129780801542065124389985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2086520534361376749593323 3129780801542065124389985)
        ·
          refine ⟨2347335601156548843292489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3129780801542065124389985 2347335601156548843292489)
          ·
            refine ⟨1760501700867411632469367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2347335601156548843292489 1760501700867411632469367)
            ·
              refine ⟨2640752551301117448704051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760501700867411632469367 2640752551301117448704051)
              ·
                refine ⟨3961128826951676173056077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2640752551301117448704051 3961128826951676173056077)
                ·
                  refine ⟨1485423310106878564896029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3961128826951676173056077 1485423310106878564896029)
                  ·
                    refine ⟨557033741290079461836011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1485423310106878564896029 557033741290079461836011)
                    ·
                      rfl

theorem cell22_1627229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1627229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627229 prefixEnd_1627229 := by exact prefixLift 1627229
  have htrace : WordTrace (prefixWord ++ tailWord_1627229) baseStart_1627229 baseEnd_1627229 := by
    simpa [prefixWord, tailWord_1627229, baseEnd_1627229] using wordTrace_append hprefix tailTrace_1627229
  have hstable : (prefixWord ++ tailWord_1627229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627229).length < 2 ^ (prefixWord ++ tailWord_1627229).sum := by decide
  have hdescent : baseEnd_1627229 < baseStart_1627229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627242 : List Nat := [3, 1, 3, 2, 2, 3, 2, 1, 5]
def baseStart_1627242 : Nat := 118140960795 + 1627242 * 2 ^ 59
def prefixEnd_1627242 : Nat := 4983230072969 + 3 ^ 40 * 1627242 * 2
def baseEnd_1627242 : Nat := 185679397151917253753657

theorem tailTrace_1627242 : CollatzResearch.WordTrace tailWord_1627242 prefixEnd_1627242 185679397151917253753657 := by
  unfold tailWord_1627242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14837597892696904913274995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39566927713858413102066653 14837597892696904913274995)
  ·
    refine ⟨22256396839045357369912493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14837597892696904913274995 22256396839045357369912493)
    ·
      refine ⟨8346148814642009013717185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22256396839045357369912493 8346148814642009013717185)
      ·
        refine ⟨6259611610981506760287889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8346148814642009013717185 6259611610981506760287889)
        ·
          refine ⟨4694708708236130070215917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6259611610981506760287889 4694708708236130070215917)
          ·
            refine ⟨1760515765588548776330969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4694708708236130070215917 1760515765588548776330969)
            ·
              refine ⟨1320386824191411582248227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1760515765588548776330969 1320386824191411582248227)
              ·
                refine ⟨1980580236287117373372341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320386824191411582248227 1980580236287117373372341)
                ·
                  refine ⟨185679397151917253753657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1980580236287117373372341 185679397151917253753657)
                  ·
                    rfl

theorem cell22_1627242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_1627242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627242 prefixEnd_1627242 := by exact prefixLift 1627242
  have htrace : WordTrace (prefixWord ++ tailWord_1627242) baseStart_1627242 baseEnd_1627242 := by
    simpa [prefixWord, tailWord_1627242, baseEnd_1627242] using wordTrace_append hprefix tailTrace_1627242
  have hstable : (prefixWord ++ tailWord_1627242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627242).length < 2 ^ (prefixWord ++ tailWord_1627242).sum := by decide
  have hdescent : baseEnd_1627242 < baseStart_1627242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627251 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 7, 5]
def baseStart_1627251 : Nat := 118140960795 + 1627251 * 2 ^ 59
def prefixEnd_1627251 : Nat := 4983230072969 + 3 ^ 40 * 1627251 * 2
def baseEnd_1627251 : Nat := 557041272339678737785943

theorem tailTrace_1627251 : CollatzResearch.WordTrace tailWord_1627251 prefixEnd_1627251 557041272339678737785943 := by
  unfold tailWord_1627251
  simp only [CollatzResearch.WordTrace]
  refine ⟨59350719827755014190177607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39567146551836676126785071 59350719827755014190177607)
  ·
    refine ⟨89026079741632521285266411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59350719827755014190177607 89026079741632521285266411)
    ·
      refine ⟨133539119612448781927899617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89026079741632521285266411 133539119612448781927899617)
      ·
        refine ⟨100154339709336586445924713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133539119612448781927899617 100154339709336586445924713)
        ·
          refine ⟨75115754782002439834443535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100154339709336586445924713 75115754782002439834443535)
          ·
            refine ⟨112673632173003659751665303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75115754782002439834443535 112673632173003659751665303)
            ·
              refine ⟨169010448259505489627497955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112673632173003659751665303 169010448259505489627497955)
              ·
                refine ⟨253515672389258234441246933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169010448259505489627497955 253515672389258234441246933)
                ·
                  refine ⟨5941773571623239869716725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 253515672389258234441246933 5941773571623239869716725)
                  ·
                    refine ⟨557041272339678737785943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5941773571623239869716725 557041272339678737785943)
                    ·
                      rfl

theorem cell22_1627251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_1627251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627251 prefixEnd_1627251 := by exact prefixLift 1627251
  have htrace : WordTrace (prefixWord ++ tailWord_1627251) baseStart_1627251 baseEnd_1627251 := by
    simpa [prefixWord, tailWord_1627251, baseEnd_1627251] using wordTrace_append hprefix tailTrace_1627251
  have hstable : (prefixWord ++ tailWord_1627251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627251).length < 2 ^ (prefixWord ++ tailWord_1627251).sum := by decide
  have hdescent : baseEnd_1627251 < baseStart_1627251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627268 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1627268 : Nat := 118140960795 + 1627268 * 2 ^ 59
def prefixEnd_1627268 : Nat := 4983230072969 + 3 ^ 40 * 1627268 * 2
def baseEnd_1627268 : Nat := 557047091787096360110891

theorem tailTrace_1627268 : CollatzResearch.WordTrace tailWord_1627268 prefixEnd_1627268 557047091787096360110891 := by
  unfold tailWord_1627268
  simp only [CollatzResearch.WordTrace]
  refine ⟨29675669934346713046773229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39567559912462284062364305 29675669934346713046773229)
  ·
    refine ⟨11128376225380017392539961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29675669934346713046773229 11128376225380017392539961)
    ·
      refine ⟨8346282169035013044404971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11128376225380017392539961 8346282169035013044404971)
      ·
        refine ⟨12519423253552519566607457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8346282169035013044404971 12519423253552519566607457)
        ·
          refine ⟨9389567440164389674955593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12519423253552519566607457 9389567440164389674955593)
          ·
            refine ⟨7042175580123292256216695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9389567440164389674955593 7042175580123292256216695)
            ·
              refine ⟨10563263370184938384325043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7042175580123292256216695 10563263370184938384325043)
              ·
                refine ⟨15844895055277407576487565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10563263370184938384325043 15844895055277407576487565)
                ·
                  refine ⟨5941835645729027841182837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15844895055277407576487565 5941835645729027841182837)
                  ·
                    refine ⟨557047091787096360110891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5941835645729027841182837 557047091787096360110891)
                    ·
                      rfl

theorem cell22_1627268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1627268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627268 prefixEnd_1627268 := by exact prefixLift 1627268
  have htrace : WordTrace (prefixWord ++ tailWord_1627268) baseStart_1627268 baseEnd_1627268 := by
    simpa [prefixWord, tailWord_1627268, baseEnd_1627268] using wordTrace_append hprefix tailTrace_1627268
  have hstable : (prefixWord ++ tailWord_1627268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627268).length < 2 ^ (prefixWord ++ tailWord_1627268).sum := by decide
  have hdescent : baseEnd_1627268 < baseStart_1627268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627283 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 2, 4]
def baseStart_1627283 : Nat := 118140960795 + 1627283 * 2 ^ 59
def prefixEnd_1627283 : Nat := 4983230072969 + 3 ^ 40 * 1627283 * 2
def baseEnd_1627283 : Nat := 557052226593641320985845

theorem tailTrace_1627283 : CollatzResearch.WordTrace tailWord_1627283 prefixEnd_1627283 557052226593641320985845 := by
  unfold tailWord_1627283
  simp only [CollatzResearch.WordTrace]
  refine ⟨59351886963639083655342503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39567924642426055770228335 59351886963639083655342503)
  ·
    refine ⟨89027830445458625483013755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59351886963639083655342503 89027830445458625483013755)
    ·
      refine ⟨133541745668187938224520633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89027830445458625483013755 133541745668187938224520633)
      ·
        refine ⟨100156309251140953668390475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133541745668187938224520633 100156309251140953668390475)
        ·
          refine ⟨150234463876711430502585713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100156309251140953668390475 150234463876711430502585713)
          ·
            refine ⟨112675847907533572876939285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150234463876711430502585713 112675847907533572876939285)
            ·
              refine ⟨5281680370665636228606529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112675847907533572876939285 5281680370665636228606529)
              ·
                refine ⟨3961260277999227171454897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5281680370665636228606529 3961260277999227171454897)
                ·
                  refine ⟨2970945208499420378591173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3961260277999227171454897 2970945208499420378591173)
                  ·
                    refine ⟨557052226593641320985845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2970945208499420378591173 557052226593641320985845)
                    ·
                      rfl

theorem cell22_1627283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 4].length) (baseStart_1627283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627283 prefixEnd_1627283 := by exact prefixLift 1627283
  have htrace : WordTrace (prefixWord ++ tailWord_1627283) baseStart_1627283 baseEnd_1627283 := by
    simpa [prefixWord, tailWord_1627283, baseEnd_1627283] using wordTrace_append hprefix tailTrace_1627283
  have hstable : (prefixWord ++ tailWord_1627283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627283).length < 2 ^ (prefixWord ++ tailWord_1627283).sum := by decide
  have hdescent : baseEnd_1627283 < baseStart_1627283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627287 : List Nat := [1, 1, 3, 3, 3, 1, 4, 2, 4]
def baseStart_1627287 : Nat := 118140960795 + 1627287 * 2 ^ 59
def prefixEnd_1627287 : Nat := 4983230072969 + 3 ^ 40 * 1627287 * 2
def baseEnd_1627287 : Nat := 185684531958462214628611

theorem tailTrace_1627287 : CollatzResearch.WordTrace tailWord_1627287 prefixEnd_1627287 185684531958462214628611 := by
  unfold tailWord_1627287
  simp only [CollatzResearch.WordTrace]
  refine ⟨59352032855624592338488115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39568021903749728225658743 59352032855624592338488115)
  ·
    refine ⟨89028049283436888507732173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59352032855624592338488115 89028049283436888507732173)
    ·
      refine ⟨33385518481288833190399565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89028049283436888507732173 33385518481288833190399565)
      ·
        refine ⟨12519569430483312446399837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33385518481288833190399565 12519569430483312446399837)
        ·
          refine ⟨4694838536431242167399939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12519569430483312446399837 4694838536431242167399939)
          ·
            refine ⟨7042257804646863251099909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4694838536431242167399939 7042257804646863251099909)
            ·
              refine ⟨1320423338371286859581233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7042257804646863251099909 1320423338371286859581233)
              ·
                refine ⟨990317503778465144685925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320423338371286859581233 990317503778465144685925)
                ·
                  refine ⟨185684531958462214628611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 990317503778465144685925 185684531958462214628611)
                  ·
                    rfl

theorem cell22_1627287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 4].length) (baseStart_1627287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627287 prefixEnd_1627287 := by exact prefixLift 1627287
  have htrace : WordTrace (prefixWord ++ tailWord_1627287) baseStart_1627287 baseEnd_1627287 := by
    simpa [prefixWord, tailWord_1627287, baseEnd_1627287] using wordTrace_append hprefix tailTrace_1627287
  have hstable : (prefixWord ++ tailWord_1627287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627287).length < 2 ^ (prefixWord ++ tailWord_1627287).sum := by decide
  have hdescent : baseEnd_1627287 < baseStart_1627287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627343 : List Nat := [1, 1, 2, 1, 1, 3, 2, 6, 5]
def baseStart_1627343 : Nat := 118140960795 + 1627343 * 2 ^ 59
def prefixEnd_1627343 : Nat := 4983230072969 + 3 ^ 40 * 1627343 * 2
def baseEnd_1627343 : Nat := 185690921939940388161887

theorem tailTrace_1627343 : CollatzResearch.WordTrace tailWord_1627343 prefixEnd_1627343 185690921939940388161887 := by
  unfold tailWord_1627343
  simp only [CollatzResearch.WordTrace]
  refine ⟨59354075343421713902526683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39569383562281142601684455 59354075343421713902526683)
  ·
    refine ⟨89031113015132570853790025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59354075343421713902526683 89031113015132570853790025)
    ·
      refine ⟨66773334761349428140342519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89031113015132570853790025 66773334761349428140342519)
      ·
        refine ⟨100160002142024142210513779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66773334761349428140342519 100160002142024142210513779)
        ·
          refine ⟨150240003213036213315770669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100160002142024142210513779 150240003213036213315770669)
          ·
            refine ⟨56340001204888579993414001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150240003213036213315770669 56340001204888579993414001)
            ·
              refine ⟨42255000903666434995060501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56340001204888579993414001 42255000903666434995060501)
              ·
                refine ⟨1980703167359364140393461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42255000903666434995060501 1980703167359364140393461)
                ·
                  refine ⟨185690921939940388161887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1980703167359364140393461 185690921939940388161887)
                  ·
                    rfl

theorem cell22_1627343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 5].length) (baseStart_1627343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627343 prefixEnd_1627343 := by exact prefixLift 1627343
  have htrace : WordTrace (prefixWord ++ tailWord_1627343) baseStart_1627343 baseEnd_1627343 := by
    simpa [prefixWord, tailWord_1627343, baseEnd_1627343] using wordTrace_append hprefix tailTrace_1627343
  have hstable : (prefixWord ++ tailWord_1627343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627343).length < 2 ^ (prefixWord ++ tailWord_1627343).sum := by decide
  have hdescent : baseEnd_1627343 < baseStart_1627343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627424 : List Nat := [2, 1, 1, 5, 3, 2, 1, 2, 1, 4]
def baseStart_1627424 : Nat := 118140960795 + 1627424 * 2 ^ 59
def prefixEnd_1627424 : Nat := 4983230072969 + 3 ^ 40 * 1627424 * 2
def baseEnd_1627424 : Nat := 557100493775163953210413

theorem tailTrace_1627424 : CollatzResearch.WordTrace tailWord_1627424 prefixEnd_1627424 557100493775163953210413 := by
  unfold tailWord_1627424
  simp only [CollatzResearch.WordTrace]
  refine ⟨29678514828064132368112663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39571353104085509824150217 29678514828064132368112663)
  ·
    refine ⟨44517772242096198552168995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29678514828064132368112663 44517772242096198552168995)
    ·
      refine ⟨66776658363144297828253493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44517772242096198552168995 66776658363144297828253493)
      ·
        refine ⟨6260311721544777921398765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66776658363144297828253493 6260311721544777921398765)
        ·
          refine ⟨2347616895579291720524537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6260311721544777921398765 2347616895579291720524537)
          ·
            refine ⟨1760712671684468790393403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2347616895579291720524537 1760712671684468790393403)
            ·
              refine ⟨2641069007526703185590105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760712671684468790393403 2641069007526703185590105)
              ·
                refine ⟨1980801755645027389192579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641069007526703185590105 1980801755645027389192579)
                ·
                  refine ⟨2971202633467541083788869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1980801755645027389192579 2971202633467541083788869)
                  ·
                    refine ⟨557100493775163953210413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2971202633467541083788869 557100493775163953210413)
                    ·
                      rfl

theorem cell22_1627424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 1, 4].length) (baseStart_1627424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627424 prefixEnd_1627424 := by exact prefixLift 1627424
  have htrace : WordTrace (prefixWord ++ tailWord_1627424) baseStart_1627424 baseEnd_1627424 := by
    simpa [prefixWord, tailWord_1627424, baseEnd_1627424] using wordTrace_append hprefix tailTrace_1627424
  have hstable : (prefixWord ++ tailWord_1627424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627424).length < 2 ^ (prefixWord ++ tailWord_1627424).sum := by decide
  have hdescent : baseEnd_1627424 < baseStart_1627424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627437 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1627437 : Nat := 118140960795 + 1627437 * 2 ^ 59
def prefixEnd_1627437 : Nat := 4983230072969 + 3 ^ 40 * 1627437 * 2
def baseEnd_1627437 : Nat := 557104943940836252635373

theorem tailTrace_1627437 : CollatzResearch.WordTrace tailWord_1627437 prefixEnd_1627437 557104943940836252635373 := by
  unfold tailWord_1627437
  simp only [CollatzResearch.WordTrace]
  refine ⟨59357503805081167956448565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39571669203387445304299043 59357503805081167956448565)
  ·
    refine ⟨5564765981726359495917053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59357503805081167956448565 5564765981726359495917053)
    ·
      refine ⟨2086787243147384810968895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5564765981726359495917053 2086787243147384810968895)
      ·
        refine ⟨3130180864721077216453343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2086787243147384810968895 3130180864721077216453343)
        ·
          refine ⟨4695271297081615824680015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3130180864721077216453343 4695271297081615824680015)
          ·
            refine ⟨7042906945622423737020023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4695271297081615824680015 7042906945622423737020023)
            ·
              refine ⟨10564360418433635605530035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7042906945622423737020023 10564360418433635605530035)
              ·
                refine ⟨15846540627650453408295053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10564360418433635605530035 15846540627650453408295053)
                ·
                  refine ⟨5942452735368920028110645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15846540627650453408295053 5942452735368920028110645)
                  ·
                    refine ⟨557104943940836252635373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5942452735368920028110645 557104943940836252635373)
                    ·
                      rfl

theorem cell22_1627437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1627437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627437 prefixEnd_1627437 := by exact prefixLift 1627437
  have htrace : WordTrace (prefixWord ++ tailWord_1627437) baseStart_1627437 baseEnd_1627437 := by
    simpa [prefixWord, tailWord_1627437, baseEnd_1627437] using wordTrace_append hprefix tailTrace_1627437
  have hstable : (prefixWord ++ tailWord_1627437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627437).length < 2 ^ (prefixWord ++ tailWord_1627437).sum := by decide
  have hdescent : baseEnd_1627437 < baseStart_1627437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627454 : List Nat := [4, 2, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_1627454 : Nat := 118140960795 + 1627454 * 2 ^ 59
def prefixEnd_1627454 : Nat := 4983230072969 + 3 ^ 40 * 1627454 * 2
def baseEnd_1627454 : Nat := 557110763388253874960321

theorem tailTrace_1627454 : CollatzResearch.WordTrace tailWord_1627454 prefixEnd_1627454 557110763388253874960321 := by
  unfold tailWord_1627454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7419765480752447482477177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39572082564013053239878277 7419765480752447482477177)
  ·
    refine ⟨5564824110564335611857883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7419765480752447482477177 5564824110564335611857883)
    ·
      refine ⟨8347236165846503417786825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5564824110564335611857883 8347236165846503417786825)
      ·
        refine ⟨6260427124384877563340119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8347236165846503417786825 6260427124384877563340119)
        ·
          refine ⟨9390640686577316345010179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6260427124384877563340119 9390640686577316345010179)
          ·
            refine ⟨14085961029865974517515269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9390640686577316345010179 14085961029865974517515269)
            ·
              refine ⟨2641117693099870222034113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14085961029865974517515269 2641117693099870222034113)
              ·
                refine ⟨1980838269824902666525585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2641117693099870222034113 1980838269824902666525585)
                ·
                  refine ⟨1485628702368676999894189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1980838269824902666525585 1485628702368676999894189)
                  ·
                    refine ⟨557110763388253874960321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1485628702368676999894189 557110763388253874960321)
                    ·
                      rfl

theorem cell22_1627454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_1627454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627454 prefixEnd_1627454 := by exact prefixLift 1627454
  have htrace : WordTrace (prefixWord ++ tailWord_1627454) baseStart_1627454 baseEnd_1627454 := by
    simpa [prefixWord, tailWord_1627454, baseEnd_1627454] using wordTrace_append hprefix tailTrace_1627454
  have hstable : (prefixWord ++ tailWord_1627454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627454).length < 2 ^ (prefixWord ++ tailWord_1627454).sum := by decide
  have hdescent : baseEnd_1627454 < baseStart_1627454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627525 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_1627525 : Nat := 118140960795 + 1627525 * 2 ^ 59
def prefixEnd_1627525 : Nat := 4983230072969 + 3 ^ 40 * 1627525 * 2
def baseEnd_1627525 : Nat := 557135068139233356435103

theorem tailTrace_1627525 : CollatzResearch.WordTrace tailWord_1627525 prefixEnd_1627525 557135068139233356435103 := by
  unfold tailWord_1627525
  simp only [CollatzResearch.WordTrace]
  refine ⟨59360713428762358985652029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39573808952508239323768019 59360713428762358985652029)
  ·
    refine ⟨22260267535785884619619511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59360713428762358985652029 22260267535785884619619511)
    ·
      refine ⟨33390401303678826929429267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22260267535785884619619511 33390401303678826929429267)
      ·
        refine ⟨50085601955518240394143901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33390401303678826929429267 50085601955518240394143901)
        ·
          refine ⟨18782100733319340147803963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50085601955518240394143901 18782100733319340147803963)
          ·
            refine ⟨28173151099979010221705945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18782100733319340147803963 28173151099979010221705945)
            ·
              refine ⟨21129863324984257666279459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28173151099979010221705945 21129863324984257666279459)
              ·
                refine ⟨31694794987476386499419189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21129863324984257666279459 31694794987476386499419189)
                ·
                  refine ⟨2971387030075911234320549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31694794987476386499419189 2971387030075911234320549)
                  ·
                    refine ⟨557135068139233356435103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2971387030075911234320549 557135068139233356435103)
                    ·
                      rfl

theorem cell22_1627525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_1627525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627525 prefixEnd_1627525 := by exact prefixLift 1627525
  have htrace : WordTrace (prefixWord ++ tailWord_1627525) baseStart_1627525 baseEnd_1627525 := by
    simpa [prefixWord, tailWord_1627525, baseEnd_1627525] using wordTrace_append hprefix tailTrace_1627525
  have hstable : (prefixWord ++ tailWord_1627525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627525).length < 2 ^ (prefixWord ++ tailWord_1627525).sum := by decide
  have hdescent : baseEnd_1627525 < baseStart_1627525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627529 : List Nat := [1, 2, 1, 1, 7, 1, 3, 1, 5]
def baseStart_1627529 : Nat := 118140960795 + 1627529 * 2 ^ 59
def prefixEnd_1627529 : Nat := 4983230072969 + 3 ^ 40 * 1627529 * 2
def baseEnd_1627529 : Nat := 185712145806992893111697

theorem tailTrace_1627529 : CollatzResearch.WordTrace tailWord_1627529 prefixEnd_1627529 185712145806992893111697 := by
  unfold tailWord_1627529
  simp only [CollatzResearch.WordTrace]
  refine ⟨59360859320747867668797641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39573906213831911779198427 59360859320747867668797641)
  ·
    refine ⟨44520644490560900751598231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59360859320747867668797641 44520644490560900751598231)
    ·
      refine ⟨66780966735841351127397347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44520644490560900751598231 66780966735841351127397347)
      ·
        refine ⟨100171450103762026691096021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66780966735841351127397347 100171450103762026691096021)
        ·
          refine ⟨2347768361806922500572563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 100171450103762026691096021 2347768361806922500572563)
          ·
            refine ⟨3521652542710383750858845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347768361806922500572563 3521652542710383750858845)
            ·
              refine ⟨1320619703516393906572067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3521652542710383750858845 1320619703516393906572067)
              ·
                refine ⟨1980929555274590859858101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320619703516393906572067 1980929555274590859858101)
                ·
                  refine ⟨185712145806992893111697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1980929555274590859858101 185712145806992893111697)
                  ·
                    rfl

theorem cell22_1627529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 5].length) (baseStart_1627529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627529 prefixEnd_1627529 := by exact prefixLift 1627529
  have htrace : WordTrace (prefixWord ++ tailWord_1627529) baseStart_1627529 baseEnd_1627529 := by
    simpa [prefixWord, tailWord_1627529, baseEnd_1627529] using wordTrace_append hprefix tailTrace_1627529
  have hstable : (prefixWord ++ tailWord_1627529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627529).length < 2 ^ (prefixWord ++ tailWord_1627529).sum := by decide
  have hdescent : baseEnd_1627529 < baseStart_1627529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627550 : List Nat := [4, 3, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_1627550 : Nat := 118140960795 + 1627550 * 2 ^ 59
def prefixEnd_1627550 : Nat := 4983230072969 + 3 ^ 40 * 1627550 * 2
def baseEnd_1627550 : Nat := 557143626150141624560027

theorem tailTrace_1627550 : CollatzResearch.WordTrace tailWord_1627550 prefixEnd_1627550 557143626150141624560027 := by
  unfold tailWord_1627550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7420203156708973531914013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39574416835781192170208069 7420203156708973531914013)
  ·
    refine ⟨2782576183765865074467755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7420203156708973531914013 2782576183765865074467755)
    ·
      refine ⟨4173864275648797611701633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2782576183765865074467755 4173864275648797611701633)
      ·
        refine ⟨3130398206736598208776225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4173864275648797611701633 3130398206736598208776225)
        ·
          refine ⟨2347798655052448656582169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3130398206736598208776225 2347798655052448656582169)
          ·
            refine ⟨1760848991289336492436627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2347798655052448656582169 1760848991289336492436627)
            ·
              refine ⟨2641273486934004738654941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760848991289336492436627 2641273486934004738654941)
              ·
                refine ⟨990477557600251776995603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2641273486934004738654941 990477557600251776995603)
                ·
                  refine ⟨1485716336400377665493405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 990477557600251776995603 1485716336400377665493405)
                  ·
                    refine ⟨557143626150141624560027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1485716336400377665493405 557143626150141624560027)
                    ·
                      rfl

theorem cell22_1627550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_1627550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627550 prefixEnd_1627550 := by exact prefixLift 1627550
  have htrace : WordTrace (prefixWord ++ tailWord_1627550) baseStart_1627550 baseEnd_1627550 := by
    simpa [prefixWord, tailWord_1627550, baseEnd_1627550] using wordTrace_append hprefix tailTrace_1627550
  have hstable : (prefixWord ++ tailWord_1627550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627550).length < 2 ^ (prefixWord ++ tailWord_1627550).sum := by decide
  have hdescent : baseEnd_1627550 < baseStart_1627550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627555 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 3, 5]
def baseStart_1627555 : Nat := 118140960795 + 1627555 * 2 ^ 59
def prefixEnd_1627555 : Nat := 4983230072969 + 3 ^ 40 * 1627555 * 2
def baseEnd_1627555 : Nat := 557145337752323278185011

theorem tailTrace_1627555 : CollatzResearch.WordTrace tailWord_1627555 prefixEnd_1627555 557145337752323278185011 := by
  unfold tailWord_1627555
  simp only [CollatzResearch.WordTrace]
  refine ⟨59361807618653674109244119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39574538412435782739496079 59361807618653674109244119)
  ·
    refine ⟨89042711427980511163866179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59361807618653674109244119 89042711427980511163866179)
    ·
      refine ⟨133564067141970766745799269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89042711427980511163866179 133564067141970766745799269)
      ·
        refine ⟨25043262589119518764837363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133564067141970766745799269 25043262589119518764837363)
        ·
          refine ⟨37564893883679278147256045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25043262589119518764837363 37564893883679278147256045)
          ·
            refine ⟨14086835206379729305221017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37564893883679278147256045 14086835206379729305221017)
            ·
              refine ⟨10565126404784796978915763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14086835206379729305221017 10565126404784796978915763)
              ·
                refine ⟨15847689607177195468373645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10565126404784796978915763 15847689607177195468373645)
                ·
                  refine ⟨5942883602691448300640117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15847689607177195468373645 5942883602691448300640117)
                  ·
                    refine ⟨557145337752323278185011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5942883602691448300640117 557145337752323278185011)
                    ·
                      rfl

theorem cell22_1627555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 5].length) (baseStart_1627555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627555 prefixEnd_1627555 := by exact prefixLift 1627555
  have htrace : WordTrace (prefixWord ++ tailWord_1627555) baseStart_1627555 baseEnd_1627555 := by
    simpa [prefixWord, tailWord_1627555, baseEnd_1627555] using wordTrace_append hprefix tailTrace_1627555
  have hstable : (prefixWord ++ tailWord_1627555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627555).length < 2 ^ (prefixWord ++ tailWord_1627555).sum := by decide
  have hdescent : baseEnd_1627555 < baseStart_1627555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627557 : List Nat := [1, 3, 1, 2, 1, 1, 2, 7, 4]
def baseStart_1627557 : Nat := 118140960795 + 1627557 * 2 ^ 59
def prefixEnd_1627557 : Nat := 4983230072969 + 3 ^ 40 * 1627557 * 2
def baseEnd_1627557 : Nat := 185715340797731979878335

theorem tailTrace_1627557 : CollatzResearch.WordTrace tailWord_1627557 prefixEnd_1627557 185715340797731979878335 := by
  unfold tailWord_1627557
  simp only [CollatzResearch.WordTrace]
  refine ⟨59361880564646428450816925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39574587043097618967211283 59361880564646428450816925)
  ·
    refine ⟨22260705211742410669056347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59361880564646428450816925 22260705211742410669056347)
    ·
      refine ⟨33391057817613616003584521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22260705211742410669056347 33391057817613616003584521)
      ·
        refine ⟨25043293363210212002688391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33391057817613616003584521 25043293363210212002688391)
        ·
          refine ⟨37564940044815318004032587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25043293363210212002688391 37564940044815318004032587)
          ·
            refine ⟨56347410067222977006048881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37564940044815318004032587 56347410067222977006048881)
            ·
              refine ⟨42260557550417232754536661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56347410067222977006048881 42260557550417232754536661)
              ·
                refine ⟨990481817587903892684453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42260557550417232754536661 990481817587903892684453)
                ·
                  refine ⟨185715340797731979878335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 990481817587903892684453 185715340797731979878335)
                  ·
                    rfl

theorem cell22_1627557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_1627557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627557 prefixEnd_1627557 := by exact prefixLift 1627557
  have htrace : WordTrace (prefixWord ++ tailWord_1627557) baseStart_1627557 baseEnd_1627557 := by
    simpa [prefixWord, tailWord_1627557, baseEnd_1627557] using wordTrace_append hprefix tailTrace_1627557
  have hstable : (prefixWord ++ tailWord_1627557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627557).length < 2 ^ (prefixWord ++ tailWord_1627557).sum := by decide
  have hdescent : baseEnd_1627557 < baseStart_1627557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627570 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_1627570 : Nat := 118140960795 + 1627570 * 2 ^ 59
def prefixEnd_1627570 : Nat := 4983230072969 + 3 ^ 40 * 1627570 * 2
def baseEnd_1627570 : Nat := 557150472558868239059965

theorem tailTrace_1627570 : CollatzResearch.WordTrace tailWord_1627570 prefixEnd_1627570 557150472558868239059965 := by
  unfold tailWord_1627570
  simp only [CollatzResearch.WordTrace]
  refine ⟨14840588678399832917760041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39574903142399554447360109 14840588678399832917760041)
  ·
    refine ⟨11130441508799874688320031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14840588678399832917760041 11130441508799874688320031)
    ·
      refine ⟨16695662263199812032480047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11130441508799874688320031 16695662263199812032480047)
      ·
        refine ⟨25043493394799718048720071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16695662263199812032480047 25043493394799718048720071)
        ·
          refine ⟨37565240092199577073080107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25043493394799718048720071 37565240092199577073080107)
          ·
            refine ⟨56347860138299365609620161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37565240092199577073080107 56347860138299365609620161)
            ·
              refine ⟨42260895103724524207215121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56347860138299365609620161 42260895103724524207215121)
              ·
                refine ⟨31695671327793393155411341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42260895103724524207215121 31695671327793393155411341)
                ·
                  refine ⟨11885876747922522433279253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31695671327793393155411341 11885876747922522433279253)
                  ·
                    refine ⟨557150472558868239059965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11885876747922522433279253 557150472558868239059965)
                    ·
                      rfl

theorem cell22_1627570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_1627570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627570 prefixEnd_1627570 := by exact prefixLift 1627570
  have htrace : WordTrace (prefixWord ++ tailWord_1627570) baseStart_1627570 baseEnd_1627570 := by
    simpa [prefixWord, tailWord_1627570, baseEnd_1627570] using wordTrace_append hprefix tailTrace_1627570
  have hstable : (prefixWord ++ tailWord_1627570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627570).length < 2 ^ (prefixWord ++ tailWord_1627570).sum := by decide
  have hdescent : baseEnd_1627570 < baseStart_1627570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627722 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_1627722 : Nat := 118140960795 + 1627722 * 2 ^ 59
def prefixEnd_1627722 : Nat := 4983230072969 + 3 ^ 40 * 1627722 * 2
def baseEnd_1627722 : Nat := 557202505265190509259499

theorem tailTrace_1627722 : CollatzResearch.WordTrace tailWord_1627722 prefixEnd_1627722 557202505265190509259499 := by
  unfold tailWord_1627722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14841974652262165407643355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39578599072699107753715613 14841974652262165407643355)
  ·
    refine ⟨22262961978393248111465033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14841974652262165407643355 22262961978393248111465033)
    ·
      refine ⟨16697221483794936083598775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22262961978393248111465033 16697221483794936083598775)
      ·
        refine ⟨25045832225692404125398163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16697221483794936083598775 25045832225692404125398163)
        ·
          refine ⟨37568748338538606188097245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25045832225692404125398163 37568748338538606188097245)
          ·
            refine ⟨14088280626951977320536467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37568748338538606188097245 14088280626951977320536467)
            ·
              refine ⟨21132420940427965980804701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14088280626951977320536467 21132420940427965980804701)
              ·
                refine ⟨7924657852660487242801763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21132420940427965980804701 7924657852660487242801763)
                ·
                  refine ⟨11886986778990730864202645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7924657852660487242801763 11886986778990730864202645)
                  ·
                    refine ⟨557202505265190509259499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11886986778990730864202645 557202505265190509259499)
                    ·
                      rfl

theorem cell22_1627722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_1627722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627722 prefixEnd_1627722 := by exact prefixLift 1627722
  have htrace : WordTrace (prefixWord ++ tailWord_1627722) baseStart_1627722 baseEnd_1627722 := by
    simpa [prefixWord, tailWord_1627722, baseEnd_1627722] using wordTrace_append hprefix tailTrace_1627722
  have hstable : (prefixWord ++ tailWord_1627722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627722).length < 2 ^ (prefixWord ++ tailWord_1627722).sum := by decide
  have hdescent : baseEnd_1627722 < baseStart_1627722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627724 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 4, 3]
def baseStart_1627724 : Nat := 118140960795 + 1627724 * 2 ^ 59
def prefixEnd_1627724 : Nat := 4983230072969 + 3 ^ 40 * 1627724 * 2
def baseEnd_1627724 : Nat := 557203189906063170709493

theorem tailTrace_1627724 : CollatzResearch.WordTrace tailWord_1627724 prefixEnd_1627724 557203189906063170709493 := by
  unfold tailWord_1627724
  simp only [CollatzResearch.WordTrace]
  refine ⟨29683985777520707986073113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39578647703360943981430817 29683985777520707986073113)
  ·
    refine ⟨22262989333140530989554835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29683985777520707986073113 22262989333140530989554835)
    ·
      refine ⟨33394483999710796484332253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22262989333140530989554835 33394483999710796484332253)
      ·
        refine ⟨12522931499891548681624595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33394483999710796484332253 12522931499891548681624595)
        ·
          refine ⟨18784397249837323022436893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12522931499891548681624595 18784397249837323022436893)
          ·
            refine ⟨7044148968688996133413835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18784397249837323022436893 7044148968688996133413835)
            ·
              refine ⟨10566223453033494200120753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7044148968688996133413835 10566223453033494200120753)
              ·
                refine ⟨7924667589775120650090565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10566223453033494200120753 7924667589775120650090565)
                ·
                  refine ⟨1485875173082835121891981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7924667589775120650090565 1485875173082835121891981)
                  ·
                    refine ⟨557203189906063170709493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1485875173082835121891981 557203189906063170709493)
                    ·
                      rfl

theorem cell22_1627724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_1627724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627724 prefixEnd_1627724 := by exact prefixLift 1627724
  have htrace : WordTrace (prefixWord ++ tailWord_1627724) baseStart_1627724 baseEnd_1627724 := by
    simpa [prefixWord, tailWord_1627724, baseEnd_1627724] using wordTrace_append hprefix tailTrace_1627724
  have hstable : (prefixWord ++ tailWord_1627724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627724).length < 2 ^ (prefixWord ++ tailWord_1627724).sum := by decide
  have hdescent : baseEnd_1627724 < baseStart_1627724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627754 : List Nat := [3, 1, 3, 2, 1, 3, 2, 7]
def baseStart_1627754 : Nat := 118140960795 + 1627754 * 2 ^ 59
def prefixEnd_1627754 : Nat := 4983230072969 + 3 ^ 40 * 1627754 * 2
def baseEnd_1627754 : Nat := 61912606613239232495489

theorem tailTrace_1627754 : CollatzResearch.WordTrace tailWord_1627754 prefixEnd_1627754 61912606613239232495489 := by
  unfold tailWord_1627754
  simp only [CollatzResearch.WordTrace]
  refine ⟨14842266436233182773934579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39579377163288487397158877 14842266436233182773934579)
  ·
    refine ⟨22263399654349774160901869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14842266436233182773934579 22263399654349774160901869)
    ·
      refine ⟨8348774870381165310338201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22263399654349774160901869 8348774870381165310338201)
      ·
        refine ⟨6261581152785873982753651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8348774870381165310338201 6261581152785873982753651)
        ·
          refine ⟨9392371729178810974130477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6261581152785873982753651 9392371729178810974130477)
          ·
            refine ⟨3522139398442054115298929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9392371729178810974130477 3522139398442054115298929)
            ·
              refine ⟨2641604548831540586474197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3522139398442054115298929 2641604548831540586474197)
              ·
                refine ⟨61912606613239232495489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2641604548831540586474197 61912606613239232495489)
                ·
                  rfl

theorem cell22_1627754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_1627754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627754 prefixEnd_1627754 := by exact prefixLift 1627754
  have htrace : WordTrace (prefixWord ++ tailWord_1627754) baseStart_1627754 baseEnd_1627754 := by
    simpa [prefixWord, tailWord_1627754, baseEnd_1627754] using wordTrace_append hprefix tailTrace_1627754
  have hstable : (prefixWord ++ tailWord_1627754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627754).length < 2 ^ (prefixWord ++ tailWord_1627754).sum := by decide
  have hdescent : baseEnd_1627754 < baseStart_1627754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627758 : List Nat := [4, 1, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_1627758 : Nat := 118140960795 + 1627758 * 2 ^ 59
def prefixEnd_1627758 : Nat := 4983230072969 + 3 ^ 40 * 1627758 * 2
def baseEnd_1627758 : Nat := 557214828800898415359389

theorem tailTrace_1627758 : CollatzResearch.WordTrace tailWord_1627758 prefixEnd_1627758 557214828800898415359389 := by
  unfold tailWord_1627758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7421151454614779972360491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39579474424612159852589285 7421151454614779972360491)
  ·
    refine ⟨11131727181922169958540737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7421151454614779972360491 11131727181922169958540737)
    ·
      refine ⟨8348795386441627468905553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11131727181922169958540737 8348795386441627468905553)
      ·
        refine ⟨6261596539831220601679165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8348795386441627468905553 6261596539831220601679165)
        ·
          refine ⟨2348098702436707725629687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6261596539831220601679165 2348098702436707725629687)
          ·
            refine ⟨3522148053655061588444531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2348098702436707725629687 3522148053655061588444531)
            ·
              refine ⟨5283222080482592382666797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3522148053655061588444531 5283222080482592382666797)
              ·
                refine ⟨1981208280180972143500049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5283222080482592382666797 1981208280180972143500049)
                ·
                  refine ⟨1485906210135729107625037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1981208280180972143500049 1485906210135729107625037)
                  ·
                    refine ⟨557214828800898415359389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1485906210135729107625037 557214828800898415359389)
                    ·
                      rfl

theorem cell22_1627758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_1627758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627758 prefixEnd_1627758 := by exact prefixLift 1627758
  have htrace : WordTrace (prefixWord ++ tailWord_1627758) baseStart_1627758 baseEnd_1627758 := by
    simpa [prefixWord, tailWord_1627758, baseEnd_1627758] using wordTrace_append hprefix tailTrace_1627758
  have hstable : (prefixWord ++ tailWord_1627758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627758).length < 2 ^ (prefixWord ++ tailWord_1627758).sum := by decide
  have hdescent : baseEnd_1627758 < baseStart_1627758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627769 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 5, 3]
def baseStart_1627769 : Nat := 118140960795 + 1627769 * 2 ^ 59
def prefixEnd_1627769 : Nat := 4983230072969 + 3 ^ 40 * 1627769 * 2
def baseEnd_1627769 : Nat := 557218594325698053334355

theorem tailTrace_1627769 : CollatzResearch.WordTrace tailWord_1627769 prefixEnd_1627769 557218594325698053334355 := by
  unfold tailWord_1627769
  simp only [CollatzResearch.WordTrace]
  refine ⟨59369612839878388657534361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39579741893252259105022907 59369612839878388657534361)
  ·
    refine ⟨44527209629908791493150771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59369612839878388657534361 44527209629908791493150771)
    ·
      refine ⟨66790814444863187239726157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44527209629908791493150771 66790814444863187239726157)
      ·
        refine ⟨25046555416823695214897309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66790814444863187239726157 25046555416823695214897309)
        ·
          refine ⟨9392458281308885705586491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25046555416823695214897309 9392458281308885705586491)
          ·
            refine ⟨14088687421963328558379737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9392458281308885705586491 14088687421963328558379737)
            ·
              refine ⟨10566515566472496418784803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14088687421963328558379737 10566515566472496418784803)
              ·
                refine ⟨15849773349708744628177205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10566515566472496418784803 15849773349708744628177205)
                ·
                  refine ⟨1485916251535194808891613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15849773349708744628177205 1485916251535194808891613)
                  ·
                    refine ⟨557218594325698053334355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1485916251535194808891613 557218594325698053334355)
                    ·
                      rfl

theorem cell22_1627769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 3].length) (baseStart_1627769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627769 prefixEnd_1627769 := by exact prefixLift 1627769
  have htrace : WordTrace (prefixWord ++ tailWord_1627769) baseStart_1627769 baseEnd_1627769 := by
    simpa [prefixWord, tailWord_1627769, baseEnd_1627769] using wordTrace_append hprefix tailTrace_1627769
  have hstable : (prefixWord ++ tailWord_1627769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627769).length < 2 ^ (prefixWord ++ tailWord_1627769).sum := by decide
  have hdescent : baseEnd_1627769 < baseStart_1627769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627797 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_1627797 : Nat := 118140960795 + 1627797 * 2 ^ 59
def prefixEnd_1627797 : Nat := 4983230072969 + 3 ^ 40 * 1627797 * 2
def baseEnd_1627797 : Nat := 557228179297915313634269

theorem tailTrace_1627797 : CollatzResearch.WordTrace tailWord_1627797 prefixEnd_1627797 557228179297915313634269 := by
  unfold tailWord_1627797
  simp only [CollatzResearch.WordTrace]
  refine ⟨59370634083776949439553645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39580422722517966293035763 59370634083776949439553645)
  ·
    refine ⟨22263987781416356039832617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59370634083776949439553645 22263987781416356039832617)
    ·
      refine ⟨16697990836062267029874463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22263987781416356039832617 16697990836062267029874463)
      ·
        refine ⟨25046986254093400544811695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16697990836062267029874463 25046986254093400544811695)
        ·
          refine ⟨37570479381140100817217543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25046986254093400544811695 37570479381140100817217543)
          ·
            refine ⟨56355719071710151225826315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37570479381140100817217543 56355719071710151225826315)
            ·
              refine ⟨84533578607565226838739473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56355719071710151225826315 84533578607565226838739473)
              ·
                refine ⟨63400183955673920129054605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84533578607565226838739473 63400183955673920129054605)
                ·
                  refine ⟨23775068983377720048395477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63400183955673920129054605 23775068983377720048395477)
                  ·
                    refine ⟨557228179297915313634269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23775068983377720048395477 557228179297915313634269)
                    ·
                      rfl

theorem cell22_1627797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_1627797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627797 prefixEnd_1627797 := by exact prefixLift 1627797
  have htrace : WordTrace (prefixWord ++ tailWord_1627797) baseStart_1627797 baseEnd_1627797 := by
    simpa [prefixWord, tailWord_1627797, baseEnd_1627797] using wordTrace_append hprefix tailTrace_1627797
  have hstable : (prefixWord ++ tailWord_1627797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627797).length < 2 ^ (prefixWord ++ tailWord_1627797).sum := by decide
  have hdescent : baseEnd_1627797 < baseStart_1627797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627799 : List Nat := [1, 1, 3, 3, 2, 2, 1, 4, 5]
def baseStart_1627799 : Nat := 118140960795 + 1627799 * 2 ^ 59
def prefixEnd_1627799 : Nat := 4983230072969 + 3 ^ 40 * 1627799 * 2
def baseEnd_1627799 : Nat := 185742954646262658361421

theorem tailTrace_1627799 : CollatzResearch.WordTrace tailWord_1627799 prefixEnd_1627799 185742954646262658361421 := by
  unfold tailWord_1627799
  simp only [CollatzResearch.WordTrace]
  refine ⟨59370707029769703781126451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39580471353179802520750967 59370707029769703781126451)
  ·
    refine ⟨89056060544654555671689677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59370707029769703781126451 89056060544654555671689677)
    ·
      refine ⟨33396022704245458376883629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89056060544654555671689677 33396022704245458376883629)
      ·
        refine ⟨12523508514092046891331361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33396022704245458376883629 12523508514092046891331361)
        ·
          refine ⟨9392631385569035168498521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12523508514092046891331361 9392631385569035168498521)
          ·
            refine ⟨7044473539176776376373891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9392631385569035168498521 7044473539176776376373891)
            ·
              refine ⟨10566710308765164564560837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7044473539176776376373891 10566710308765164564560837)
              ·
                refine ⟨1981258182893468355855157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10566710308765164564560837 1981258182893468355855157)
                ·
                  refine ⟨185742954646262658361421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1981258182893468355855157 185742954646262658361421)
                  ·
                    rfl

theorem cell22_1627799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 5].length) (baseStart_1627799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627799 prefixEnd_1627799 := by exact prefixLift 1627799
  have htrace : WordTrace (prefixWord ++ tailWord_1627799) baseStart_1627799 baseEnd_1627799 := by
    simpa [prefixWord, tailWord_1627799, baseEnd_1627799] using wordTrace_append hprefix tailTrace_1627799
  have hstable : (prefixWord ++ tailWord_1627799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627799).length < 2 ^ (prefixWord ++ tailWord_1627799).sum := by decide
  have hdescent : baseEnd_1627799 < baseStart_1627799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627844 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 8]
def baseStart_1627844 : Nat := 118140960795 + 1627844 * 2 ^ 59
def prefixEnd_1627844 : Nat := 4983230072969 + 3 ^ 40 * 1627844 * 2
def baseEnd_1627844 : Nat := 185748089452807619236375

theorem tailTrace_1627844 : CollatzResearch.WordTrace tailWord_1627844 prefixEnd_1627844 185748089452807619236375 := by
  unfold tailWord_1627844
  simp only [CollatzResearch.WordTrace]
  refine ⟨29686174157303338233257293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39581565543071117644343057 29686174157303338233257293)
  ·
    refine ⟨11132315308988751837471485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29686174157303338233257293 11132315308988751837471485)
    ·
      refine ⟨4174618240870781939051807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11132315308988751837471485 4174618240870781939051807)
      ·
        refine ⟨6261927361306172908577711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4174618240870781939051807 6261927361306172908577711)
        ·
          refine ⟨9392891041959259362866567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6261927361306172908577711 9392891041959259362866567)
          ·
            refine ⟨14089336562938889044299851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9392891041959259362866567 14089336562938889044299851)
            ·
              refine ⟨21134004844408333566449777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14089336562938889044299851 21134004844408333566449777)
              ·
                refine ⟨15850503633306250174837333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21134004844408333566449777 15850503633306250174837333)
                ·
                  refine ⟨185748089452807619236375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15850503633306250174837333 185748089452807619236375)
                  ·
                    rfl

theorem cell22_1627844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_1627844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627844 prefixEnd_1627844 := by exact prefixLift 1627844
  have htrace : WordTrace (prefixWord ++ tailWord_1627844) baseStart_1627844 baseEnd_1627844 := by
    simpa [prefixWord, tailWord_1627844, baseEnd_1627844] using wordTrace_append hprefix tailTrace_1627844
  have hstable : (prefixWord ++ tailWord_1627844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627844).length < 2 ^ (prefixWord ++ tailWord_1627844).sum := by decide
  have hdescent : baseEnd_1627844 < baseStart_1627844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627889 : List Nat := [1, 2, 2, 2, 2, 4, 1, 8]
def baseStart_1627889 : Nat := 118140960795 + 1627889 * 2 ^ 59
def prefixEnd_1627889 : Nat := 4983230072969 + 3 ^ 40 * 1627889 * 2
def baseEnd_1627889 : Nat := 61917741419784193370443

theorem tailTrace_1627889 : CollatzResearch.WordTrace tailWord_1627889 prefixEnd_1627889 61917741419784193370443 := by
  unfold tailWord_1627889
  simp only [CollatzResearch.WordTrace]
  refine ⟨59373989599443649151902721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39582659732962432767935147 59373989599443649151902721)
  ·
    refine ⟨44530492199582736863927041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59373989599443649151902721 44530492199582736863927041)
    ·
      refine ⟨33397869149687052647945281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44530492199582736863927041 33397869149687052647945281)
      ·
        refine ⟨25048401862265289485958961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33397869149687052647945281 25048401862265289485958961)
        ·
          refine ⟨18786301396698967114469221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25048401862265289485958961 18786301396698967114469221)
          ·
            refine ⟨3522431511881056333962979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18786301396698967114469221 3522431511881056333962979)
            ·
              refine ⟨5283647267821584500944469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3522431511881056333962979 5283647267821584500944469)
              ·
                refine ⟨61917741419784193370443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5283647267821584500944469 61917741419784193370443)
                ·
                  rfl

theorem cell22_1627889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 8].length) (baseStart_1627889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1627889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1627889 prefixEnd_1627889 := by exact prefixLift 1627889
  have htrace : WordTrace (prefixWord ++ tailWord_1627889) baseStart_1627889 baseEnd_1627889 := by
    simpa [prefixWord, tailWord_1627889, baseEnd_1627889] using wordTrace_append hprefix tailTrace_1627889
  have hstable : (prefixWord ++ tailWord_1627889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627889).length < 2 ^ (prefixWord ++ tailWord_1627889).sum := by decide
  have hdescent : baseEnd_1627889 < baseStart_1627889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628011 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 4, 3]
def baseStart_1628011 : Nat := 118140960795 + 1628011 * 2 ^ 59
def prefixEnd_1628011 : Nat := 4983230072969 + 3 ^ 40 * 1628011 * 2
def baseEnd_1628011 : Nat := 557301435871290088783613

theorem tailTrace_1628011 : CollatzResearch.WordTrace tailWord_1628011 prefixEnd_1628011 557301435871290088783613 := by
  unfold tailWord_1628011
  simp only [CollatzResearch.WordTrace]
  refine ⟨59378439305001663987843887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39585626203334442658562591 59378439305001663987843887)
  ·
    refine ⟨89067658957502495981765831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59378439305001663987843887 89067658957502495981765831)
    ·
      refine ⟨133601488436253743972648747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89067658957502495981765831 133601488436253743972648747)
      ·
        refine ⟨200402232654380615958973121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133601488436253743972648747 200402232654380615958973121)
        ·
          refine ⟨150301674490785461969229841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200402232654380615958973121 150301674490785461969229841)
          ·
            refine ⟨112726255868089096476922381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150301674490785461969229841 112726255868089096476922381)
            ·
              refine ⟨42272345950533411178845893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112726255868089096476922381 42272345950533411178845893)
              ·
                refine ⟨7926064865725014596033605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42272345950533411178845893 7926064865725014596033605)
                ·
                  refine ⟨1486137162323440236756301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7926064865725014596033605 1486137162323440236756301)
                  ·
                    refine ⟨557301435871290088783613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1486137162323440236756301 557301435871290088783613)
                    ·
                      rfl

theorem cell22_1628011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 3].length) (baseStart_1628011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628011 prefixEnd_1628011 := by exact prefixLift 1628011
  have htrace : WordTrace (prefixWord ++ tailWord_1628011) baseStart_1628011 baseEnd_1628011 := by
    simpa [prefixWord, tailWord_1628011, baseEnd_1628011] using wordTrace_append hprefix tailTrace_1628011
  have hstable : (prefixWord ++ tailWord_1628011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628011).length < 2 ^ (prefixWord ++ tailWord_1628011).sum := by decide
  have hdescent : baseEnd_1628011 < baseStart_1628011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628013 : List Nat := [1, 5, 1, 1, 1, 1, 3, 5, 4]
def baseStart_1628013 : Nat := 118140960795 + 1628013 * 2 ^ 59
def prefixEnd_1628013 : Nat := 4983230072969 + 3 ^ 40 * 1628013 * 2
def baseEnd_1628013 : Nat := 185767373504054250077869

theorem tailTrace_1628013 : CollatzResearch.WordTrace tailWord_1628013 prefixEnd_1628013 185767373504054250077869 := by
  unfold tailWord_1628013
  simp only [CollatzResearch.WordTrace]
  refine ⟨59378512250994418329416693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39585674833996278886277795 59378512250994418329416693)
  ·
    refine ⟨5566735523530726718382815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59378512250994418329416693 5566735523530726718382815)
    ·
      refine ⟨8350103285296090077574223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5566735523530726718382815 8350103285296090077574223)
      ·
        refine ⟨12525154927944135116361335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8350103285296090077574223 12525154927944135116361335)
        ·
          refine ⟨18787732391916202674542003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12525154927944135116361335 18787732391916202674542003)
          ·
            refine ⟨28181598587874304011813005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18787732391916202674542003 28181598587874304011813005)
            ·
              refine ⟨10568099470452864004429877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28181598587874304011813005 10568099470452864004429877)
              ·
                refine ⟨990759325354956000415301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10568099470452864004429877 990759325354956000415301)
                ·
                  refine ⟨185767373504054250077869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 990759325354956000415301 185767373504054250077869)
                  ·
                    rfl

theorem cell22_1628013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_1628013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628013 prefixEnd_1628013 := by exact prefixLift 1628013
  have htrace : WordTrace (prefixWord ++ tailWord_1628013) baseStart_1628013 baseEnd_1628013 := by
    simpa [prefixWord, tailWord_1628013, baseEnd_1628013] using wordTrace_append hprefix tailTrace_1628013
  have hstable : (prefixWord ++ tailWord_1628013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628013).length < 2 ^ (prefixWord ++ tailWord_1628013).sum := by decide
  have hdescent : baseEnd_1628013 < baseStart_1628013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628026 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_1628026 : Nat := 118140960795 + 1628026 * 2 ^ 59
def prefixEnd_1628026 : Nat := 4983230072969 + 3 ^ 40 * 1628026 * 2
def baseEnd_1628026 : Nat := 557306570677835049658567

theorem tailTrace_1628026 : CollatzResearch.WordTrace tailWord_1628026 prefixEnd_1628026 557306570677835049658567 := by
  unfold tailWord_1628026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14844746599986830387409983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39585990933298214366426621 14844746599986830387409983)
  ·
    refine ⟨22267119899980245581114975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14844746599986830387409983 22267119899980245581114975)
    ·
      refine ⟨33400679849970368371672463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22267119899980245581114975 33400679849970368371672463)
      ·
        refine ⟨50101019774955552557508695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33400679849970368371672463 50101019774955552557508695)
        ·
          refine ⟨75151529662433328836263043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50101019774955552557508695 75151529662433328836263043)
          ·
            refine ⟨112727294493649993254394565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75151529662433328836263043 112727294493649993254394565)
            ·
              refine ⟨21136367717559373735198981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112727294493649993254394565 21136367717559373735198981)
              ·
                refine ⟨3963068947042382575349809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21136367717559373735198981 3963068947042382575349809)
                ·
                  refine ⟨2972301710281786931512357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3963068947042382575349809 2972301710281786931512357)
                  ·
                    refine ⟨557306570677835049658567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2972301710281786931512357 557306570677835049658567)
                    ·
                      rfl

theorem cell22_1628026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_1628026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628026 prefixEnd_1628026 := by exact prefixLift 1628026
  have htrace : WordTrace (prefixWord ++ tailWord_1628026) baseStart_1628026 baseEnd_1628026 := by
    simpa [prefixWord, tailWord_1628026, baseEnd_1628026] using wordTrace_append hprefix tailTrace_1628026
  have hstable : (prefixWord ++ tailWord_1628026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628026).length < 2 ^ (prefixWord ++ tailWord_1628026).sum := by decide
  have hdescent : baseEnd_1628026 < baseStart_1628026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628030 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1628030 : Nat := 118140960795 + 1628030 * 2 ^ 59
def prefixEnd_1628030 : Nat := 4983230072969 + 3 ^ 40 * 1628030 * 2
def baseEnd_1628030 : Nat := 185769313319860124186185

theorem tailTrace_1628030 : CollatzResearch.WordTrace tailWord_1628030 prefixEnd_1628030 185769313319860124186185 := by
  unfold tailWord_1628030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7422391536491603779098193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39586088194621886821857029 7422391536491603779098193)
  ·
    refine ⟨5566793652368702834323645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7422391536491603779098193 5566793652368702834323645)
    ·
      refine ⟨2087547619638263562871367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5566793652368702834323645 2087547619638263562871367)
      ·
        refine ⟨3131321429457395344307051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087547619638263562871367 3131321429457395344307051)
        ·
          refine ⟨4696982144186093016460577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3131321429457395344307051 4696982144186093016460577)
          ·
            refine ⟨3522736608139569762345433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4696982144186093016460577 3522736608139569762345433)
            ·
              refine ⟨2642052456104677321759075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3522736608139569762345433 2642052456104677321759075)
              ·
                refine ⟨3963078684157015982638613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642052456104677321759075 3963078684157015982638613)
                ·
                  refine ⟨185769313319860124186185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3963078684157015982638613 185769313319860124186185)
                  ·
                    rfl

theorem cell22_1628030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1628030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628030 prefixEnd_1628030 := by exact prefixLift 1628030
  have htrace : WordTrace (prefixWord ++ tailWord_1628030) baseStart_1628030 baseEnd_1628030 := by
    simpa [prefixWord, tailWord_1628030, baseEnd_1628030] using wordTrace_append hprefix tailTrace_1628030
  have hstable : (prefixWord ++ tailWord_1628030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628030).length < 2 ^ (prefixWord ++ tailWord_1628030).sum := by decide
  have hdescent : baseEnd_1628030 < baseStart_1628030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628058 : List Nat := [3, 1, 1, 4, 2, 1, 4, 6]
def baseStart_1628058 : Nat := 118140960795 + 1628058 * 2 ^ 59
def prefixEnd_1628058 : Nat := 4983230072969 + 3 ^ 40 * 1628058 * 2
def baseEnd_1628058 : Nat := 61924169436866403650941

theorem tailTrace_1628058 : CollatzResearch.WordTrace tailWord_1628058 prefixEnd_1628058 61924169436866403650941 := by
  unfold tailWord_1628058
  simp only [CollatzResearch.WordTrace]
  refine ⟨14845038383957847753701207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39586769023887594009869885 14845038383957847753701207)
  ·
    refine ⟨22267557575936771630551811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14845038383957847753701207 22267557575936771630551811)
    ·
      refine ⟨33401336363905157445827717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22267557575936771630551811 33401336363905157445827717)
      ·
        refine ⟨6262750568232217021092697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33401336363905157445827717 6262750568232217021092697)
        ·
          refine ⟨4697062926174162765819523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6262750568232217021092697 4697062926174162765819523)
          ·
            refine ⟨7045594389261244148729285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697062926174162765819523 7045594389261244148729285)
            ·
              refine ⟨1321048947986483277886741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7045594389261244148729285 1321048947986483277886741)
              ·
                refine ⟨61924169436866403650941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1321048947986483277886741 61924169436866403650941)
                ·
                  rfl

theorem cell22_1628058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_1628058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628058 prefixEnd_1628058 := by exact prefixLift 1628058
  have htrace : WordTrace (prefixWord ++ tailWord_1628058) baseStart_1628058 baseEnd_1628058 := by
    simpa [prefixWord, tailWord_1628058, baseEnd_1628058] using wordTrace_append hprefix tailTrace_1628058
  have hstable : (prefixWord ++ tailWord_1628058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628058).length < 2 ^ (prefixWord ++ tailWord_1628058).sum := by decide
  have hdescent : baseEnd_1628058 < baseStart_1628058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628193 : List Nat := [1, 2, 3, 2, 4, 1, 9]
def baseStart_1628193 : Nat := 118140960795 + 1628193 * 2 ^ 59
def prefixEnd_1628193 : Nat := 4983230072969 + 3 ^ 40 * 1628193 * 2
def baseEnd_1628193 : Nat := 20643101414470454841965

theorem tailTrace_1628193 : CollatzResearch.WordTrace tailWord_1628193 prefixEnd_1628193 20643101414470454841965 := by
  unfold tailWord_1628193
  simp only [CollatzResearch.WordTrace]
  refine ⟨59385077390342309070969233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39590051593561539380646155 59385077390342309070969233)
  ·
    refine ⟨44538808042756731803226925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59385077390342309070969233 44538808042756731803226925)
    ·
      refine ⟨16702053016033774426210097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44538808042756731803226925 16702053016033774426210097)
      ·
        refine ⟨12526539762025330819657573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16702053016033774426210097 12526539762025330819657573)
        ·
          refine ⟨2348726205379749528685795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12526539762025330819657573 2348726205379749528685795)
          ·
            refine ⟨3523089308069624293028693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2348726205379749528685795 3523089308069624293028693)
            ·
              refine ⟨20643101414470454841965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3523089308069624293028693 20643101414470454841965)
              ·
                rfl

theorem cell22_1628193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 9].length) (baseStart_1628193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628193 prefixEnd_1628193 := by exact prefixLift 1628193
  have htrace : WordTrace (prefixWord ++ tailWord_1628193) baseStart_1628193 baseEnd_1628193 := by
    simpa [prefixWord, tailWord_1628193, baseEnd_1628193] using wordTrace_append hprefix tailTrace_1628193
  have hstable : (prefixWord ++ tailWord_1628193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628193).length < 2 ^ (prefixWord ++ tailWord_1628193).sum := by decide
  have hdescent : baseEnd_1628193 < baseStart_1628193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628197 : List Nat := [1, 3, 1, 2, 2, 5, 1, 2, 2, 3]
def baseStart_1628197 : Nat := 118140960795 + 1628197 * 2 ^ 59
def prefixEnd_1628197 : Nat := 4983230072969 + 3 ^ 40 * 1628197 * 2
def baseEnd_1628197 : Nat := 557365107472447603633043

theorem tailTrace_1628197 : CollatzResearch.WordTrace tailWord_1628197 prefixEnd_1628197 557365107472447603633043 := by
  unfold tailWord_1628197
  simp only [CollatzResearch.WordTrace]
  refine ⟨59385223282327817754114845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39590148854885211836076563 59385223282327817754114845)
  ·
    refine ⟨22269458730872931657793067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59385223282327817754114845 22269458730872931657793067)
    ·
      refine ⟨33404188096309397486689601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22269458730872931657793067 33404188096309397486689601)
      ·
        refine ⟨25053141072232048115017201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33404188096309397486689601 25053141072232048115017201)
        ·
          refine ⟨18789855804174036086262901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25053141072232048115017201 18789855804174036086262901)
          ·
            refine ⟨1761548981641315883087147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18789855804174036086262901 1761548981641315883087147)
            ·
              refine ⟨2642323472461973824630721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761548981641315883087147 2642323472461973824630721)
              ·
                refine ⟨1981742604346480368473041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2642323472461973824630721 1981742604346480368473041)
                ·
                  refine ⟨1486306953259860276354781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1981742604346480368473041 1486306953259860276354781)
                  ·
                    refine ⟨557365107472447603633043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1486306953259860276354781 557365107472447603633043)
                    ·
                      rfl

theorem cell22_1628197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_1628197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628197 prefixEnd_1628197 := by exact prefixLift 1628197
  have htrace : WordTrace (prefixWord ++ tailWord_1628197) baseStart_1628197 baseEnd_1628197 := by
    simpa [prefixWord, tailWord_1628197, baseEnd_1628197] using wordTrace_append hprefix tailTrace_1628197
  have hstable : (prefixWord ++ tailWord_1628197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628197).length < 2 ^ (prefixWord ++ tailWord_1628197).sum := by decide
  have hdescent : baseEnd_1628197 < baseStart_1628197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628214 : List Nat := [5, 1, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_1628214 : Nat := 118140960795 + 1628214 * 2 ^ 59
def prefixEnd_1628214 : Nat := 4983230072969 + 3 ^ 40 * 1628214 * 2
def baseEnd_1628214 : Nat := 557370926919865225957991

theorem tailTrace_1628214 : CollatzResearch.WordTrace tailWord_1628214 prefixEnd_1628214 557370926919865225957991 := by
  unfold tailWord_1628214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3711615207704139353592731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39590562215510819771655797 3711615207704139353592731)
  ·
    refine ⟨5567422811556209030389097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3711615207704139353592731 5567422811556209030389097)
    ·
      refine ⟨4175567108667156772791823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5567422811556209030389097 4175567108667156772791823)
      ·
        refine ⟨6263350663000735159187735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4175567108667156772791823 6263350663000735159187735)
        ·
          refine ⟨9395025994501102738781603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6263350663000735159187735 9395025994501102738781603)
          ·
            refine ⟨14092538991751654108172405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9395025994501102738781603 14092538991751654108172405)
            ·
              refine ⟨1321175530476717572641163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14092538991751654108172405 1321175530476717572641163)
              ·
                refine ⟨1981763295715076358961745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321175530476717572641163 1981763295715076358961745)
                ·
                  refine ⟨1486322471786307269221309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1981763295715076358961745 1486322471786307269221309)
                  ·
                    refine ⟨557370926919865225957991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1486322471786307269221309 557370926919865225957991)
                    ·
                      rfl

theorem cell22_1628214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_1628214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628214 prefixEnd_1628214 := by exact prefixLift 1628214
  have htrace : WordTrace (prefixWord ++ tailWord_1628214) baseStart_1628214 baseEnd_1628214 := by
    simpa [prefixWord, tailWord_1628214, baseEnd_1628214] using wordTrace_append hprefix tailTrace_1628214
  have hstable : (prefixWord ++ tailWord_1628214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628214).length < 2 ^ (prefixWord ++ tailWord_1628214).sum := by decide
  have hdescent : baseEnd_1628214 < baseStart_1628214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628238 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_1628238 : Nat := 118140960795 + 1628238 * 2 ^ 59
def prefixEnd_1628238 : Nat := 4983230072969 + 3 ^ 40 * 1628238 * 2
def baseEnd_1628238 : Nat := 185793047536779054452639

theorem tailTrace_1628238 : CollatzResearch.WordTrace tailWord_1628238 prefixEnd_1628238 185793047536779054452639 := by
  unfold tailWord_1628238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7423339834397410219544671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39591145783452854504238245 7423339834397410219544671)
  ·
    refine ⟨11135009751596115329317007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7423339834397410219544671 11135009751596115329317007)
    ·
      refine ⟨16702514627394172993975511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11135009751596115329317007 16702514627394172993975511)
      ·
        refine ⟨25053771941091259490963267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16702514627394172993975511 25053771941091259490963267)
        ·
          refine ⟨37580657911636889236444901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25053771941091259490963267 37580657911636889236444901)
          ·
            refine ⟨7046373358431916731833419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37580657911636889236444901 7046373358431916731833419)
            ·
              refine ⟨10569560037647875097750129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7046373358431916731833419 10569560037647875097750129)
              ·
                refine ⟨7927170028235906323312597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10569560037647875097750129 7927170028235906323312597)
                ·
                  refine ⟨185793047536779054452639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7927170028235906323312597 185793047536779054452639)
                  ·
                    rfl

theorem cell22_1628238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_1628238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628238 prefixEnd_1628238 := by exact prefixLift 1628238
  have htrace : WordTrace (prefixWord ++ tailWord_1628238) baseStart_1628238 baseEnd_1628238 := by
    simpa [prefixWord, tailWord_1628238, baseEnd_1628238] using wordTrace_append hprefix tailTrace_1628238
  have hstable : (prefixWord ++ tailWord_1628238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628238).length < 2 ^ (prefixWord ++ tailWord_1628238).sum := by decide
  have hdescent : baseEnd_1628238 < baseStart_1628238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628272 : List Nat := [2, 1, 1, 1, 5, 4, 2, 1, 5]
def baseStart_1628272 : Nat := 118140960795 + 1628272 * 2 ^ 59
def prefixEnd_1628272 : Nat := 4983230072969 + 3 ^ 40 * 1628272 * 2
def baseEnd_1628272 : Nat := 185796927168390802669271

theorem tailTrace_1628272 : CollatzResearch.WordTrace tailWord_1628272 prefixEnd_1628272 185796927168390802669271 := by
  unfold tailWord_1628272
  simp only [CollatzResearch.WordTrace]
  refine ⟨29693979378528052781547535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39591972504704070375396713 29693979378528052781547535)
  ·
    refine ⟨44540969067792079172321303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29693979378528052781547535 44540969067792079172321303)
    ·
      refine ⟨66811453601688118758481955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44540969067792079172321303 66811453601688118758481955)
      ·
        refine ⟨100217180402532178137722933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66811453601688118758481955 100217180402532178137722933)
        ·
          refine ⟨9395360662737391700411525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100217180402532178137722933 9395360662737391700411525)
          ·
            refine ⟨1761630124263260943827161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9395360662737391700411525 1761630124263260943827161)
            ·
              refine ⟨1321222593197445707870371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1761630124263260943827161 1321222593197445707870371)
              ·
                refine ⟨1981833889796168561805557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321222593197445707870371 1981833889796168561805557)
                ·
                  refine ⟨185796927168390802669271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1981833889796168561805557 185796927168390802669271)
                  ·
                    rfl

theorem cell22_1628272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 5].length) (baseStart_1628272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628272 prefixEnd_1628272 := by exact prefixLift 1628272
  have htrace : WordTrace (prefixWord ++ tailWord_1628272) baseStart_1628272 baseEnd_1628272 := by
    simpa [prefixWord, tailWord_1628272, baseEnd_1628272] using wordTrace_append hprefix tailTrace_1628272
  have hstable : (prefixWord ++ tailWord_1628272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628272).length < 2 ^ (prefixWord ++ tailWord_1628272).sum := by decide
  have hdescent : baseEnd_1628272 < baseStart_1628272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628285 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_1628285 : Nat := 118140960795 + 1628285 * 2 ^ 59
def prefixEnd_1628285 : Nat := 4983230072969 + 3 ^ 40 * 1628285 * 2
def baseEnd_1628285 : Nat := 557395231670844707432773

theorem tailTrace_1628285 : CollatzResearch.WordTrace tailWord_1628285 prefixEnd_1628285 557395231670844707432773 := by
  unfold tailWord_1628285
  simp only [CollatzResearch.WordTrace]
  refine ⟨59388432906009008783318309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39592288604006005855545539 59388432906009008783318309)
  ·
    refine ⟨11135331169876689146872183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59388432906009008783318309 11135331169876689146872183)
    ·
      refine ⟨16702996754815033720308275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11135331169876689146872183 16702996754815033720308275)
      ·
        refine ⟨25054495132222550580462413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16702996754815033720308275 25054495132222550580462413)
        ·
          refine ⟨9395435674583456467673405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25054495132222550580462413 9395435674583456467673405)
          ·
            refine ⟨3523288377968796175377527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9395435674583456467673405 3523288377968796175377527)
            ·
              refine ⟨5284932566953194263066291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523288377968796175377527 5284932566953194263066291)
              ·
                refine ⟨7927398850429791394599437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5284932566953194263066291 7927398850429791394599437)
                ·
                  refine ⟨2972774568911171772974789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7927398850429791394599437 2972774568911171772974789)
                  ·
                    refine ⟨557395231670844707432773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2972774568911171772974789 557395231670844707432773)
                    ·
                      rfl

theorem cell22_1628285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_1628285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628285 prefixEnd_1628285 := by exact prefixLift 1628285
  have htrace : WordTrace (prefixWord ++ tailWord_1628285) baseStart_1628285 baseEnd_1628285 := by
    simpa [prefixWord, tailWord_1628285, baseEnd_1628285] using wordTrace_append hprefix tailTrace_1628285
  have hstable : (prefixWord ++ tailWord_1628285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628285).length < 2 ^ (prefixWord ++ tailWord_1628285).sum := by decide
  have hdescent : baseEnd_1628285 < baseStart_1628285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628317 : List Nat := [1, 4, 2, 1, 1, 4, 1, 4, 4]
def baseStart_1628317 : Nat := 118140960795 + 1628317 * 2 ^ 59
def prefixEnd_1628317 : Nat := 4983230072969 + 3 ^ 40 * 1628317 * 2
def baseEnd_1628317 : Nat := 185802061974935763544225

theorem tailTrace_1628317 : CollatzResearch.WordTrace tailWord_1628317 prefixEnd_1628317 185802061974935763544225 := by
  unfold tailWord_1628317
  simp only [CollatzResearch.WordTrace]
  refine ⟨59389600041893078248483205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39593066694595385498988803 59389600041893078248483205)
  ·
    refine ⟨11135550007854952171590601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59389600041893078248483205 11135550007854952171590601)
    ·
      refine ⟨8351662505891214128692951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11135550007854952171590601 8351662505891214128692951)
      ·
        refine ⟨12527493758836821193039427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8351662505891214128692951 12527493758836821193039427)
        ·
          refine ⟨18791240638255231789559141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12527493758836821193039427 18791240638255231789559141)
          ·
            refine ⟨3523357619672855960542339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18791240638255231789559141 3523357619672855960542339)
            ·
              refine ⟨5285036429509283940813509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523357619672855960542339 5285036429509283940813509)
              ·
                refine ⟨990944330532990738902533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5285036429509283940813509 990944330532990738902533)
                ·
                  refine ⟨185802061974935763544225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 990944330532990738902533 185802061974935763544225)
                  ·
                    rfl

theorem cell22_1628317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_1628317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628317 prefixEnd_1628317 := by exact prefixLift 1628317
  have htrace : WordTrace (prefixWord ++ tailWord_1628317) baseStart_1628317 baseEnd_1628317 := by
    simpa [prefixWord, tailWord_1628317, baseEnd_1628317] using wordTrace_append hprefix tailTrace_1628317
  have hstable : (prefixWord ++ tailWord_1628317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628317).length < 2 ^ (prefixWord ++ tailWord_1628317).sum := by decide
  have hdescent : baseEnd_1628317 < baseStart_1628317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628334 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_1628334 : Nat := 118140960795 + 1628334 * 2 ^ 59
def prefixEnd_1628334 : Nat := 4983230072969 + 3 ^ 40 * 1628334 * 2
def baseEnd_1628334 : Nat := 185804001790741637652541

theorem tailTrace_1628334 : CollatzResearch.WordTrace tailWord_1628334 prefixEnd_1628334 185804001790741637652541 := by
  unfold tailWord_1628334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7423777510353936268981507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39593480055220993434568037 7423777510353936268981507)
  ·
    refine ⟨11135666265530904403472261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7423777510353936268981507 11135666265530904403472261)
    ·
      refine ⟨2087937424787044575651049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11135666265530904403472261 2087937424787044575651049)
      ·
        refine ⟨1565953068590283431738287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2087937424787044575651049 1565953068590283431738287)
        ·
          refine ⟨2348929602885425147607431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1565953068590283431738287 2348929602885425147607431)
          ·
            refine ⟨3523394404328137721411147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2348929602885425147607431 3523394404328137721411147)
            ·
              refine ⟨5285091606492206582116721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3523394404328137721411147 5285091606492206582116721)
              ·
                refine ⟨3963818704869154936587541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5285091606492206582116721 3963818704869154936587541)
                ·
                  refine ⟨185804001790741637652541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3963818704869154936587541 185804001790741637652541)
                  ·
                    rfl

theorem cell22_1628334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_1628334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628334 prefixEnd_1628334 := by exact prefixLift 1628334
  have htrace : WordTrace (prefixWord ++ tailWord_1628334) baseStart_1628334 baseEnd_1628334 := by
    simpa [prefixWord, tailWord_1628334, baseEnd_1628334] using wordTrace_append hprefix tailTrace_1628334
  have hstable : (prefixWord ++ tailWord_1628334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628334).length < 2 ^ (prefixWord ++ tailWord_1628334).sum := by decide
  have hdescent : baseEnd_1628334 < baseStart_1628334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628345 : List Nat := [1, 2, 1, 4, 1, 2, 5, 6]
def baseStart_1628345 : Nat := 118140960795 + 1628345 * 2 ^ 59
def prefixEnd_1628345 : Nat := 4983230072969 + 3 ^ 40 * 1628345 * 2
def baseEnd_1628345 : Nat := 61935085655224950103621

theorem tailTrace_1628345 : CollatzResearch.WordTrace tailWord_1628345 prefixEnd_1628345 61935085655224950103621 := by
  unfold tailWord_1628345
  simp only [CollatzResearch.WordTrace]
  refine ⟨59390621285791639030502489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39593747523861092687001659 59390621285791639030502489)
  ·
    refine ⟨44542965964343729272876867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59390621285791639030502489 44542965964343729272876867)
    ·
      refine ⟨66814448946515593909315301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44542965964343729272876867 66814448946515593909315301)
      ·
        refine ⟨12527709177471673857996619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66814448946515593909315301 12527709177471673857996619)
        ·
          refine ⟨18791563766207510786994929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12527709177471673857996619 18791563766207510786994929)
          ·
            refine ⟨14093672824655633090246197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18791563766207510786994929 14093672824655633090246197)
            ·
              refine ⟨1321281827311465602210581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14093672824655633090246197 1321281827311465602210581)
              ·
                refine ⟨61935085655224950103621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1321281827311465602210581 61935085655224950103621)
                ·
                  rfl

theorem cell22_1628345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 6].length) (baseStart_1628345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628345 prefixEnd_1628345 := by exact prefixLift 1628345
  have htrace : WordTrace (prefixWord ++ tailWord_1628345) baseStart_1628345 baseEnd_1628345 := by
    simpa [prefixWord, tailWord_1628345, baseEnd_1628345] using wordTrace_append hprefix tailTrace_1628345
  have hstable : (prefixWord ++ tailWord_1628345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628345).length < 2 ^ (prefixWord ++ tailWord_1628345).sum := by decide
  have hdescent : baseEnd_1628345 < baseStart_1628345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628353 : List Nat := [1, 2, 6, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1628353 : Nat := 118140960795 + 1628353 * 2 ^ 59
def prefixEnd_1628353 : Nat := 4983230072969 + 3 ^ 40 * 1628353 * 2
def baseEnd_1628353 : Nat := 557418509460515196732565

theorem tailTrace_1628353 : CollatzResearch.WordTrace tailWord_1628353 prefixEnd_1628353 557418509460515196732565 := by
  unfold tailWord_1628353
  simp only [CollatzResearch.WordTrace]
  refine ⟨59390913069762656396793713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39593942046508437597862475 59390913069762656396793713)
  ·
    refine ⟨44543184802321992297595285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59390913069762656396793713 44543184802321992297595285)
    ·
      refine ⟨2087961787608843388949779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44543184802321992297595285 2087961787608843388949779)
      ·
        refine ⟨3131942681413265083424669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087961787608843388949779 3131942681413265083424669)
        ·
          refine ⟨1174478505529974406284251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3131942681413265083424669 1174478505529974406284251)
          ·
            refine ⟨1761717758294961609426377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174478505529974406284251 1761717758294961609426377)
            ·
              refine ⟨1321288318721221207069783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1761717758294961609426377 1321288318721221207069783)
              ·
                refine ⟨1981932478081831810604675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321288318721221207069783 1981932478081831810604675)
                ·
                  refine ⟨2972898717122747715907013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1981932478081831810604675 2972898717122747715907013)
                  ·
                    refine ⟨557418509460515196732565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2972898717122747715907013 557418509460515196732565)
                    ·
                      rfl

theorem cell22_1628353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1628353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628353 prefixEnd_1628353 := by exact prefixLift 1628353
  have htrace : WordTrace (prefixWord ++ tailWord_1628353) baseStart_1628353 baseEnd_1628353 := by
    simpa [prefixWord, tailWord_1628353, baseEnd_1628353] using wordTrace_append hprefix tailTrace_1628353
  have hstable : (prefixWord ++ tailWord_1628353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628353).length < 2 ^ (prefixWord ++ tailWord_1628353).sum := by decide
  have hdescent : baseEnd_1628353 < baseStart_1628353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628360 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 7, 3]
def baseStart_1628360 : Nat := 118140960795 + 1628360 * 2 ^ 59
def prefixEnd_1628360 : Nat := 4983230072969 + 3 ^ 40 * 1628360 * 2
def baseEnd_1628360 : Nat := 557420905703569511807543

theorem tailTrace_1628360 : CollatzResearch.WordTrace tailWord_1628360 prefixEnd_1628360 557420905703569511807543 := by
  unfold tailWord_1628360
  simp only [CollatzResearch.WordTrace]
  refine ⟨29695584190368648296149267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39594112253824864394865689 29695584190368648296149267)
  ·
    refine ⟨44543376285552972444223901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29695584190368648296149267 44543376285552972444223901)
    ·
      refine ⟨16703766107082364666583963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44543376285552972444223901 16703766107082364666583963)
      ·
        refine ⟨25055649160623546999875945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16703766107082364666583963 25055649160623546999875945)
        ·
          refine ⟨18791736870467660249906959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25055649160623546999875945 18791736870467660249906959)
          ·
            refine ⟨28187605305701490374860439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18791736870467660249906959 28187605305701490374860439)
            ·
              refine ⟨42281407958552235562290659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28187605305701490374860439 42281407958552235562290659)
              ·
                refine ⟨63422111937828353343435989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42281407958552235562290659 63422111937828353343435989)
                ·
                  refine ⟨1486455748542852031486781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 63422111937828353343435989 1486455748542852031486781)
                  ·
                    refine ⟨557420905703569511807543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1486455748542852031486781 557420905703569511807543)
                    ·
                      rfl

theorem cell22_1628360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_1628360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628360 prefixEnd_1628360 := by exact prefixLift 1628360
  have htrace : WordTrace (prefixWord ++ tailWord_1628360) baseStart_1628360 baseEnd_1628360 := by
    simpa [prefixWord, tailWord_1628360, baseEnd_1628360] using wordTrace_append hprefix tailTrace_1628360
  have hstable : (prefixWord ++ tailWord_1628360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628360).length < 2 ^ (prefixWord ++ tailWord_1628360).sum := by decide
  have hdescent : baseEnd_1628360 < baseStart_1628360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628497 : List Nat := [1, 2, 2, 1, 4, 4, 1, 7]
def baseStart_1628497 : Nat := 118140960795 + 1628497 * 2 ^ 59
def prefixEnd_1628497 : Nat := 4983230072969 + 3 ^ 40 * 1628497 * 2
def baseEnd_1628497 : Nat := 61940867067038535681347

theorem tailTrace_1628497 : CollatzResearch.WordTrace tailWord_1628497 prefixEnd_1628497 61940867067038535681347 := by
  unfold tailWord_1628497
  simp only [CollatzResearch.WordTrace]
  refine ⟨59396165181240968990035745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39597443454160645993357163 59396165181240968990035745)
  ·
    refine ⟨44547123885930726742526809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59396165181240968990035745 44547123885930726742526809)
    ·
      refine ⟨33410342914448045056895107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44547123885930726742526809 33410342914448045056895107)
      ·
        refine ⟨50115514371672067585342661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33410342914448045056895107 50115514371672067585342661)
        ·
          refine ⟨9396658944688512672251749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50115514371672067585342661 9396658944688512672251749)
          ·
            refine ⟨1761873552129096126047203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9396658944688512672251749 1761873552129096126047203)
            ·
              refine ⟨2642810328193644189070805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761873552129096126047203 2642810328193644189070805)
              ·
                refine ⟨61940867067038535681347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2642810328193644189070805 61940867067038535681347)
                ·
                  rfl

theorem cell22_1628497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 7].length) (baseStart_1628497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628497 prefixEnd_1628497 := by exact prefixLift 1628497
  have htrace : WordTrace (prefixWord ++ tailWord_1628497) baseStart_1628497 baseEnd_1628497 := by
    simpa [prefixWord, tailWord_1628497, baseEnd_1628497] using wordTrace_append hprefix tailTrace_1628497
  have hstable : (prefixWord ++ tailWord_1628497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628497).length < 2 ^ (prefixWord ++ tailWord_1628497).sum := by decide
  have hdescent : baseEnd_1628497 < baseStart_1628497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628514 : List Nat := [3, 3, 2, 1, 1, 3, 3, 6]
def baseStart_1628514 : Nat := 118140960795 + 1628514 * 2 ^ 59
def prefixEnd_1628514 : Nat := 4983230072969 + 3 ^ 40 * 1628514 * 2
def baseEnd_1628514 : Nat := 61941513672307160384119

theorem tailTrace_1628514 : CollatzResearch.WordTrace tailWord_1628514 prefixEnd_1628514 61941513672307160384119 := by
  unfold tailWord_1628514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14849196305544845223351149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39597856814786253928936397 14849196305544845223351149)
  ·
    refine ⟨5568448614579316958756681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14849196305544845223351149 5568448614579316958756681)
    ·
      refine ⟨4176336460934487719067511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5568448614579316958756681 4176336460934487719067511)
      ·
        refine ⟨6264504691401731578601267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4176336460934487719067511 6264504691401731578601267)
        ·
          refine ⟨9396757037102597367901901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6264504691401731578601267 9396757037102597367901901)
          ·
            refine ⟨3523783888913474012963213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9396757037102597367901901 3523783888913474012963213)
            ·
              refine ⟨1321418958342552754861205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3523783888913474012963213 1321418958342552754861205)
              ·
                refine ⟨61941513672307160384119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1321418958342552754861205 61941513672307160384119)
                ·
                  rfl

theorem cell22_1628514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_1628514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628514 prefixEnd_1628514 := by exact prefixLift 1628514
  have htrace : WordTrace (prefixWord ++ tailWord_1628514) baseStart_1628514 baseEnd_1628514 := by
    simpa [prefixWord, tailWord_1628514, baseEnd_1628514] using wordTrace_append hprefix tailTrace_1628514
  have hstable : (prefixWord ++ tailWord_1628514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628514).length < 2 ^ (prefixWord ++ tailWord_1628514).sum := by decide
  have hdescent : baseEnd_1628514 < baseStart_1628514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628604 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 6]
def baseStart_1628604 : Nat := 118140960795 + 1628604 * 2 ^ 59
def prefixEnd_1628604 : Nat := 4983230072969 + 3 ^ 40 * 1628604 * 2
def baseEnd_1628604 : Nat := 185834810630011402902265

theorem tailTrace_1628604 : CollatzResearch.WordTrace tailWord_1628604 prefixEnd_1628604 185834810630011402902265 := by
  unfold tailWord_1628604
  simp only [CollatzResearch.WordTrace]
  refine ⟨29700033895926663132090433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39600045194568884176120577 29700033895926663132090433)
  ·
    refine ⟨22275025421944997349067825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29700033895926663132090433 22275025421944997349067825)
    ·
      refine ⟨16706269066458748011800869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22275025421944997349067825 16706269066458748011800869)
      ·
        refine ⟨3132425449961015252212663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16706269066458748011800869 3132425449961015252212663)
        ·
          refine ⟨4698638174941522878318995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3132425449961015252212663 4698638174941522878318995)
          ·
            refine ⟨7047957262412284317478493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4698638174941522878318995 7047957262412284317478493)
            ·
              refine ⟨2642983973404606619054435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7047957262412284317478493 2642983973404606619054435)
              ·
                refine ⟨3964475960106909928581653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642983973404606619054435 3964475960106909928581653)
                ·
                  refine ⟨185834810630011402902265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3964475960106909928581653 185834810630011402902265)
                  ·
                    rfl

theorem cell22_1628604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_1628604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628604 prefixEnd_1628604 := by exact prefixLift 1628604
  have htrace : WordTrace (prefixWord ++ tailWord_1628604) baseStart_1628604 baseEnd_1628604 := by
    simpa [prefixWord, tailWord_1628604, baseEnd_1628604] using wordTrace_append hprefix tailTrace_1628604
  have hstable : (prefixWord ++ tailWord_1628604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628604).length < 2 ^ (prefixWord ++ tailWord_1628604).sum := by decide
  have hdescent : baseEnd_1628604 < baseStart_1628604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628634 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_1628634 : Nat := 118140960795 + 1628634 * 2 ^ 59
def prefixEnd_1628634 : Nat := 4983230072969 + 3 ^ 40 * 1628634 * 2
def baseEnd_1628634 : Nat := 557514701503124130456703

theorem tailTrace_1628634 : CollatzResearch.WordTrace tailWord_1628634 prefixEnd_1628634 557514701503124130456703 := by
  unfold tailWord_1628634
  simp only [CollatzResearch.WordTrace]
  refine ⟨14850290495436160346943239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39600774654496427591848637 14850290495436160346943239)
  ·
    refine ⟨22275435743154240520414859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14850290495436160346943239 22275435743154240520414859)
    ·
      refine ⟨33413153614731360780622289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22275435743154240520414859 33413153614731360780622289)
      ·
        refine ⟨25059865211048520585466717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33413153614731360780622289 25059865211048520585466717)
        ·
          refine ⟨9397449454143195219550019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25059865211048520585466717 9397449454143195219550019)
          ·
            refine ⟨14096174181214792829325029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9397449454143195219550019 14096174181214792829325029)
            ·
              refine ⟨2643032658977773655498443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14096174181214792829325029 2643032658977773655498443)
              ·
                refine ⟨3964548988466660483247665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2643032658977773655498443 3964548988466660483247665)
                ·
                  refine ⟨2973411741349995362435749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3964548988466660483247665 2973411741349995362435749)
                  ·
                    refine ⟨557514701503124130456703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2973411741349995362435749 557514701503124130456703)
                    ·
                      rfl

theorem cell22_1628634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_1628634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628634 prefixEnd_1628634 := by exact prefixLift 1628634
  have htrace : WordTrace (prefixWord ++ tailWord_1628634) baseStart_1628634 baseEnd_1628634 := by
    simpa [prefixWord, tailWord_1628634, baseEnd_1628634] using wordTrace_append hprefix tailTrace_1628634
  have hstable : (prefixWord ++ tailWord_1628634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628634).length < 2 ^ (prefixWord ++ tailWord_1628634).sum := by decide
  have hdescent : baseEnd_1628634 < baseStart_1628634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628653 : List Nat := [1, 5, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_1628653 : Nat := 118140960795 + 1628653 * 2 ^ 59
def prefixEnd_1628653 : Nat := 4983230072969 + 3 ^ 40 * 1628653 * 2
def baseEnd_1628653 : Nat := 557521205591414414231645

theorem tailTrace_1628653 : CollatzResearch.WordTrace tailWord_1628653 prefixEnd_1628653 557521205591414414231645 := by
  unfold tailWord_1628653
  simp only [CollatzResearch.WordTrace]
  refine ⟨59401854968675807632714613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39601236645783871755143075 59401854968675807632714613)
  ·
    refine ⟨5568923903313356965566995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59401854968675807632714613 5568923903313356965566995)
    ·
      refine ⟨8353385854970035448350493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5568923903313356965566995 8353385854970035448350493)
      ·
        refine ⟨3132519695613763293131435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8353385854970035448350493 3132519695613763293131435)
        ·
          refine ⟨4698779543420644939697153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3132519695613763293131435 4698779543420644939697153)
          ·
            refine ⟨3524084657565483704772865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4698779543420644939697153 3524084657565483704772865)
            ·
              refine ⟨2643063493174112778579649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3524084657565483704772865 2643063493174112778579649)
              ·
                refine ⟨1982297619880584583934737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2643063493174112778579649 1982297619880584583934737)
                ·
                  refine ⟨1486723214910438437951053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1982297619880584583934737 1486723214910438437951053)
                  ·
                    refine ⟨557521205591414414231645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1486723214910438437951053 557521205591414414231645)
                    ·
                      rfl

theorem cell22_1628653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_1628653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628653 prefixEnd_1628653 := by exact prefixLift 1628653
  have htrace : WordTrace (prefixWord ++ tailWord_1628653) baseStart_1628653 baseEnd_1628653 := by
    simpa [prefixWord, tailWord_1628653, baseEnd_1628653] using wordTrace_append hprefix tailTrace_1628653
  have hstable : (prefixWord ++ tailWord_1628653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628653).length < 2 ^ (prefixWord ++ tailWord_1628653).sum := by decide
  have hdescent : baseEnd_1628653 < baseStart_1628653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628664 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 3, 3]
def baseStart_1628664 : Nat := 118140960795 + 1628664 * 2 ^ 59
def prefixEnd_1628664 : Nat := 4983230072969 + 3 ^ 40 * 1628664 * 2
def baseEnd_1628664 : Nat := 557524971116214052206611

theorem tailTrace_1628664 : CollatzResearch.WordTrace tailWord_1628664 prefixEnd_1628664 557524971116214052206611 := by
  unfold tailWord_1628664
  simp only [CollatzResearch.WordTrace]
  refine ⟨29701128085817978255682523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39601504114423971007576697 29701128085817978255682523)
  ·
    refine ⟨44551692128726967383523785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29701128085817978255682523 44551692128726967383523785)
    ·
      refine ⟨33413769096545225537642839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44551692128726967383523785 33413769096545225537642839)
      ·
        refine ⟨50120653644817838306464259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33413769096545225537642839 50120653644817838306464259)
        ·
          refine ⟨75180980467226757459696389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50120653644817838306464259 75180980467226757459696389)
          ·
            refine ⟨14096433837605017023693073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75180980467226757459696389 14096433837605017023693073)
            ·
              refine ⟨10572325378203762767769805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14096433837605017023693073 10572325378203762767769805)
              ·
                refine ⟨3964622016826411037913677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10572325378203762767769805 3964622016826411037913677)
                ·
                  refine ⟨1486733256309904139217629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3964622016826411037913677 1486733256309904139217629)
                  ·
                    refine ⟨557524971116214052206611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1486733256309904139217629 557524971116214052206611)
                    ·
                      rfl

theorem cell22_1628664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_1628664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628664 prefixEnd_1628664 := by exact prefixLift 1628664
  have htrace : WordTrace (prefixWord ++ tailWord_1628664) baseStart_1628664 baseEnd_1628664 := by
    simpa [prefixWord, tailWord_1628664, baseEnd_1628664] using wordTrace_append hprefix tailTrace_1628664
  have hstable : (prefixWord ++ tailWord_1628664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628664).length < 2 ^ (prefixWord ++ tailWord_1628664).sum := by decide
  have hdescent : baseEnd_1628664 < baseStart_1628664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628685 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1628685 : Nat := 118140960795 + 1628685 * 2 ^ 59
def prefixEnd_1628685 : Nat := 4983230072969 + 3 ^ 40 * 1628685 * 2
def baseEnd_1628685 : Nat := 557532159845376997431547

theorem tailTrace_1628685 : CollatzResearch.WordTrace tailWord_1628685 prefixEnd_1628685 557532159845376997431547 := by
  unfold tailWord_1628685
  simp only [CollatzResearch.WordTrace]
  refine ⟨59403022104559877097879509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39602014736373251398586339 59403022104559877097879509)
  ·
    refine ⟨1392258330575622119481551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 59403022104559877097879509 1392258330575622119481551)
    ·
      refine ⟨2088387495863433179222327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1392258330575622119481551 2088387495863433179222327)
      ·
        refine ⟨3132581243795149768833491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2088387495863433179222327 3132581243795149768833491)
        ·
          refine ⟨4698871865692724653250237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3132581243795149768833491 4698871865692724653250237)
          ·
            refine ⟨1762076949634771744968839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4698871865692724653250237 1762076949634771744968839)
            ·
              refine ⟨2643115424452157617453259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762076949634771744968839 2643115424452157617453259)
              ·
                refine ⟨3964673136678236426179889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2643115424452157617453259 3964673136678236426179889)
                ·
                  refine ⟨2973504852508677319634917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3964673136678236426179889 2973504852508677319634917)
                  ·
                    refine ⟨557532159845376997431547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2973504852508677319634917 557532159845376997431547)
                    ·
                      rfl

theorem cell22_1628685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1628685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628685 prefixEnd_1628685 := by exact prefixLift 1628685
  have htrace : WordTrace (prefixWord ++ tailWord_1628685) baseStart_1628685 baseEnd_1628685 := by
    simpa [prefixWord, tailWord_1628685, baseEnd_1628685] using wordTrace_append hprefix tailTrace_1628685
  have hstable : (prefixWord ++ tailWord_1628685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628685).length < 2 ^ (prefixWord ++ tailWord_1628685).sum := by decide
  have hdescent : baseEnd_1628685 < baseStart_1628685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628726 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1628726 : Nat := 118140960795 + 1628726 * 2 ^ 59
def prefixEnd_1628726 : Nat := 4983230072969 + 3 ^ 40 * 1628726 * 2
def baseEnd_1628726 : Nat := 557546194983266557156421

theorem tailTrace_1628726 : CollatzResearch.WordTrace tailWord_1628726 prefixEnd_1628726 557546194983266557156421 := by
  unfold tailWord_1628726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3712782343588208818757627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39603011664940894066748021 3712782343588208818757627)
  ·
    refine ⟨5569173515382313228136441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3712782343588208818757627 5569173515382313228136441)
    ·
      refine ⟨4176880136536734921102331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5569173515382313228136441 4176880136536734921102331)
      ·
        refine ⟨6265320204805102381653497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4176880136536734921102331 6265320204805102381653497)
        ·
          refine ⟨4698990153603826786240123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6265320204805102381653497 4698990153603826786240123)
          ·
            refine ⟨7048485230405740179360185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4698990153603826786240123 7048485230405740179360185)
            ·
              refine ⟨5286363922804305134520139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7048485230405740179360185 5286363922804305134520139)
              ·
                refine ⟨7929545884206457701780209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5286363922804305134520139 7929545884206457701780209)
                ·
                  refine ⟨5947159413154843276335157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7929545884206457701780209 5947159413154843276335157)
                  ·
                    refine ⟨557546194983266557156421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5947159413154843276335157 557546194983266557156421)
                    ·
                      rfl

theorem cell22_1628726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1628726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628726 prefixEnd_1628726 := by exact prefixLift 1628726
  have htrace : WordTrace (prefixWord ++ tailWord_1628726) baseStart_1628726 baseEnd_1628726 := by
    simpa [prefixWord, tailWord_1628726, baseEnd_1628726] using wordTrace_append hprefix tailTrace_1628726
  have hstable : (prefixWord ++ tailWord_1628726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628726).length < 2 ^ (prefixWord ++ tailWord_1628726).sum := by decide
  have hdescent : baseEnd_1628726 < baseStart_1628726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628741 : List Nat := [1, 3, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_1628741 : Nat := 118140960795 + 1628741 * 2 ^ 59
def prefixEnd_1628741 : Nat := 4983230072969 + 3 ^ 40 * 1628741 * 2
def baseEnd_1628741 : Nat := 557551329789811518031375

theorem tailTrace_1628741 : CollatzResearch.WordTrace tailWord_1628741 prefixEnd_1628741 557551329789811518031375 := by
  unfold tailWord_1628741
  simp only [CollatzResearch.WordTrace]
  refine ⟨59405064592356998661918077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39603376394904665774612051 59405064592356998661918077)
  ·
    refine ⟨22276899222133874498219279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59405064592356998661918077 22276899222133874498219279)
    ·
      refine ⟨33415348833200811747328919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22276899222133874498219279 33415348833200811747328919)
      ·
        refine ⟨50123023249801217620993379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33415348833200811747328919 50123023249801217620993379)
        ·
          refine ⟨75184534874701826431490069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50123023249801217620993379 75184534874701826431490069)
          ·
            refine ⟨3524275072251648113976097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75184534874701826431490069 3524275072251648113976097)
            ·
              refine ⟨2643206304188736085482073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3524275072251648113976097 2643206304188736085482073)
              ·
                refine ⟨1982404728141552064111555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2643206304188736085482073 1982404728141552064111555)
                ·
                  refine ⟨2973607092212328096167333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982404728141552064111555 2973607092212328096167333)
                  ·
                    refine ⟨557551329789811518031375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2973607092212328096167333 557551329789811518031375)
                    ·
                      rfl

theorem cell22_1628741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_1628741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628741 prefixEnd_1628741 := by exact prefixLift 1628741
  have htrace : WordTrace (prefixWord ++ tailWord_1628741) baseStart_1628741 baseEnd_1628741 := by
    simpa [prefixWord, tailWord_1628741, baseEnd_1628741] using wordTrace_append hprefix tailTrace_1628741
  have hstable : (prefixWord ++ tailWord_1628741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628741).length < 2 ^ (prefixWord ++ tailWord_1628741).sum := by decide
  have hdescent : baseEnd_1628741 < baseStart_1628741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628754 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_1628754 : Nat := 118140960795 + 1628754 * 2 ^ 59
def prefixEnd_1628754 : Nat := 4983230072969 + 3 ^ 40 * 1628754 * 2
def baseEnd_1628754 : Nat := 557555779955483817456335

theorem tailTrace_1628754 : CollatzResearch.WordTrace tailWord_1628754 prefixEnd_1628754 557555779955483817456335 := by
  unfold tailWord_1628754
  simp only [CollatzResearch.WordTrace]
  refine ⟨14851384685327475470535329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39603692494206601254760877 14851384685327475470535329)
  ·
    refine ⟨11138538513995606602901497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14851384685327475470535329 11138538513995606602901497)
    ·
      refine ⟨8353903885496704952176123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11138538513995606602901497 8353903885496704952176123)
      ·
        refine ⟨12530855828245057428264185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8353903885496704952176123 12530855828245057428264185)
        ·
          refine ⟨9398141871183793071198139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12530855828245057428264185 9398141871183793071198139)
          ·
            refine ⟨14097212806775689606797209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9398141871183793071198139 14097212806775689606797209)
            ·
              refine ⟨10572909605081767205097907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14097212806775689606797209 10572909605081767205097907)
              ·
                refine ⟨15859364407622650807646861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10572909605081767205097907 15859364407622650807646861)
                ·
                  refine ⟨5947261652858494052867573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15859364407622650807646861 5947261652858494052867573)
                  ·
                    refine ⟨557555779955483817456335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5947261652858494052867573 557555779955483817456335)
                    ·
                      rfl

theorem cell22_1628754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_1628754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628754 prefixEnd_1628754 := by exact prefixLift 1628754
  have htrace : WordTrace (prefixWord ++ tailWord_1628754) baseStart_1628754 baseEnd_1628754 := by
    simpa [prefixWord, tailWord_1628754, baseEnd_1628754] using wordTrace_append hprefix tailTrace_1628754
  have hstable : (prefixWord ++ tailWord_1628754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628754).length < 2 ^ (prefixWord ++ tailWord_1628754).sum := by decide
  have hdescent : baseEnd_1628754 < baseStart_1628754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628766 : List Nat := [4, 4, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1628766 : Nat := 118140960795 + 1628766 * 2 ^ 59
def prefixEnd_1628766 : Nat := 4983230072969 + 3 ^ 40 * 1628766 * 2
def baseEnd_1628766 : Nat := 557559887800719786156299

theorem tailTrace_1628766 : CollatzResearch.WordTrace tailWord_1628766 prefixEnd_1628766 557559887800719786156299 := by
  unfold tailWord_1628766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7425747052158303491447269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39603984278177618621052101 7425747052158303491447269)
  ·
    refine ⟨1392327572279681904646363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7425747052158303491447269 1392327572279681904646363)
    ·
      refine ⟨2088491358419522856969545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1392327572279681904646363 2088491358419522856969545)
      ·
        refine ⟨1566368518814642142727159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2088491358419522856969545 1566368518814642142727159)
        ·
          refine ⟨2349552778221963214090739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566368518814642142727159 2349552778221963214090739)
          ·
            refine ⟨3524329167332944821136109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349552778221963214090739 3524329167332944821136109)
            ·
              refine ⟨1321623437749854307926041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3524329167332944821136109 1321623437749854307926041)
              ·
                refine ⟨991217578312390730944531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1321623437749854307926041 991217578312390730944531)
                ·
                  refine ⟨1486826367468586096416797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991217578312390730944531 1486826367468586096416797)
                  ·
                    refine ⟨557559887800719786156299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1486826367468586096416797 557559887800719786156299)
                    ·
                      rfl

theorem cell22_1628766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1628766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628766 prefixEnd_1628766 := by exact prefixLift 1628766
  have htrace : WordTrace (prefixWord ++ tailWord_1628766) baseStart_1628766 baseEnd_1628766 := by
    simpa [prefixWord, tailWord_1628766, baseEnd_1628766] using wordTrace_append hprefix tailTrace_1628766
  have hstable : (prefixWord ++ tailWord_1628766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628766).length < 2 ^ (prefixWord ++ tailWord_1628766).sum := by decide
  have hdescent : baseEnd_1628766 < baseStart_1628766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628769 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 4, 4]
def baseStart_1628769 : Nat := 118140960795 + 1628769 * 2 ^ 59
def prefixEnd_1628769 : Nat := 4983230072969 + 3 ^ 40 * 1628769 * 2
def baseEnd_1628769 : Nat := 557560914762028778331289

theorem tailTrace_1628769 : CollatzResearch.WordTrace tailWord_1628769 prefixEnd_1628769 557560914762028778331289 := by
  unfold tailWord_1628769
  simp only [CollatzResearch.WordTrace]
  refine ⟨59406085836255559443937361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39604057224170372962624907 59406085836255559443937361)
  ·
    refine ⟨44554564377191669582953021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59406085836255559443937361 44554564377191669582953021)
    ·
      refine ⟨16707961641446876093607383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44554564377191669582953021 16707961641446876093607383)
      ·
        refine ⟨25061942462170314140411075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16707961641446876093607383 25061942462170314140411075)
        ·
          refine ⟨37592913693255471210616613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25061942462170314140411075 37592913693255471210616613)
          ·
            refine ⟨7048671317485400851990615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37592913693255471210616613 7048671317485400851990615)
            ·
              refine ⟨10573006976228101277985923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7048671317485400851990615 10573006976228101277985923)
              ·
                refine ⟨15859510464342151916978885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10573006976228101277985923 15859510464342151916978885)
                ·
                  refine ⟨2973658212064153484433541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15859510464342151916978885 2973658212064153484433541)
                  ·
                    refine ⟨557560914762028778331289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2973658212064153484433541 557560914762028778331289)
                    ·
                      rfl

theorem cell22_1628769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_1628769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628769 prefixEnd_1628769 := by exact prefixLift 1628769
  have htrace : WordTrace (prefixWord ++ tailWord_1628769) baseStart_1628769 baseEnd_1628769 := by
    simpa [prefixWord, tailWord_1628769, baseEnd_1628769] using wordTrace_append hprefix tailTrace_1628769
  have hstable : (prefixWord ++ tailWord_1628769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628769).length < 2 ^ (prefixWord ++ tailWord_1628769).sum := by decide
  have hdescent : baseEnd_1628769 < baseStart_1628769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628771 : List Nat := [1, 1, 1, 5, 1, 2, 2, 4, 2, 3]
def baseStart_1628771 : Nat := 118140960795 + 1628771 * 2 ^ 59
def prefixEnd_1628771 : Nat := 4983230072969 + 3 ^ 40 * 1628771 * 2
def baseEnd_1628771 : Nat := 557561599402901439781283

theorem tailTrace_1628771 : CollatzResearch.WordTrace tailWord_1628771 prefixEnd_1628771 557561599402901439781283 := by
  unfold tailWord_1628771
  simp only [CollatzResearch.WordTrace]
  refine ⟨59406158782248313785510167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39604105854832209190340111 59406158782248313785510167)
  ·
    refine ⟨89109238173372470678265251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59406158782248313785510167 89109238173372470678265251)
    ·
      refine ⟨133663857260058706017397877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89109238173372470678265251 133663857260058706017397877)
      ·
        refine ⟨12530986618130503689131051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133663857260058706017397877 12530986618130503689131051)
        ·
          refine ⟨18796479927195755533696577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12530986618130503689131051 18796479927195755533696577)
          ·
            refine ⟨14097359945396816650272433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18796479927195755533696577 14097359945396816650272433)
            ·
              refine ⟨10573019959047612487704325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14097359945396816650272433 10573019959047612487704325)
              ·
                refine ⟨1982441242321427341444561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10573019959047612487704325 1982441242321427341444561)
                ·
                  refine ⟨1486830931741070506083421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1982441242321427341444561 1486830931741070506083421)
                  ·
                    refine ⟨557561599402901439781283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1486830931741070506083421 557561599402901439781283)
                    ·
                      rfl

theorem cell22_1628771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 3].length) (baseStart_1628771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628771 prefixEnd_1628771 := by exact prefixLift 1628771
  have htrace : WordTrace (prefixWord ++ tailWord_1628771) baseStart_1628771 baseEnd_1628771 := by
    simpa [prefixWord, tailWord_1628771, baseEnd_1628771] using wordTrace_append hprefix tailTrace_1628771
  have hstable : (prefixWord ++ tailWord_1628771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628771).length < 2 ^ (prefixWord ++ tailWord_1628771).sum := by decide
  have hdescent : baseEnd_1628771 < baseStart_1628771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628773 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 6]
def baseStart_1628773 : Nat := 118140960795 + 1628773 * 2 ^ 59
def prefixEnd_1628773 : Nat := 4983230072969 + 3 ^ 40 * 1628773 * 2
def baseEnd_1628773 : Nat := 185854094681258033743759

theorem tailTrace_1628773 : CollatzResearch.WordTrace tailWord_1628773 prefixEnd_1628773 185854094681258033743759 := by
  unfold tailWord_1628773
  simp only [CollatzResearch.WordTrace]
  refine ⟨59406231728241068127082973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39604154485494045418055315 59406231728241068127082973)
  ·
    refine ⟨22277336898090400547656115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59406231728241068127082973 22277336898090400547656115)
    ·
      refine ⟨33416005347135600821484173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22277336898090400547656115 33416005347135600821484173)
      ·
        refine ⟨12531002005175850308056565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33416005347135600821484173 12531002005175850308056565)
        ·
          refine ⟨1174781437985235966380303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12531002005175850308056565 1174781437985235966380303)
          ·
            refine ⟨1762172156977853949570455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174781437985235966380303 1762172156977853949570455)
            ·
              refine ⟨2643258235466780924355683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762172156977853949570455 2643258235466780924355683)
              ·
                refine ⟨3964887353200171386533525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2643258235466780924355683 3964887353200171386533525)
                ·
                  refine ⟨185854094681258033743759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3964887353200171386533525 185854094681258033743759)
                  ·
                    rfl

theorem cell22_1628773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_1628773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628773 prefixEnd_1628773 := by exact prefixLift 1628773
  have htrace : WordTrace (prefixWord ++ tailWord_1628773) baseStart_1628773 baseEnd_1628773 := by
    simpa [prefixWord, tailWord_1628773, baseEnd_1628773] using wordTrace_append hprefix tailTrace_1628773
  have hstable : (prefixWord ++ tailWord_1628773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628773).length < 2 ^ (prefixWord ++ tailWord_1628773).sum := by decide
  have hdescent : baseEnd_1628773 < baseStart_1628773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628829 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 7]
def baseStart_1628829 : Nat := 118140960795 + 1628829 * 2 ^ 59
def prefixEnd_1628829 : Nat := 4983230072969 + 3 ^ 40 * 1628829 * 2
def baseEnd_1628829 : Nat := 185860484662736207277035

theorem tailTrace_1628829 : CollatzResearch.WordTrace tailWord_1628829 prefixEnd_1628829 185860484662736207277035 := by
  unfold tailWord_1628829
  simp only [CollatzResearch.WordTrace]
  refine ⟨59408274216038189691121541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39605516144025459794081027 59408274216038189691121541)
  ·
    refine ⟨11139051415507160567085289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59408274216038189691121541 11139051415507160567085289)
    ·
      refine ⟨8354288561630370425313967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11139051415507160567085289 8354288561630370425313967)
      ·
        refine ⟨12531432842445555637970951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8354288561630370425313967 12531432842445555637970951)
        ·
          refine ⟨18797149263668333456956427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12531432842445555637970951 18797149263668333456956427)
          ·
            refine ⟨28195723895502500185434641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18797149263668333456956427 28195723895502500185434641)
            ·
              refine ⟨21146792921626875139075981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28195723895502500185434641 21146792921626875139075981)
              ·
                refine ⟨7930047345610078177153493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21146792921626875139075981 7930047345610078177153493)
                ·
                  refine ⟨185860484662736207277035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7930047345610078177153493 185860484662736207277035)
                  ·
                    rfl

theorem cell22_1628829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_1628829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628829 prefixEnd_1628829 := by exact prefixLift 1628829
  have htrace : WordTrace (prefixWord ++ tailWord_1628829) baseStart_1628829 baseEnd_1628829 := by
    simpa [prefixWord, tailWord_1628829, baseEnd_1628829] using wordTrace_append hprefix tailTrace_1628829
  have hstable : (prefixWord ++ tailWord_1628829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628829).length < 2 ^ (prefixWord ++ tailWord_1628829).sum := by decide
  have hdescent : baseEnd_1628829 < baseStart_1628829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628936 : List Nat := [2, 1, 3, 2, 2, 4, 8]
def baseStart_1628936 : Nat := 118140960795 + 1628936 * 2 ^ 59
def prefixEnd_1628936 : Nat := 4983230072969 + 3 ^ 40 * 1628936 * 2
def baseEnd_1628936 : Nat := 20652521565736889237251

theorem tailTrace_1628936 : CollatzResearch.WordTrace tailWord_1628936 prefixEnd_1628936 20652521565736889237251 := by
  unfold tailWord_1628936
  simp only [CollatzResearch.WordTrace]
  refine ⟨29706088413325273482633331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39608117884433697976844441 29706088413325273482633331)
  ·
    refine ⟨44559132619987910223949997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29706088413325273482633331 44559132619987910223949997)
    ·
      refine ⟨16709674732495466333981249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44559132619987910223949997 16709674732495466333981249)
      ·
        refine ⟨12532256049371599750485937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16709674732495466333981249 12532256049371599750485937)
        ·
          refine ⟨9399192037028699812864453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12532256049371599750485937 9399192037028699812864453)
          ·
            refine ⟨1762348506942881214912085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9399192037028699812864453 1762348506942881214912085)
            ·
              refine ⟨20652521565736889237251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1762348506942881214912085 20652521565736889237251)
              ·
                rfl

theorem cell22_1628936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 8].length) (baseStart_1628936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628936 prefixEnd_1628936 := by exact prefixLift 1628936
  have htrace : WordTrace (prefixWord ++ tailWord_1628936) baseStart_1628936 baseEnd_1628936 := by
    simpa [prefixWord, tailWord_1628936, baseEnd_1628936] using wordTrace_append hprefix tailTrace_1628936
  have hstable : (prefixWord ++ tailWord_1628936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628936).length < 2 ^ (prefixWord ++ tailWord_1628936).sum := by decide
  have hdescent : baseEnd_1628936 < baseStart_1628936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628957 : List Nat := [1, 4, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_1628957 : Nat := 118140960795 + 1628957 * 2 ^ 59
def prefixEnd_1628957 : Nat := 4983230072969 + 3 ^ 40 * 1628957 * 2
def baseEnd_1628957 : Nat := 557625271004058954630713

theorem tailTrace_1628957 : CollatzResearch.WordTrace tailWord_1628957 prefixEnd_1628957 557625271004058954630713 := by
  unfold tailWord_1628957
  simp only [CollatzResearch.WordTrace]
  refine ⟨59412942759574467551781125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39608628506382978367854083 59412942759574467551781125)
  ·
    refine ⟨11139926767420212665958961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59412942759574467551781125 11139926767420212665958961)
    ·
      refine ⟨8354945075565159499469221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11139926767420212665958961 8354945075565159499469221)
      ·
        refine ⟨1566552201668467406150479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8354945075565159499469221 1566552201668467406150479)
        ·
          refine ⟨2349828302502701109225719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566552201668467406150479 2349828302502701109225719)
          ·
            refine ⟨3524742453754051663838579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349828302502701109225719 3524742453754051663838579)
            ·
              refine ⟨5287113680631077495757869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3524742453754051663838579 5287113680631077495757869)
              ·
                refine ⟨1982667630236654060909201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5287113680631077495757869 1982667630236654060909201)
                ·
                  refine ⟨1487000722677490545681901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1982667630236654060909201 1487000722677490545681901)
                  ·
                    refine ⟨557625271004058954630713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1487000722677490545681901 557625271004058954630713)
                    ·
                      rfl

theorem cell22_1628957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_1628957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628957 prefixEnd_1628957 := by exact prefixLift 1628957
  have htrace : WordTrace (prefixWord ++ tailWord_1628957) baseStart_1628957 baseEnd_1628957 := by
    simpa [prefixWord, tailWord_1628957, baseEnd_1628957] using wordTrace_append hprefix tailTrace_1628957
  have hstable : (prefixWord ++ tailWord_1628957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628957).length < 2 ^ (prefixWord ++ tailWord_1628957).sum := by decide
  have hdescent : baseEnd_1628957 < baseStart_1628957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628968 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1628968 : Nat := 118140960795 + 1628968 * 2 ^ 59
def prefixEnd_1628968 : Nat := 4983230072969 + 3 ^ 40 * 1628968 * 2
def baseEnd_1628968 : Nat := 557629036528858592605679

theorem tailTrace_1628968 : CollatzResearch.WordTrace tailWord_1628968 prefixEnd_1628968 557629036528858592605679 := by
  unfold tailWord_1628968
  simp only [CollatzResearch.WordTrace]
  refine ⟨29706671981267308215215779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39608895975023077620287705 29706671981267308215215779)
  ·
    refine ⟨44560007971900962322823669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29706671981267308215215779 44560007971900962322823669)
    ·
      refine ⟨4177500747365715217764719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44560007971900962322823669 4177500747365715217764719)
      ·
        refine ⟨6266251121048572826647079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4177500747365715217764719 6266251121048572826647079)
        ·
          refine ⟨9399376681572859239970619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6266251121048572826647079 9399376681572859239970619)
          ·
            refine ⟨14099065022359288859955929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9399376681572859239970619 14099065022359288859955929)
            ·
              refine ⟨10574298766769466644966947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14099065022359288859955929 10574298766769466644966947)
              ·
                refine ⟨15861448150154199967450421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10574298766769466644966947 15861448150154199967450421)
                ·
                  refine ⟨1487010764076956246948477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15861448150154199967450421 1487010764076956246948477)
                  ·
                    refine ⟨557629036528858592605679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1487010764076956246948477 557629036528858592605679)
                    ·
                      rfl

theorem cell22_1628968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1628968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1628968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1628968 prefixEnd_1628968 := by exact prefixLift 1628968
  have htrace : WordTrace (prefixWord ++ tailWord_1628968) baseStart_1628968 baseEnd_1628968 := by
    simpa [prefixWord, tailWord_1628968, baseEnd_1628968] using wordTrace_append hprefix tailTrace_1628968
  have hstable : (prefixWord ++ tailWord_1628968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628968).length < 2 ^ (prefixWord ++ tailWord_1628968).sum := by decide
  have hdescent : baseEnd_1628968 < baseStart_1628968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629028 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_1629028 : Nat := 118140960795 + 1629028 * 2 ^ 59
def prefixEnd_1629028 : Nat := 4983230072969 + 3 ^ 40 * 1629028 * 2
def baseEnd_1629028 : Nat := 557649575755038436105495

theorem tailTrace_1629028 : CollatzResearch.WordTrace tailWord_1629028 prefixEnd_1629028 557649575755038436105495 := by
  unfold tailWord_1629028
  simp only [CollatzResearch.WordTrace]
  refine ⟨29707766171158623338807869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39610354894878164451743825 29707766171158623338807869)
  ·
    refine ⟨11140412314184483752052951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29707766171158623338807869 11140412314184483752052951)
    ·
      refine ⟨16710618471276725628079427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11140412314184483752052951 16710618471276725628079427)
      ·
        refine ⟨25065927706915088442119141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16710618471276725628079427 25065927706915088442119141)
        ·
          refine ⟨4699861445046579082897339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25065927706915088442119141 4699861445046579082897339)
          ·
            refine ⟨7049792167569868624346009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4699861445046579082897339 7049792167569868624346009)
            ·
              refine ⟨5287344125677401468259507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7049792167569868624346009 5287344125677401468259507)
              ·
                refine ⟨7931016188516102202389261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5287344125677401468259507 7931016188516102202389261)
                ·
                  refine ⟨2974131070693538325895973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7931016188516102202389261 2974131070693538325895973)
                  ·
                    refine ⟨557649575755038436105495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2974131070693538325895973 557649575755038436105495)
                    ·
                      rfl

theorem cell22_1629028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_1629028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629028 prefixEnd_1629028 := by exact prefixLift 1629028
  have htrace : WordTrace (prefixWord ++ tailWord_1629028) baseStart_1629028 baseEnd_1629028 := by
    simpa [prefixWord, tailWord_1629028, baseEnd_1629028] using wordTrace_append hprefix tailTrace_1629028
  have hstable : (prefixWord ++ tailWord_1629028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629028).length < 2 ^ (prefixWord ++ tailWord_1629028).sum := by decide
  have hdescent : baseEnd_1629028 < baseStart_1629028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629043 : List Nat := [1, 1, 1, 2, 2, 1, 5, 5, 4]
def baseStart_1629043 : Nat := 118140960795 + 1629043 * 2 ^ 59
def prefixEnd_1629043 : Nat := 4983230072969 + 3 ^ 40 * 1629043 * 2
def baseEnd_1629043 : Nat := 185884903520527798993483

theorem tailTrace_1629043 : CollatzResearch.WordTrace tailWord_1629043 prefixEnd_1629043 185884903520527798993483 := by
  unfold tailWord_1629043
  simp only [CollatzResearch.WordTrace]
  refine ⟨59416079437262904239411783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39610719624841936159607855 59416079437262904239411783)
  ·
    refine ⟨89124119155894356359117675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59416079437262904239411783 89124119155894356359117675)
    ·
      refine ⟨133686178733841534538676513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89124119155894356359117675 133686178733841534538676513)
      ·
        refine ⟨100264634050381150904007385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133686178733841534538676513 100264634050381150904007385)
        ·
          refine ⟨75198475537785863178005539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100264634050381150904007385 75198475537785863178005539)
          ·
            refine ⟨112797713306678794767008309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75198475537785863178005539 112797713306678794767008309)
            ·
              refine ⟨10574785622501137009407029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112797713306678794767008309 10574785622501137009407029)
              ·
                refine ⟨991386152109481594631909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10574785622501137009407029 991386152109481594631909)
                ·
                  refine ⟨185884903520527798993483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 991386152109481594631909 185884903520527798993483)
                  ·
                    rfl

theorem cell22_1629043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 4].length) (baseStart_1629043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629043 prefixEnd_1629043 := by exact prefixLift 1629043
  have htrace : WordTrace (prefixWord ++ tailWord_1629043) baseStart_1629043 baseEnd_1629043 := by
    simpa [prefixWord, tailWord_1629043, baseEnd_1629043] using wordTrace_append hprefix tailTrace_1629043
  have hstable : (prefixWord ++ tailWord_1629043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629043).length < 2 ^ (prefixWord ++ tailWord_1629043).sum := by decide
  have hdescent : baseEnd_1629043 < baseStart_1629043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629045 : List Nat := [1, 3, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1629045 : Nat := 118140960795 + 1629045 * 2 ^ 59
def prefixEnd_1629045 : Nat := 4983230072969 + 3 ^ 40 * 1629045 * 2
def baseEnd_1629045 : Nat := 557655395202456058430443

theorem tailTrace_1629045 : CollatzResearch.WordTrace tailWord_1629045 prefixEnd_1629045 557655395202456058430443 := by
  unfold tailWord_1629045
  simp only [CollatzResearch.WordTrace]
  refine ⟨59416152383255658580984589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39610768255503772387323059 59416152383255658580984589)
  ·
    refine ⟨22281057143720871967869221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59416152383255658580984589 22281057143720871967869221)
    ·
      refine ⟨4177698214447663493975479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22281057143720871967869221 4177698214447663493975479)
      ·
        refine ⟨6266547321671495240963219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4177698214447663493975479 6266547321671495240963219)
        ·
          refine ⟨9399820982507242861444829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6266547321671495240963219 9399820982507242861444829)
          ·
            refine ⟨3524932868440216073041811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9399820982507242861444829 3524932868440216073041811)
            ·
              refine ⟨5287399302660324109562717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3524932868440216073041811 5287399302660324109562717)
              ·
                refine ⟨1982774738497621541086019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5287399302660324109562717 1982774738497621541086019)
                ·
                  refine ⟨2974162107746432311629029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1982774738497621541086019 2974162107746432311629029)
                  ·
                    refine ⟨557655395202456058430443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2974162107746432311629029 557655395202456058430443)
                    ·
                      rfl

theorem cell22_1629045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1629045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629045 prefixEnd_1629045 := by exact prefixLift 1629045
  have htrace : WordTrace (prefixWord ++ tailWord_1629045) baseStart_1629045 baseEnd_1629045 := by
    simpa [prefixWord, tailWord_1629045, baseEnd_1629045] using wordTrace_append hprefix tailTrace_1629045
  have hstable : (prefixWord ++ tailWord_1629045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629045).length < 2 ^ (prefixWord ++ tailWord_1629045).sum := by decide
  have hdescent : baseEnd_1629045 < baseStart_1629045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629088 : List Nat := [2, 1, 1, 4, 1, 1, 6, 6]
def baseStart_1629088 : Nat := 118140960795 + 1629088 * 2 ^ 59
def prefixEnd_1629088 : Nat := 4983230072969 + 3 ^ 40 * 1629088 * 2
def baseEnd_1629088 : Nat := 61963346109024253289479

theorem tailTrace_1629088 : CollatzResearch.WordTrace tailWord_1629088 prefixEnd_1629088 61963346109024253289479 := by
  unfold tailWord_1629088
  simp only [CollatzResearch.WordTrace]
  refine ⟨29708860361049938462399959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39611813814733251283199945 29708860361049938462399959)
  ·
    refine ⟨44563290541574907693599939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29708860361049938462399959 44563290541574907693599939)
    ·
      refine ⟨66844935812362361540399909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44563290541574907693599939 66844935812362361540399909)
      ·
        refine ⟨12533425464817942788824983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66844935812362361540399909 12533425464817942788824983)
        ·
          refine ⟨18800138197226914183237475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12533425464817942788824983 18800138197226914183237475)
          ·
            refine ⟨28200207295840371274856213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18800138197226914183237475 28200207295840371274856213)
            ·
              refine ⟨1321884716992517403508885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28200207295840371274856213 1321884716992517403508885)
              ·
                refine ⟨61963346109024253289479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1321884716992517403508885 61963346109024253289479)
                ·
                  rfl

theorem cell22_1629088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 6].length) (baseStart_1629088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629088 prefixEnd_1629088 := by exact prefixLift 1629088
  have htrace : WordTrace (prefixWord ++ tailWord_1629088) baseStart_1629088 baseEnd_1629088 := by
    simpa [prefixWord, tailWord_1629088, baseEnd_1629088] using wordTrace_append hprefix tailTrace_1629088
  have hstable : (prefixWord ++ tailWord_1629088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629088).length < 2 ^ (prefixWord ++ tailWord_1629088).sum := by decide
  have hdescent : baseEnd_1629088 < baseStart_1629088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629105 : List Nat := [1, 2, 2, 4, 4, 1, 8]
def baseStart_1629105 : Nat := 118140960795 + 1629105 * 2 ^ 59
def prefixEnd_1629105 : Nat := 4983230072969 + 3 ^ 40 * 1629105 * 2
def baseEnd_1629105 : Nat := 20654664238097625997417

theorem tailTrace_1629105 : CollatzResearch.WordTrace tailWord_1629105 prefixEnd_1629105 20654664238097625997417 := by
  unfold tailWord_1629105
  simp only [CollatzResearch.WordTrace]
  refine ⟨59418340763038288828168769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39612227175358859218779179 59418340763038288828168769)
  ·
    refine ⟨44563755572278716621126577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59418340763038288828168769 44563755572278716621126577)
    ·
      refine ⟨33422816679209037465844933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44563755572278716621126577 33422816679209037465844933)
      ·
        refine ⟨6266778127351694524845925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33422816679209037465844933 6266778127351694524845925)
        ·
          refine ⟨1175020898878442723408611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6266778127351694524845925 1175020898878442723408611)
          ·
            refine ⟨1762531348317664085112917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175020898878442723408611 1762531348317664085112917)
            ·
              refine ⟨20654664238097625997417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1762531348317664085112917 20654664238097625997417)
              ·
                rfl

theorem cell22_1629105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 8].length) (baseStart_1629105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629105 prefixEnd_1629105 := by exact prefixLift 1629105
  have htrace : WordTrace (prefixWord ++ tailWord_1629105) baseStart_1629105 baseEnd_1629105 := by
    simpa [prefixWord, tailWord_1629105, baseEnd_1629105] using wordTrace_append hprefix tailTrace_1629105
  have hstable : (prefixWord ++ tailWord_1629105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629105).length < 2 ^ (prefixWord ++ tailWord_1629105).sum := by decide
  have hdescent : baseEnd_1629105 < baseStart_1629105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629118 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_1629118 : Nat := 118140960795 + 1629118 * 2 ^ 59
def prefixEnd_1629118 : Nat := 4983230072969 + 3 ^ 40 * 1629118 * 2
def baseEnd_1629118 : Nat := 557680384594308201355219

theorem tailTrace_1629118 : CollatzResearch.WordTrace tailWord_1629118 prefixEnd_1629118 557680384594308201355219 := by
  unfold tailWord_1629118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427351863998899006049001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39612543274660794698928005 7427351863998899006049001)
  ·
    refine ⟨5570513897999174254536751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7427351863998899006049001 5570513897999174254536751)
    ·
      refine ⟨8355770846998761381805127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5570513897999174254536751 8355770846998761381805127)
      ·
        refine ⟨12533656270498142072707691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8355770846998761381805127 12533656270498142072707691)
        ·
          refine ⟨18800484405747213109061537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12533656270498142072707691 18800484405747213109061537)
          ·
            refine ⟨14100363304310409831796153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18800484405747213109061537 14100363304310409831796153)
            ·
              refine ⟨10575272478232807373847115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14100363304310409831796153 10575272478232807373847115)
              ·
                refine ⟨15862908717349211060770673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10575272478232807373847115 15862908717349211060770673)
                ·
                  refine ⟨11897181538011908295578005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15862908717349211060770673 11897181538011908295578005)
                  ·
                    refine ⟨557680384594308201355219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11897181538011908295578005 557680384594308201355219)
                    ·
                      rfl

theorem cell22_1629118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_1629118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629118 prefixEnd_1629118 := by exact prefixLift 1629118
  have htrace : WordTrace (prefixWord ++ tailWord_1629118) baseStart_1629118 baseEnd_1629118 := by
    simpa [prefixWord, tailWord_1629118, baseEnd_1629118] using wordTrace_append hprefix tailTrace_1629118
  have hstable : (prefixWord ++ tailWord_1629118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629118).length < 2 ^ (prefixWord ++ tailWord_1629118).sum := by decide
  have hdescent : baseEnd_1629118 < baseStart_1629118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629120 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 3, 3]
def baseStart_1629120 : Nat := 118140960795 + 1629120 * 2 ^ 59
def prefixEnd_1629120 : Nat := 4983230072969 + 3 ^ 40 * 1629120 * 2
def baseEnd_1629120 : Nat := 557681069235180862805213

theorem tailTrace_1629120 : CollatzResearch.WordTrace tailWord_1629120 prefixEnd_1629120 557681069235180862805213 := by
  unfold tailWord_1629120
  simp only [CollatzResearch.WordTrace]
  refine ⟨29709443928991973194982407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39612591905322630926643209 29709443928991973194982407)
  ·
    refine ⟨44564165893487959792473611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29709443928991973194982407 44564165893487959792473611)
    ·
      refine ⟨66846248840231939688710417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44564165893487959792473611 66846248840231939688710417)
      ·
        refine ⟨50134686630173954766532813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66846248840231939688710417 50134686630173954766532813)
        ·
          refine ⟨18800507486315233037449805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50134686630173954766532813 18800507486315233037449805)
          ·
            refine ⟨7050190307368212389043677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18800507486315233037449805 7050190307368212389043677)
            ·
              refine ⟨2643821365263079645891379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7050190307368212389043677 2643821365263079645891379)
              ·
                refine ⟨3965732047894619468837069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2643821365263079645891379 3965732047894619468837069)
                ·
                  refine ⟨1487149517960482300813901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3965732047894619468837069 1487149517960482300813901)
                  ·
                    refine ⟨557681069235180862805213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1487149517960482300813901 557681069235180862805213)
                    ·
                      rfl

theorem cell22_1629120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 3, 3].length) (baseStart_1629120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629120 prefixEnd_1629120 := by exact prefixLift 1629120
  have htrace : WordTrace (prefixWord ++ tailWord_1629120) baseStart_1629120 baseEnd_1629120 := by
    simpa [prefixWord, tailWord_1629120, baseEnd_1629120] using wordTrace_append hprefix tailTrace_1629120
  have hstable : (prefixWord ++ tailWord_1629120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629120).length < 2 ^ (prefixWord ++ tailWord_1629120).sum := by decide
  have hdescent : baseEnd_1629120 < baseStart_1629120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629182 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1629182 : Nat := 118140960795 + 1629182 * 2 ^ 59
def prefixEnd_1629182 : Nat := 4983230072969 + 3 ^ 40 * 1629182 * 2
def baseEnd_1629182 : Nat := 557702293102233367755023

theorem tailTrace_1629182 : CollatzResearch.WordTrace tailWord_1629182 prefixEnd_1629182 557702293102233367755023 := by
  unfold tailWord_1629182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427643647969916372340225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39614099455839553985814533 7427643647969916372340225)
  ·
    refine ⟨5570732735977437279255169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7427643647969916372340225 5570732735977437279255169)
    ·
      refine ⟨4178049551983077959441377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5570732735977437279255169 4178049551983077959441377)
      ·
        refine ⟨3133537163987308469581033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4178049551983077959441377 3133537163987308469581033)
        ·
          refine ⟨2350152872990481352185775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3133537163987308469581033 2350152872990481352185775)
          ·
            refine ⟨3525229309485722028278663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350152872990481352185775 3525229309485722028278663)
            ·
              refine ⟨5287843964228583042417995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3525229309485722028278663 5287843964228583042417995)
              ·
                refine ⟨7931765946342874563626993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5287843964228583042417995 7931765946342874563626993)
                ·
                  refine ⟨5948824459757155922720245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7931765946342874563626993 5948824459757155922720245)
                  ·
                    refine ⟨557702293102233367755023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5948824459757155922720245 557702293102233367755023)
                    ·
                      rfl

theorem cell22_1629182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1629182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629182 prefixEnd_1629182 := by exact prefixLift 1629182
  have htrace : WordTrace (prefixWord ++ tailWord_1629182) baseStart_1629182 baseEnd_1629182 := by
    simpa [prefixWord, tailWord_1629182, baseEnd_1629182] using wordTrace_append hprefix tailTrace_1629182
  have hstable : (prefixWord ++ tailWord_1629182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629182).length < 2 ^ (prefixWord ++ tailWord_1629182).sum := by decide
  have hdescent : baseEnd_1629182 < baseStart_1629182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629210 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 4, 3]
def baseStart_1629210 : Nat := 118140960795 + 1629210 * 2 ^ 59
def prefixEnd_1629210 : Nat := 4983230072969 + 3 ^ 40 * 1629210 * 2
def baseEnd_1629210 : Nat := 557711878074450628054937

theorem tailTrace_1629210 : CollatzResearch.WordTrace tailWord_1629210 prefixEnd_1629210 557711878074450628054937 := by
  unfold tailWord_1629210
  simp only [CollatzResearch.WordTrace]
  refine ⟨14855542606914472940185271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39614780285105261173827389 14855542606914472940185271)
  ·
    refine ⟨22283313910371709410277907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14855542606914472940185271 22283313910371709410277907)
    ·
      refine ⟨33424970865557564115416861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22283313910371709410277907 33424970865557564115416861)
      ·
        refine ⟨12534364074584086543281323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33424970865557564115416861 12534364074584086543281323)
        ·
          refine ⟨18801546111876129814921985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12534364074584086543281323 18801546111876129814921985)
          ·
            refine ⟨14101159583907097361191489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18801546111876129814921985 14101159583907097361191489)
            ·
              refine ⟨10575869687930323020893617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14101159583907097361191489 10575869687930323020893617)
              ·
                refine ⟨7931902265947742265670213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10575869687930323020893617 7931902265947742265670213)
                ·
                  refine ⟨1487231674865201674813165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7931902265947742265670213 1487231674865201674813165)
                  ·
                    refine ⟨557711878074450628054937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1487231674865201674813165 557711878074450628054937)
                    ·
                      rfl

theorem cell22_1629210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_1629210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629210 prefixEnd_1629210 := by exact prefixLift 1629210
  have htrace : WordTrace (prefixWord ++ tailWord_1629210) baseStart_1629210 baseEnd_1629210 := by
    simpa [prefixWord, tailWord_1629210, baseEnd_1629210] using wordTrace_append hprefix tailTrace_1629210
  have hstable : (prefixWord ++ tailWord_1629210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629210).length < 2 ^ (prefixWord ++ tailWord_1629210).sum := by decide
  have hdescent : baseEnd_1629210 < baseStart_1629210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629244 : List Nat := [2, 2, 2, 2, 2, 3, 3, 1, 2, 3]
def baseStart_1629244 : Nat := 118140960795 + 1629244 * 2 ^ 59
def prefixEnd_1629244 : Nat := 4983230072969 + 3 ^ 40 * 1629244 * 2
def baseEnd_1629244 : Nat := 557723516969285872704833

theorem tailTrace_1629244 : CollatzResearch.WordTrace tailWord_1629244 prefixEnd_1629244 557723516969285872704833 := by
  unfold tailWord_1629244
  simp only [CollatzResearch.WordTrace]
  refine ⟨29711705254767357783739393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39615607006356477044985857 29711705254767357783739393)
  ·
    refine ⟨22283778941075518337804545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29711705254767357783739393 22283778941075518337804545)
    ·
      refine ⟨16712834205806638753353409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22283778941075518337804545 16712834205806638753353409)
      ·
        refine ⟨12534625654354979065015057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16712834205806638753353409 12534625654354979065015057)
        ·
          refine ⟨9400969240766234298761293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12534625654354979065015057 9400969240766234298761293)
          ·
            refine ⟨3525363465287337862035485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9400969240766234298761293 3525363465287337862035485)
            ·
              refine ⟨1322011299482751698263307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3525363465287337862035485 1322011299482751698263307)
              ·
                refine ⟨1983016949224127547394961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322011299482751698263307 1983016949224127547394961)
                ·
                  refine ⟨1487262711918095660546221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1983016949224127547394961 1487262711918095660546221)
                  ·
                    refine ⟨557723516969285872704833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1487262711918095660546221 557723516969285872704833)
                    ·
                      rfl

theorem cell22_1629244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_1629244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629244 prefixEnd_1629244 := by exact prefixLift 1629244
  have htrace : WordTrace (prefixWord ++ tailWord_1629244) baseStart_1629244 baseEnd_1629244 := by
    simpa [prefixWord, tailWord_1629244, baseEnd_1629244] using wordTrace_append hprefix tailTrace_1629244
  have hstable : (prefixWord ++ tailWord_1629244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629244).length < 2 ^ (prefixWord ++ tailWord_1629244).sum := by decide
  have hdescent : baseEnd_1629244 < baseStart_1629244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629253 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_1629253 : Nat := 118140960795 + 1629253 * 2 ^ 59
def prefixEnd_1629253 : Nat := 4983230072969 + 3 ^ 40 * 1629253 * 2
def baseEnd_1629253 : Nat := 557726597853212849229805

theorem tailTrace_1629253 : CollatzResearch.WordTrace tailWord_1629253 prefixEnd_1629253 557726597853212849229805 := by
  unfold tailWord_1629253
  simp only [CollatzResearch.WordTrace]
  refine ⟨59423738766502110104556413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39615825844334740069704275 59423738766502110104556413)
  ·
    refine ⟨22283902037438291289208655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59423738766502110104556413 22283902037438291289208655)
    ·
      refine ⟨33425853056157436933812983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22283902037438291289208655 33425853056157436933812983)
      ·
        refine ⟨50138779584236155400719475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33425853056157436933812983 50138779584236155400719475)
        ·
          refine ⟨75208169376354233101079213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50138779584236155400719475 75208169376354233101079213)
          ·
            refine ⟨28203063516132837412904705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75208169376354233101079213 28203063516132837412904705)
            ·
              refine ⟨21152297637099628059678529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28203063516132837412904705 21152297637099628059678529)
              ·
                refine ⟨15864223227824721044758897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21152297637099628059678529 15864223227824721044758897)
                ·
                  refine ⟨11898167420868540783569173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15864223227824721044758897 11898167420868540783569173)
                  ·
                    refine ⟨557726597853212849229805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11898167420868540783569173 557726597853212849229805)
                    ·
                      rfl

theorem cell22_1629253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_1629253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629253 prefixEnd_1629253 := by exact prefixLift 1629253
  have htrace : WordTrace (prefixWord ++ tailWord_1629253) baseStart_1629253 baseEnd_1629253 := by
    simpa [prefixWord, tailWord_1629253, baseEnd_1629253] using wordTrace_append hprefix tailTrace_1629253
  have hstable : (prefixWord ++ tailWord_1629253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629253).length < 2 ^ (prefixWord ++ tailWord_1629253).sum := by decide
  have hdescent : baseEnd_1629253 < baseStart_1629253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629285 : List Nat := [1, 3, 1, 3, 2, 1, 2, 4, 5]
def baseStart_1629285 : Nat := 118140960795 + 1629285 * 2 ^ 59
def prefixEnd_1629285 : Nat := 4983230072969 + 3 ^ 40 * 1629285 * 2
def baseEnd_1629285 : Nat := 185912517369058477476569

theorem tailTrace_1629285 : CollatzResearch.WordTrace tailWord_1629285 prefixEnd_1629285 185912517369058477476569 := by
  unfold tailWord_1629285
  simp only [CollatzResearch.WordTrace]
  refine ⟨59424905902386179569721309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39616603934924119713147539 59424905902386179569721309)
  ·
    refine ⟨22284339713394817338645491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59424905902386179569721309 22284339713394817338645491)
    ·
      refine ⟨33426509570092226007968237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22284339713394817338645491 33426509570092226007968237)
      ·
        refine ⟨12534941088784584752988089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33426509570092226007968237 12534941088784584752988089)
        ·
          refine ⟨9401205816588438564741067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12534941088784584752988089 9401205816588438564741067)
          ·
            refine ⟨14101808724882657847111601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9401205816588438564741067 14101808724882657847111601)
            ·
              refine ⟨10576356543661993385333701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14101808724882657847111601 10576356543661993385333701)
              ·
                refine ⟨1983066851936623759750069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10576356543661993385333701 1983066851936623759750069)
                ·
                  refine ⟨185912517369058477476569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1983066851936623759750069 185912517369058477476569)
                  ·
                    rfl

theorem cell22_1629285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_1629285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629285 prefixEnd_1629285 := by exact prefixLift 1629285
  have htrace : WordTrace (prefixWord ++ tailWord_1629285) baseStart_1629285 baseEnd_1629285 := by
    simpa [prefixWord, tailWord_1629285, baseEnd_1629285] using wordTrace_append hprefix tailTrace_1629285
  have hstable : (prefixWord ++ tailWord_1629285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629285).length < 2 ^ (prefixWord ++ tailWord_1629285).sum := by decide
  have hdescent : baseEnd_1629285 < baseStart_1629285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629302 : List Nat := [5, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_1629302 : Nat := 118140960795 + 1629302 * 2 ^ 59
def prefixEnd_1629302 : Nat := 4983230072969 + 3 ^ 40 * 1629302 * 2
def baseEnd_1629302 : Nat := 185914457184864351584885

theorem tailTrace_1629302 : CollatzResearch.WordTrace tailWord_1629302 prefixEnd_1629302 185914457184864351584885 := by
  unfold tailWord_1629302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3714095371457786967068135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39617017295549727648726773 3714095371457786967068135)
  ·
    refine ⟨5571143057186680450602203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3714095371457786967068135 5571143057186680450602203)
    ·
      refine ⟨8356714585780020675903305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5571143057186680450602203 8356714585780020675903305)
      ·
        refine ⟨6267535939335015506927479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8356714585780020675903305 6267535939335015506927479)
        ·
          refine ⟨9401303909002523260391219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6267535939335015506927479 9401303909002523260391219)
          ·
            refine ⟨14101955863503784890586829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9401303909002523260391219 14101955863503784890586829)
            ·
              refine ⟨5288233448813919333970061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14101955863503784890586829 5288233448813919333970061)
              ·
                refine ⟨1983087543305219750238773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5288233448813919333970061 1983087543305219750238773)
                ·
                  refine ⟨185914457184864351584885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1983087543305219750238773 185914457184864351584885)
                  ·
                    rfl

theorem cell22_1629302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_1629302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629302 prefixEnd_1629302 := by exact prefixLift 1629302
  have htrace : WordTrace (prefixWord ++ tailWord_1629302) baseStart_1629302 baseEnd_1629302 := by
    simpa [prefixWord, tailWord_1629302, baseEnd_1629302] using wordTrace_append hprefix tailTrace_1629302
  have hstable : (prefixWord ++ tailWord_1629302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629302).length < 2 ^ (prefixWord ++ tailWord_1629302).sum := by decide
  have hdescent : baseEnd_1629302 < baseStart_1629302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629315 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 3, 4]
def baseStart_1629315 : Nat := 118140960795 + 1629315 * 2 ^ 59
def prefixEnd_1629315 : Nat := 4983230072969 + 3 ^ 40 * 1629315 * 2
def baseEnd_1629315 : Nat := 557747821720265354179615

theorem tailTrace_1629315 : CollatzResearch.WordTrace tailWord_1629315 prefixEnd_1629315 557747821720265354179615 := by
  unfold tailWord_1629315
  simp only [CollatzResearch.WordTrace]
  refine ⟨59426000092277494693313399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39617333394851663128875599 59426000092277494693313399)
  ·
    refine ⟨89139000138416242039970099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59426000092277494693313399 89139000138416242039970099)
    ·
      refine ⟨133708500207624363059955149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89139000138416242039970099 133708500207624363059955149)
      ·
        refine ⟨50140687577859136147483181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133708500207624363059955149 50140687577859136147483181)
        ·
          refine ⟨18802757841697176055306193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50140687577859136147483181 18802757841697176055306193)
          ·
            refine ⟨14102068381272882041479645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18802757841697176055306193 14102068381272882041479645)
            ·
              refine ⟨5288275642977330765554867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14102068381272882041479645 5288275642977330765554867)
              ·
                refine ⟨7932413464465996148332301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5288275642977330765554867 7932413464465996148332301)
                ·
                  refine ⟨2974655049174748555624613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7932413464465996148332301 2974655049174748555624613)
                  ·
                    refine ⟨557747821720265354179615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2974655049174748555624613 557747821720265354179615)
                    ·
                      rfl

theorem cell22_1629315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 4].length) (baseStart_1629315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629315 prefixEnd_1629315 := by exact prefixLift 1629315
  have htrace : WordTrace (prefixWord ++ tailWord_1629315) baseStart_1629315 baseEnd_1629315 := by
    simpa [prefixWord, tailWord_1629315, baseEnd_1629315] using wordTrace_append hprefix tailTrace_1629315
  have hstable : (prefixWord ++ tailWord_1629315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629315).length < 2 ^ (prefixWord ++ tailWord_1629315).sum := by decide
  have hdescent : baseEnd_1629315 < baseStart_1629315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629345 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 3, 5]
def baseStart_1629345 : Nat := 118140960795 + 1629345 * 2 ^ 59
def prefixEnd_1629345 : Nat := 4983230072969 + 3 ^ 40 * 1629345 * 2
def baseEnd_1629345 : Nat := 557758091333355275929523

theorem tailTrace_1629345 : CollatzResearch.WordTrace tailWord_1629345 prefixEnd_1629345 557758091333355275929523 := by
  unfold tailWord_1629345
  simp only [CollatzResearch.WordTrace]
  refine ⟨59427094282168809816905489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39618062854779206544603659 59427094282168809816905489)
  ·
    refine ⟨44570320711626607362679117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59427094282168809816905489 44570320711626607362679117)
    ·
      refine ⟨16713870266859977761004669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44570320711626607362679117 16713870266859977761004669)
      ·
        refine ⟨6267701350072491660376751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16713870266859977761004669 6267701350072491660376751)
        ·
          refine ⟨9401552025108737490565127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6267701350072491660376751 9401552025108737490565127)
          ·
            refine ⟨14102328037663106235847691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9401552025108737490565127 14102328037663106235847691)
            ·
              refine ⟨21153492056494659353771537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14102328037663106235847691 21153492056494659353771537)
              ·
                refine ⟨15865119042370994515328653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21153492056494659353771537 15865119042370994515328653)
                ·
                  refine ⟨5949419640889122943248245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15865119042370994515328653 5949419640889122943248245)
                  ·
                    refine ⟨557758091333355275929523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5949419640889122943248245 557758091333355275929523)
                    ·
                      rfl

theorem cell22_1629345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_1629345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629345 prefixEnd_1629345 := by exact prefixLift 1629345
  have htrace : WordTrace (prefixWord ++ tailWord_1629345) baseStart_1629345 baseEnd_1629345 := by
    simpa [prefixWord, tailWord_1629345, baseEnd_1629345] using wordTrace_append hprefix tailTrace_1629345
  have hstable : (prefixWord ++ tailWord_1629345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629345).length < 2 ^ (prefixWord ++ tailWord_1629345).sum := by decide
  have hdescent : baseEnd_1629345 < baseStart_1629345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629362 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_1629362 : Nat := 118140960795 + 1629362 * 2 ^ 59
def prefixEnd_1629362 : Nat := 4983230072969 + 3 ^ 40 * 1629362 * 2
def baseEnd_1629362 : Nat := 557763910780772898254471

theorem tailTrace_1629362 : CollatzResearch.WordTrace tailWord_1629362 prefixEnd_1629362 557763910780772898254471 := by
  unfold tailWord_1629362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14856928580776805430068585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39618476215404814480182893 14856928580776805430068585)
  ·
    refine ⟨11142696435582604072551439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14856928580776805430068585 11142696435582604072551439)
    ·
      refine ⟨16714044653373906108827159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11142696435582604072551439 16714044653373906108827159)
      ·
        refine ⟨25071066980060859163240739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16714044653373906108827159 25071066980060859163240739)
        ·
          refine ⟨37606600470091288744861109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25071066980060859163240739 37606600470091288744861109)
          ·
            refine ⟨3525618794071058319830729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37606600470091288744861109 3525618794071058319830729)
            ·
              refine ⟨2644214095553293739873047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3525618794071058319830729 2644214095553293739873047)
              ·
                refine ⟨3966321143329940609809571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644214095553293739873047 3966321143329940609809571)
                ·
                  refine ⟨5949481714994910914714357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966321143329940609809571 5949481714994910914714357)
                  ·
                    refine ⟨557763910780772898254471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5949481714994910914714357 557763910780772898254471)
                    ·
                      rfl

theorem cell22_1629362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_1629362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629362 prefixEnd_1629362 := by exact prefixLift 1629362
  have htrace : WordTrace (prefixWord ++ tailWord_1629362) baseStart_1629362 baseEnd_1629362 := by
    simpa [prefixWord, tailWord_1629362, baseEnd_1629362] using wordTrace_append hprefix tailTrace_1629362
  have hstable : (prefixWord ++ tailWord_1629362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629362).length < 2 ^ (prefixWord ++ tailWord_1629362).sum := by decide
  have hdescent : baseEnd_1629362 < baseStart_1629362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629396 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_1629396 : Nat := 118140960795 + 1629396 * 2 ^ 59
def prefixEnd_1629396 : Nat := 4983230072969 + 3 ^ 40 * 1629396 * 2
def baseEnd_1629396 : Nat := 557775549675608142904367

theorem tailTrace_1629396 : CollatzResearch.WordTrace tailWord_1629396 prefixEnd_1629396 557775549675608142904367 := by
  unfold tailWord_1629396
  simp only [CollatzResearch.WordTrace]
  refine ⟨29714477202492022763506021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39619302936656030351341361 29714477202492022763506021)
  ·
    refine ⟨5571464475467254268157379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29714477202492022763506021 5571464475467254268157379)
    ·
      refine ⟨8357196713200881402236069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5571464475467254268157379 8357196713200881402236069)
      ·
        refine ⟨1566974383725165262919263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8357196713200881402236069 1566974383725165262919263)
        ·
          refine ⟨2350461575587747894378895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566974383725165262919263 2350461575587747894378895)
          ·
            refine ⟨3525692363381621841568343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350461575587747894378895 3525692363381621841568343)
            ·
              refine ⟨5288538545072432762352515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3525692363381621841568343 5288538545072432762352515)
              ·
                refine ⟨7932807817608649143528773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5288538545072432762352515 7932807817608649143528773)
                ·
                  refine ⟨1487401465801621714411645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7932807817608649143528773 1487401465801621714411645)
                  ·
                    refine ⟨557775549675608142904367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1487401465801621714411645 557775549675608142904367)
                    ·
                      rfl

theorem cell22_1629396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_1629396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629396 prefixEnd_1629396 := by exact prefixLift 1629396
  have htrace : WordTrace (prefixWord ++ tailWord_1629396) baseStart_1629396 baseEnd_1629396 := by
    simpa [prefixWord, tailWord_1629396, baseEnd_1629396] using wordTrace_append hprefix tailTrace_1629396
  have hstable : (prefixWord ++ tailWord_1629396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629396).length < 2 ^ (prefixWord ++ tailWord_1629396).sum := by decide
  have hdescent : baseEnd_1629396 < baseStart_1629396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629407 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 3, 3]
def baseStart_1629407 : Nat := 118140960795 + 1629407 * 2 ^ 59
def prefixEnd_1629407 : Nat := 4983230072969 + 3 ^ 40 * 1629407 * 2
def baseEnd_1629407 : Nat := 557779315200407780879333

theorem tailTrace_1629407 : CollatzResearch.WordTrace tailWord_1629407 prefixEnd_1629407 557779315200407780879333 := by
  unfold tailWord_1629407
  simp only [CollatzResearch.WordTrace]
  refine ⟨59429355607944194405662475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39619570405296129603774983 59429355607944194405662475)
  ·
    refine ⟨89144033411916291608493713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59429355607944194405662475 89144033411916291608493713)
    ·
      refine ⟨66858025058937218706370285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89144033411916291608493713 66858025058937218706370285)
      ·
        refine ⟨25071759397101457014888857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66858025058937218706370285 25071759397101457014888857)
        ·
          refine ⟨18803819547826092761166643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25071759397101457014888857 18803819547826092761166643)
          ·
            refine ⟨28205729321739139141749965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18803819547826092761166643 28205729321739139141749965)
            ·
              refine ⟨10577148495652177178156237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28205729321739139141749965 10577148495652177178156237)
              ·
                refine ⟨3966430685869566441808589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10577148495652177178156237 3966430685869566441808589)
                ·
                  refine ⟨1487411507201087415678221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3966430685869566441808589 1487411507201087415678221)
                  ·
                    refine ⟨557779315200407780879333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1487411507201087415678221 557779315200407780879333)
                    ·
                      rfl

theorem cell22_1629407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 3].length) (baseStart_1629407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629407 prefixEnd_1629407 := by exact prefixLift 1629407
  have htrace : WordTrace (prefixWord ++ tailWord_1629407) baseStart_1629407 baseEnd_1629407 := by
    simpa [prefixWord, tailWord_1629407, baseEnd_1629407] using wordTrace_append hprefix tailTrace_1629407
  have hstable : (prefixWord ++ tailWord_1629407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629407).length < 2 ^ (prefixWord ++ tailWord_1629407).sum := by decide
  have hdescent : baseEnd_1629407 < baseStart_1629407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629426 : List Nat := [3, 2, 1, 3, 4, 1, 2, 6]
def baseStart_1629426 : Nat := 118140960795 + 1629426 * 2 ^ 59
def prefixEnd_1629426 : Nat := 4983230072969 + 3 ^ 40 * 1629426 * 2
def baseEnd_1629426 : Nat := 61976202143188673850475

theorem tailTrace_1629426 : CollatzResearch.WordTrace tailWord_1629426 prefixEnd_1629426 61976202143188673850475 := by
  unfold tailWord_1629426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14857512148718840162651033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39620032396583573767069421 14857512148718840162651033)
  ·
    refine ⟨11143134111539130121988275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14857512148718840162651033 11143134111539130121988275)
    ·
      refine ⟨16714701167308695182982413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11143134111539130121988275 16714701167308695182982413)
      ·
        refine ⟨6268012937740760693618405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16714701167308695182982413 6268012937740760693618405)
        ·
          refine ⟨1175252425826392630053451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6268012937740760693618405 1175252425826392630053451)
          ·
            refine ⟨1762878638739588945080177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175252425826392630053451 1762878638739588945080177)
            ·
              refine ⟨1322158979054691708810133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1762878638739588945080177 1322158979054691708810133)
              ·
                refine ⟨61976202143188673850475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1322158979054691708810133 61976202143188673850475)
                ·
                  rfl

theorem cell22_1629426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_1629426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629426 prefixEnd_1629426 := by exact prefixLift 1629426
  have htrace : WordTrace (prefixWord ++ tailWord_1629426) baseStart_1629426 baseEnd_1629426 := by
    simpa [prefixWord, tailWord_1629426, baseEnd_1629426] using wordTrace_append hprefix tailTrace_1629426
  have hstable : (prefixWord ++ tailWord_1629426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629426).length < 2 ^ (prefixWord ++ tailWord_1629426).sum := by decide
  have hdescent : baseEnd_1629426 < baseStart_1629426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629441 : List Nat := [1, 2, 4, 1, 1, 3, 3, 3, 1, 3]
def baseStart_1629441 : Nat := 118140960795 + 1629441 * 2 ^ 59
def prefixEnd_1629441 : Nat := 4983230072969 + 3 ^ 40 * 1629441 * 2
def baseEnd_1629441 : Nat := 557790954095243025529229

theorem tailTrace_1629441 : CollatzResearch.WordTrace tailWord_1629441 prefixEnd_1629441 557790954095243025529229 := by
  unfold tailWord_1629441
  simp only [CollatzResearch.WordTrace]
  refine ⟨59430595689821018212400177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39620397126547345474933451 59430595689821018212400177)
  ·
    refine ⟨44572946767365763659300133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59430595689821018212400177 44572946767365763659300133)
    ·
      refine ⟨8357427518881080686118775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44572946767365763659300133 8357427518881080686118775)
      ·
        refine ⟨12536141278321621029178163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8357427518881080686118775 12536141278321621029178163)
        ·
          refine ⟨18804211917482431543767245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12536141278321621029178163 18804211917482431543767245)
          ·
            refine ⟨7051579469055911828912717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18804211917482431543767245 7051579469055911828912717)
            ·
              refine ⟨2644342300895966935842269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7051579469055911828912717 2644342300895966935842269)
              ·
                refine ⟨991628362835987600940851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2644342300895966935842269 991628362835987600940851)
                ·
                  refine ⟨1487442544253981401411277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991628362835987600940851 1487442544253981401411277)
                  ·
                    refine ⟨557790954095243025529229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1487442544253981401411277 557790954095243025529229)
                    ·
                      rfl

theorem cell22_1629441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_1629441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629441 prefixEnd_1629441 := by exact prefixLift 1629441
  have htrace : WordTrace (prefixWord ++ tailWord_1629441) baseStart_1629441 baseEnd_1629441 := by
    simpa [prefixWord, tailWord_1629441, baseEnd_1629441] using wordTrace_append hprefix tailTrace_1629441
  have hstable : (prefixWord ++ tailWord_1629441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629441).length < 2 ^ (prefixWord ++ tailWord_1629441).sum := by decide
  have hdescent : baseEnd_1629441 < baseStart_1629441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629471 : List Nat := [1, 1, 2, 4, 4, 2, 2, 1, 5]
def baseStart_1629471 : Nat := 118140960795 + 1629471 * 2 ^ 59
def prefixEnd_1629471 : Nat := 4983230072969 + 3 ^ 40 * 1629471 * 2
def baseEnd_1629471 : Nat := 185933741236110982426379

theorem tailTrace_1629471 : CollatzResearch.WordTrace tailWord_1629471 prefixEnd_1629471 185933741236110982426379 := by
  unfold tailWord_1629471
  simp only [CollatzResearch.WordTrace]
  refine ⟨59431689879712333335992267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39621126586474888890661511 59431689879712333335992267)
  ·
    refine ⟨89147534819568500003988401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59431689879712333335992267 89147534819568500003988401)
    ·
      refine ⟨66860651114676375002991301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89147534819568500003988401 66860651114676375002991301)
      ·
        refine ⟨12536372084001820313060869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66860651114676375002991301 12536372084001820313060869)
        ·
          refine ⟨2350569765750341308698913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12536372084001820313060869 2350569765750341308698913)
          ·
            refine ⟨1762927324312755981524185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2350569765750341308698913 1762927324312755981524185)
            ·
              refine ⟨1322195493234566986143139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1762927324312755981524185 1322195493234566986143139)
              ·
                refine ⟨1983293239851850479214709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322195493234566986143139 1983293239851850479214709)
                ·
                  refine ⟨185933741236110982426379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1983293239851850479214709 185933741236110982426379)
                  ·
                    rfl

theorem cell22_1629471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 5].length) (baseStart_1629471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629471 prefixEnd_1629471 := by exact prefixLift 1629471
  have htrace : WordTrace (prefixWord ++ tailWord_1629471) baseStart_1629471 baseEnd_1629471 := by
    simpa [prefixWord, tailWord_1629471, baseEnd_1629471] using wordTrace_append hprefix tailTrace_1629471
  have hstable : (prefixWord ++ tailWord_1629471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629471).length < 2 ^ (prefixWord ++ tailWord_1629471).sum := by decide
  have hdescent : baseEnd_1629471 < baseStart_1629471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629516 : List Nat := [2, 2, 1, 3, 2, 2, 4, 2, 4]
def baseStart_1629516 : Nat := 118140960795 + 1629516 * 2 ^ 59
def prefixEnd_1629516 : Nat := 4983230072969 + 3 ^ 40 * 1629516 * 2
def baseEnd_1629516 : Nat := 185938876042655943301333

theorem tailTrace_1629516 : CollatzResearch.WordTrace tailWord_1629516 prefixEnd_1629516 185938876042655943301333 := by
  unfold tailWord_1629516
  simp only [CollatzResearch.WordTrace]
  refine ⟨29716665582274653010690201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39622220776366204014253601 29716665582274653010690201)
  ·
    refine ⟨22287499186705989758017651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29716665582274653010690201 22287499186705989758017651)
    ·
      refine ⟨33431248780058984637026477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22287499186705989758017651 33431248780058984637026477)
      ·
        refine ⟨12536718292522119238884929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33431248780058984637026477 12536718292522119238884929)
        ·
          refine ⟨9402538719391589429163697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12536718292522119238884929 9402538719391589429163697)
          ·
            refine ⟨7051904039543692071872773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9402538719391589429163697 7051904039543692071872773)
            ·
              refine ⟨1322232007414442263476145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7051904039543692071872773 1322232007414442263476145)
              ·
                refine ⟨991674005560831697607109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322232007414442263476145 991674005560831697607109)
                ·
                  refine ⟨185938876042655943301333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 991674005560831697607109 185938876042655943301333)
                  ·
                    rfl

theorem cell22_1629516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_1629516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629516 prefixEnd_1629516 := by exact prefixLift 1629516
  have htrace : WordTrace (prefixWord ++ tailWord_1629516) baseStart_1629516 baseEnd_1629516 := by
    simpa [prefixWord, tailWord_1629516, baseEnd_1629516] using wordTrace_append hprefix tailTrace_1629516
  have hstable : (prefixWord ++ tailWord_1629516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629516).length < 2 ^ (prefixWord ++ tailWord_1629516).sum := by decide
  have hdescent : baseEnd_1629516 < baseStart_1629516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629527 : List Nat := [1, 1, 3, 2, 3, 2, 3, 7]
def baseStart_1629527 : Nat := 118140960795 + 1629527 * 2 ^ 59
def prefixEnd_1629527 : Nat := 4983230072969 + 3 ^ 40 * 1629527 * 2
def baseEnd_1629527 : Nat := 61980043739196385319885

theorem tailTrace_1629527 : CollatzResearch.WordTrace tailWord_1629527 prefixEnd_1629527 61980043739196385319885 := by
  unfold tailWord_1629527
  simp only [CollatzResearch.WordTrace]
  refine ⟨59433732367509454900030835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39622488245006303266687223 59433732367509454900030835)
  ·
    refine ⟨89150598551264182350046253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59433732367509454900030835 89150598551264182350046253)
    ·
      refine ⟨33431474456724068381267345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89150598551264182350046253 33431474456724068381267345)
      ·
        refine ⟨25073605842543051285950509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33431474456724068381267345 25073605842543051285950509)
        ·
          refine ⟨9402602190953644232231441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25073605842543051285950509 9402602190953644232231441)
          ·
            refine ⟨7051951643215233174173581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9402602190953644232231441 7051951643215233174173581)
            ·
              refine ⟨2644481866205712440315093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7051951643215233174173581 2644481866205712440315093)
              ·
                refine ⟨61980043739196385319885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2644481866205712440315093 61980043739196385319885)
                ·
                  rfl

theorem cell22_1629527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 7].length) (baseStart_1629527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629527 prefixEnd_1629527 := by exact prefixLift 1629527
  have htrace : WordTrace (prefixWord ++ tailWord_1629527) baseStart_1629527 baseEnd_1629527 := by
    simpa [prefixWord, tailWord_1629527, baseEnd_1629527] using wordTrace_append hprefix tailTrace_1629527
  have hstable : (prefixWord ++ tailWord_1629527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629527).length < 2 ^ (prefixWord ++ tailWord_1629527).sum := by decide
  have hdescent : baseEnd_1629527 < baseStart_1629527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629533 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 6]
def baseStart_1629533 : Nat := 118140960795 + 1629533 * 2 ^ 59
def prefixEnd_1629533 : Nat := 4983230072969 + 3 ^ 40 * 1629533 * 2
def baseEnd_1629533 : Nat := 185940815858461817409649

theorem tailTrace_1629533 : CollatzResearch.WordTrace tailWord_1629533 prefixEnd_1629533 185940815858461817409649 := by
  unfold tailWord_1629533
  simp only [CollatzResearch.WordTrace]
  refine ⟨59433951205487717924749253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39622634136991811949832835 59433951205487717924749253)
  ·
    refine ⟨11143865851028947110890485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59433951205487717924749253 11143865851028947110890485)
    ·
      refine ⟨1044737423533963791645983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11143865851028947110890485 1044737423533963791645983)
      ·
        refine ⟨1567106135300945687468975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044737423533963791645983 1567106135300945687468975)
        ·
          refine ⟨2350659202951418531203463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567106135300945687468975 2350659202951418531203463)
          ·
            refine ⟨3525988804427127796805195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350659202951418531203463 3525988804427127796805195)
            ·
              refine ⟨5288983206640691695207793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3525988804427127796805195 5288983206640691695207793)
              ·
                refine ⟨3966737404980518771405845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5288983206640691695207793 3966737404980518771405845)
                ·
                  refine ⟨185940815858461817409649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3966737404980518771405845 185940815858461817409649)
                  ·
                    rfl

theorem cell22_1629533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_1629533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629533 prefixEnd_1629533 := by exact prefixLift 1629533
  have htrace : WordTrace (prefixWord ++ tailWord_1629533) baseStart_1629533 baseEnd_1629533 := by
    simpa [prefixWord, tailWord_1629533, baseEnd_1629533] using wordTrace_append hprefix tailTrace_1629533
  have hstable : (prefixWord ++ tailWord_1629533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629533).length < 2 ^ (prefixWord ++ tailWord_1629533).sum := by decide
  have hdescent : baseEnd_1629533 < baseStart_1629533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629576 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 3, 3]
def baseStart_1629576 : Nat := 118140960795 + 1629576 * 2 ^ 59
def prefixEnd_1629576 : Nat := 4983230072969 + 3 ^ 40 * 1629576 * 2
def baseEnd_1629576 : Nat := 557837167354147673403815

theorem tailTrace_1629576 : CollatzResearch.WordTrace tailWord_1629576 prefixEnd_1629576 557837167354147673403815 := by
  unfold tailWord_1629576
  simp only [CollatzResearch.WordTrace]
  refine ⟨29717759772165968134282291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39623679696221290845709721 29717759772165968134282291)
  ·
    refine ⟨44576639658248952201423437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29717759772165968134282291 44576639658248952201423437)
    ·
      refine ⟨16716239871843357075533789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44576639658248952201423437 16716239871843357075533789)
      ·
        refine ⟨6268589951941258903325171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16716239871843357075533789 6268589951941258903325171)
        ·
          refine ⟨9402884927911888354987757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6268589951941258903325171 9402884927911888354987757)
          ·
            refine ⟨3526081847966958133120409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9402884927911888354987757 3526081847966958133120409)
            ·
              refine ⟨2644561385975218599840307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3526081847966958133120409 2644561385975218599840307)
              ·
                refine ⟨3966842078962827899760461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2644561385975218599840307 3966842078962827899760461)
                ·
                  refine ⟨1487565779611060462410173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3966842078962827899760461 1487565779611060462410173)
                  ·
                    refine ⟨557837167354147673403815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1487565779611060462410173 557837167354147673403815)
                    ·
                      rfl

theorem cell22_1629576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_1629576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629576 prefixEnd_1629576 := by exact prefixLift 1629576
  have htrace : WordTrace (prefixWord ++ tailWord_1629576) baseStart_1629576 baseEnd_1629576 := by
    simpa [prefixWord, tailWord_1629576, baseEnd_1629576] using wordTrace_append hprefix tailTrace_1629576
  have hstable : (prefixWord ++ tailWord_1629576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629576).length < 2 ^ (prefixWord ++ tailWord_1629576).sum := by decide
  have hdescent : baseEnd_1629576 < baseStart_1629576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629647 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 3, 6]
def baseStart_1629647 : Nat := 118140960795 + 1629647 * 2 ^ 59
def prefixEnd_1629647 : Nat := 4983230072969 + 3 ^ 40 * 1629647 * 2
def baseEnd_1629647 : Nat := 557861472105127154878597

theorem tailTrace_1629647 : CollatzResearch.WordTrace tailWord_1629647 prefixEnd_1629647 557861472105127154878597 := by
  unfold tailWord_1629647
  simp only [CollatzResearch.WordTrace]
  refine ⟨59438109127074715394399195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39625406084716476929599463 59438109127074715394399195)
  ·
    refine ⟨89157163690612073091598793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59438109127074715394399195 89157163690612073091598793)
    ·
      refine ⟨66867872767959054818699095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89157163690612073091598793 66867872767959054818699095)
      ·
        refine ⟨100301809151938582228048643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66867872767959054818699095 100301809151938582228048643)
        ·
          refine ⟨150452713727907873342072965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100301809151938582228048643 150452713727907873342072965)
          ·
            refine ⟨28209883823982726251638681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150452713727907873342072965 28209883823982726251638681)
            ·
              refine ⟨21157412867987044688729011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28209883823982726251638681 21157412867987044688729011)
              ·
                refine ⟨31736119301980567033093517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21157412867987044688729011 31736119301980567033093517)
                ·
                  refine ⟨11901044738242712637410069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31736119301980567033093517 11901044738242712637410069)
                  ·
                    refine ⟨557861472105127154878597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11901044738242712637410069 557861472105127154878597)
                    ·
                      rfl

theorem cell22_1629647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_1629647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629647 prefixEnd_1629647 := by exact prefixLift 1629647
  have htrace : WordTrace (prefixWord ++ tailWord_1629647) baseStart_1629647 baseEnd_1629647 := by
    simpa [prefixWord, tailWord_1629647, baseEnd_1629647] using wordTrace_append hprefix tailTrace_1629647
  have hstable : (prefixWord ++ tailWord_1629647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629647).length < 2 ^ (prefixWord ++ tailWord_1629647).sum := by decide
  have hdescent : baseEnd_1629647 < baseStart_1629647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629685 : List Nat := [1, 3, 5, 1, 1, 1, 4, 2, 4]
def baseStart_1629685 : Nat := 118140960795 + 1629685 * 2 ^ 59
def prefixEnd_1629685 : Nat := 4983230072969 + 3 ^ 40 * 1629685 * 2
def baseEnd_1629685 : Nat := 185958160093902574142827

theorem tailTrace_1629685 : CollatzResearch.WordTrace tailWord_1629685 prefixEnd_1629685 185958160093902574142827 := by
  unfold tailWord_1629685
  simp only [CollatzResearch.WordTrace]
  refine ⟨59439495100937047884282509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39626330067291365256188339 59439495100937047884282509)
  ·
    refine ⟨22289810662851392956605941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59439495100937047884282509 22289810662851392956605941)
    ·
      refine ⟨2089669749642318089681807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22289810662851392956605941 2089669749642318089681807)
      ·
        refine ⟨3134504624463477134522711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2089669749642318089681807 3134504624463477134522711)
        ·
          refine ⟨4701756936695215701784067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3134504624463477134522711 4701756936695215701784067)
          ·
            refine ⟨7052635405042823552676101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701756936695215701784067 7052635405042823552676101)
            ·
              refine ⟨1322369138445529416126769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7052635405042823552676101 1322369138445529416126769)
              ·
                refine ⟨991776853834147062095077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322369138445529416126769 991776853834147062095077)
                ·
                  refine ⟨185958160093902574142827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 991776853834147062095077 185958160093902574142827)
                  ·
                    rfl

theorem cell22_1629685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_1629685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629685 prefixEnd_1629685 := by exact prefixLift 1629685
  have htrace : WordTrace (prefixWord ++ tailWord_1629685) baseStart_1629685 baseEnd_1629685 := by
    simpa [prefixWord, tailWord_1629685, baseEnd_1629685] using wordTrace_append hprefix tailTrace_1629685
  have hstable : (prefixWord ++ tailWord_1629685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629685).length < 2 ^ (prefixWord ++ tailWord_1629685).sum := by decide
  have hdescent : baseEnd_1629685 < baseStart_1629685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629724 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 7]
def baseStart_1629724 : Nat := 118140960795 + 1629724 * 2 ^ 59
def prefixEnd_1629724 : Nat := 4983230072969 + 3 ^ 40 * 1629724 * 2
def baseEnd_1629724 : Nat := 185962610259574873567787

theorem tailTrace_1629724 : CollatzResearch.WordTrace tailWord_1629724 prefixEnd_1629724 185962610259574873567787 := by
  unfold tailWord_1629724
  simp only [CollatzResearch.WordTrace]
  refine ⟨29720458773897878772476113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39627278365197171696634817 29720458773897878772476113)
  ·
    refine ⟨22290344080423409079357085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29720458773897878772476113 22290344080423409079357085)
    ·
      refine ⟨8358879030158778404758907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22290344080423409079357085 8358879030158778404758907)
      ·
        refine ⟨12538318545238167607138361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8358879030158778404758907 12538318545238167607138361)
        ·
          refine ⟨9403738908928625705353771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12538318545238167607138361 9403738908928625705353771)
          ·
            refine ⟨14105608363392938558030657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9403738908928625705353771 14105608363392938558030657)
            ·
              refine ⟨10579206272544703918522993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14105608363392938558030657 10579206272544703918522993)
              ·
                refine ⟨7934404704408527938892245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10579206272544703918522993 7934404704408527938892245)
                ·
                  refine ⟨185962610259574873567787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7934404704408527938892245 185962610259574873567787)
                  ·
                    rfl

theorem cell22_1629724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_1629724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629724 prefixEnd_1629724 := by exact prefixLift 1629724
  have htrace : WordTrace (prefixWord ++ tailWord_1629724) baseStart_1629724 baseEnd_1629724 := by
    simpa [prefixWord, tailWord_1629724, baseEnd_1629724] using wordTrace_append hprefix tailTrace_1629724
  have hstable : (prefixWord ++ tailWord_1629724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629724).length < 2 ^ (prefixWord ++ tailWord_1629724).sum := by decide
  have hdescent : baseEnd_1629724 < baseStart_1629724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629784 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 3, 5]
def baseStart_1629784 : Nat := 118140960795 + 1629784 * 2 ^ 59
def prefixEnd_1629784 : Nat := 4983230072969 + 3 ^ 40 * 1629784 * 2
def baseEnd_1629784 : Nat := 557908370004904464203177

theorem tailTrace_1629784 : CollatzResearch.WordTrace tailWord_1629784 prefixEnd_1629784 557908370004904464203177 := by
  unfold tailWord_1629784
  simp only [CollatzResearch.WordTrace]
  refine ⟨29721552963789193896068203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39628737285052258528090937 29721552963789193896068203)
  ·
    refine ⟨44582329445683790844102305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29721552963789193896068203 44582329445683790844102305)
    ·
      refine ⟨33436747084262843133076729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44582329445683790844102305 33436747084262843133076729)
      ·
        refine ⟨25077560313197132349807547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33436747084262843133076729 25077560313197132349807547)
        ·
          refine ⟨37616340469795698524711321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25077560313197132349807547 37616340469795698524711321)
          ·
            refine ⟨28212255352346773893533491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37616340469795698524711321 28212255352346773893533491)
            ·
              refine ⟨42318383028520160840300237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28212255352346773893533491 42318383028520160840300237)
              ·
                refine ⟨15869393635695060315112589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42318383028520160840300237 15869393635695060315112589)
                ·
                  refine ⟨5951022613385647618167221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15869393635695060315112589 5951022613385647618167221)
                  ·
                    refine ⟨557908370004904464203177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5951022613385647618167221 557908370004904464203177)
                    ·
                      rfl

theorem cell22_1629784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_1629784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629784 prefixEnd_1629784 := by exact prefixLift 1629784
  have htrace : WordTrace (prefixWord ++ tailWord_1629784) baseStart_1629784 baseEnd_1629784 := by
    simpa [prefixWord, tailWord_1629784, baseEnd_1629784] using wordTrace_append hprefix tailTrace_1629784
  have hstable : (prefixWord ++ tailWord_1629784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629784).length < 2 ^ (prefixWord ++ tailWord_1629784).sum := by decide
  have hdescent : baseEnd_1629784 < baseStart_1629784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629788 : List Nat := [2, 2, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1629788 : Nat := 118140960795 + 1629788 * 2 ^ 59
def prefixEnd_1629788 : Nat := 4983230072969 + 3 ^ 40 * 1629788 * 2
def baseEnd_1629788 : Nat := 557909739286649787103165

theorem tailTrace_1629788 : CollatzResearch.WordTrace tailWord_1629788 prefixEnd_1629788 557909739286649787103165 := by
  unfold tailWord_1629788
  simp only [CollatzResearch.WordTrace]
  refine ⟨29721625909781948237641009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39628834546375930983521345 29721625909781948237641009)
  ·
    refine ⟨22291219432336461178230757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29721625909781948237641009 22291219432336461178230757)
    ·
      refine ⟨4179603643563086470918267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22291219432336461178230757 4179603643563086470918267)
      ·
        refine ⟨6269405465344629706377401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4179603643563086470918267 6269405465344629706377401)
        ·
          refine ⟨4702054099008472279783051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6269405465344629706377401 4702054099008472279783051)
          ·
            refine ⟨7053081148512708419674577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4702054099008472279783051 7053081148512708419674577)
            ·
              refine ⟨5289810861384531314755933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7053081148512708419674577 5289810861384531314755933)
              ·
                refine ⟨1983679073019199243033475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5289810861384531314755933 1983679073019199243033475)
                ·
                  refine ⟨2975518609528798864550213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983679073019199243033475 2975518609528798864550213)
                  ·
                    refine ⟨557909739286649787103165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2975518609528798864550213 557909739286649787103165)
                    ·
                      rfl

theorem cell22_1629788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1629788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629788 prefixEnd_1629788 := by exact prefixLift 1629788
  have htrace : WordTrace (prefixWord ++ tailWord_1629788) baseStart_1629788 baseEnd_1629788 := by
    simpa [prefixWord, tailWord_1629788, baseEnd_1629788] using wordTrace_append hprefix tailTrace_1629788
  have hstable : (prefixWord ++ tailWord_1629788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629788).length < 2 ^ (prefixWord ++ tailWord_1629788).sum := by decide
  have hdescent : baseEnd_1629788 < baseStart_1629788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629801 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 4, 3]
def baseStart_1629801 : Nat := 118140960795 + 1629801 * 2 ^ 59
def prefixEnd_1629801 : Nat := 4983230072969 + 3 ^ 40 * 1629801 * 2
def baseEnd_1629801 : Nat := 557914189452322086528125

theorem tailTrace_1629801 : CollatzResearch.WordTrace tailWord_1629801 prefixEnd_1629801 557914189452322086528125 := by
  unfold tailWord_1629801
  simp only [CollatzResearch.WordTrace]
  refine ⟨59443725968516799695505257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39629150645677866463670171 59443725968516799695505257)
  ·
    refine ⟨44582794476387599771628943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59443725968516799695505257 44582794476387599771628943)
    ·
      refine ⟨66874191714581399657443415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44582794476387599771628943 66874191714581399657443415)
      ·
        refine ⟨100311287571872099486165123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66874191714581399657443415 100311287571872099486165123)
        ·
          refine ⟨150466931357808149229247685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100311287571872099486165123 150466931357808149229247685)
          ·
            refine ⟨28212549629589027980483941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150466931357808149229247685 28212549629589027980483941)
            ·
              refine ⟨5289853055547942746340739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28212549629589027980483941 5289853055547942746340739)
              ·
                refine ⟨7934779583321914119511109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5289853055547942746340739 7934779583321914119511109)
                ·
                  refine ⟨1487771171872858897408333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7934779583321914119511109 1487771171872858897408333)
                  ·
                    refine ⟨557914189452322086528125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1487771171872858897408333 557914189452322086528125)
                    ·
                      rfl

theorem cell22_1629801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 3].length) (baseStart_1629801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629801 prefixEnd_1629801 := by exact prefixLift 1629801
  have htrace : WordTrace (prefixWord ++ tailWord_1629801) baseStart_1629801 baseEnd_1629801 := by
    simpa [prefixWord, tailWord_1629801, baseEnd_1629801] using wordTrace_append hprefix tailTrace_1629801
  have hstable : (prefixWord ++ tailWord_1629801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629801).length < 2 ^ (prefixWord ++ tailWord_1629801).sum := by decide
  have hdescent : baseEnd_1629801 < baseStart_1629801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629908 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1629908 : Nat := 118140960795 + 1629908 * 2 ^ 59
def prefixEnd_1629908 : Nat := 4983230072969 + 3 ^ 40 * 1629908 * 2
def baseEnd_1629908 : Nat := 557950817739009474102797

theorem tailTrace_1629908 : CollatzResearch.WordTrace tailWord_1629908 prefixEnd_1629908 557950817739009474102797 := by
  unfold tailWord_1629908
  simp only [CollatzResearch.WordTrace]
  refine ⟨29723814289564578484825189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39631752386086104646433585 29723814289564578484825189)
  ·
    refine ⟨5573215179293358465904723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29723814289564578484825189 5573215179293358465904723)
    ·
      refine ⟨8359822768940037698857085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5573215179293358465904723 8359822768940037698857085)
      ·
        refine ⟨3134933538352514137071407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8359822768940037698857085 3134933538352514137071407)
        ·
          refine ⟨4702400307528771205607111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3134933538352514137071407 4702400307528771205607111)
          ·
            refine ⟨7053600461293156808410667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4702400307528771205607111 7053600461293156808410667)
            ·
              refine ⟨10580400691939735212616001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7053600461293156808410667 10580400691939735212616001)
              ·
                refine ⟨7935300518954801409462001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10580400691939735212616001 7935300518954801409462001)
                ·
                  refine ⟨5951475389216101057096501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7935300518954801409462001 5951475389216101057096501)
                  ·
                    refine ⟨557950817739009474102797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5951475389216101057096501 557950817739009474102797)
                    ·
                      rfl

theorem cell22_1629908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1629908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629908 prefixEnd_1629908 := by exact prefixLift 1629908
  have htrace : WordTrace (prefixWord ++ tailWord_1629908) baseStart_1629908 baseEnd_1629908 := by
    simpa [prefixWord, tailWord_1629908, baseEnd_1629908] using wordTrace_append hprefix tailTrace_1629908
  have hstable : (prefixWord ++ tailWord_1629908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629908).length < 2 ^ (prefixWord ++ tailWord_1629908).sum := by decide
  have hdescent : baseEnd_1629908 < baseStart_1629908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629927 : List Nat := [1, 1, 5, 4, 1, 1, 3, 1, 5]
def baseStart_1629927 : Nat := 118140960795 + 1629927 * 2 ^ 59
def prefixEnd_1629927 : Nat := 4983230072969 + 3 ^ 40 * 1629927 * 2
def baseEnd_1629927 : Nat := 185985773942433252625913

theorem tailTrace_1629927 : CollatzResearch.WordTrace tailWord_1629927 prefixEnd_1629927 185985773942433252625913 := by
  unfold tailWord_1629927
  simp only [CollatzResearch.WordTrace]
  refine ⟨59448321566060323214592035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39632214377373548809728023 59448321566060323214592035)
  ·
    refine ⟨89172482349090484821888053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59448321566060323214592035 89172482349090484821888053)
    ·
      refine ⟨8359920220227232952052005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89172482349090484821888053 8359920220227232952052005)
      ·
        refine ⟨1567485041292606178509751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8359920220227232952052005 1567485041292606178509751)
        ·
          refine ⟨2351227561938909267764627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567485041292606178509751 2351227561938909267764627)
          ·
            refine ⟨3526841342908363901646941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351227561938909267764627 3526841342908363901646941)
            ·
              refine ⟨1322565503590636463117603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3526841342908363901646941 1322565503590636463117603)
              ·
                refine ⟨1983848255385954694676405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322565503590636463117603 1983848255385954694676405)
                ·
                  refine ⟨185985773942433252625913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1983848255385954694676405 185985773942433252625913)
                  ·
                    rfl

theorem cell22_1629927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 5].length) (baseStart_1629927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629927 prefixEnd_1629927 := by exact prefixLift 1629927
  have htrace : WordTrace (prefixWord ++ tailWord_1629927) baseStart_1629927 baseEnd_1629927 := by
    simpa [prefixWord, tailWord_1629927, baseEnd_1629927] using wordTrace_append hprefix tailTrace_1629927
  have hstable : (prefixWord ++ tailWord_1629927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629927).length < 2 ^ (prefixWord ++ tailWord_1629927).sum := by decide
  have hdescent : baseEnd_1629927 < baseStart_1629927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629936 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 1, 5]
def baseStart_1629936 : Nat := 118140960795 + 1629936 * 2 ^ 59
def prefixEnd_1629936 : Nat := 4983230072969 + 3 ^ 40 * 1629936 * 2
def baseEnd_1629936 : Nat := 557960402711226734402711

theorem tailTrace_1629936 : CollatzResearch.WordTrace tailWord_1629936 prefixEnd_1629936 557960402711226734402711 := by
  unfold tailWord_1629936
  simp only [CollatzResearch.WordTrace]
  refine ⟨29724324911513858875834831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39632433215351811834446441 29724324911513858875834831)
  ·
    refine ⟨44586487367270788313752247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29724324911513858875834831 44586487367270788313752247)
    ·
      refine ⟨66879731050906182470628371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44586487367270788313752247 66879731050906182470628371)
      ·
        refine ⟨100319596576359273705942557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66879731050906182470628371 100319596576359273705942557)
        ·
          refine ⟨37619848716134727639728459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100319596576359273705942557 37619848716134727639728459)
          ·
            refine ⟨56429773074202091459592689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37619848716134727639728459 56429773074202091459592689)
            ·
              refine ⟨42322329805651568594694517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56429773074202091459592689 42322329805651568594694517)
              ·
                refine ⟨3967718419279834555752611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42322329805651568594694517 3967718419279834555752611)
                ·
                  refine ⟨5951577628919751833628917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967718419279834555752611 5951577628919751833628917)
                  ·
                    refine ⟨557960402711226734402711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5951577628919751833628917 557960402711226734402711)
                    ·
                      rfl

theorem cell22_1629936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_1629936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629936 prefixEnd_1629936 := by exact prefixLift 1629936
  have htrace : WordTrace (prefixWord ++ tailWord_1629936) baseStart_1629936 baseEnd_1629936 := by
    simpa [prefixWord, tailWord_1629936, baseEnd_1629936] using wordTrace_append hprefix tailTrace_1629936
  have hstable : (prefixWord ++ tailWord_1629936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629936).length < 2 ^ (prefixWord ++ tailWord_1629936).sum := by decide
  have hdescent : baseEnd_1629936 < baseStart_1629936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629951 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 1, 6]
def baseStart_1629951 : Nat := 118140960795 + 1629951 * 2 ^ 59
def prefixEnd_1629951 : Nat := 4983230072969 + 3 ^ 40 * 1629951 * 2
def baseEnd_1629951 : Nat := 557965537517771695277665

theorem tailTrace_1629951 : CollatzResearch.WordTrace tailWord_1629951 prefixEnd_1629951 557965537517771695277665 := by
  unfold tailWord_1629951
  simp only [CollatzResearch.WordTrace]
  refine ⟨59449196917973375313465707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39632797945315583542310471 59449196917973375313465707)
  ·
    refine ⟨89173795376960062970198561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59449196917973375313465707 89173795376960062970198561)
    ·
      refine ⟨66880346532720047227648921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89173795376960062970198561 66880346532720047227648921)
      ·
        refine ⟨50160259899540035420736691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66880346532720047227648921 50160259899540035420736691)
        ·
          refine ⟨75240389849310053131105037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50160259899540035420736691 75240389849310053131105037)
          ·
            refine ⟨28215146193491269924164389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75240389849310053131105037 28215146193491269924164389)
            ·
              refine ⟨5290339911279613110780823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28215146193491269924164389 5290339911279613110780823)
              ·
                refine ⟨7935509866919419666171235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5290339911279613110780823 7935509866919419666171235)
                ·
                  refine ⟨11903264800379129499256853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935509866919419666171235 11903264800379129499256853)
                  ·
                    refine ⟨557965537517771695277665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11903264800379129499256853 557965537517771695277665)
                    ·
                      rfl

theorem cell22_1629951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_1629951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629951 prefixEnd_1629951 := by exact prefixLift 1629951
  have htrace : WordTrace (prefixWord ++ tailWord_1629951) baseStart_1629951 baseEnd_1629951 := by
    simpa [prefixWord, tailWord_1629951, baseEnd_1629951] using wordTrace_append hprefix tailTrace_1629951
  have hstable : (prefixWord ++ tailWord_1629951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629951).length < 2 ^ (prefixWord ++ tailWord_1629951).sum := by decide
  have hdescent : baseEnd_1629951 < baseStart_1629951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629953 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 4, 3]
def baseStart_1629953 : Nat := 118140960795 + 1629953 * 2 ^ 59
def prefixEnd_1629953 : Nat := 4983230072969 + 3 ^ 40 * 1629953 * 2
def baseEnd_1629953 : Nat := 557966222158644356727659

theorem tailTrace_1629953 : CollatzResearch.WordTrace tailWord_1629953 prefixEnd_1629953 557966222158644356727659 := by
  unfold tailWord_1629953
  simp only [CollatzResearch.WordTrace]
  refine ⟨59449269863966129655038513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39632846575977419770025675 59449269863966129655038513)
  ·
    refine ⟨44586952397974597241278885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59449269863966129655038513 44586952397974597241278885)
    ·
      refine ⟨8360053574620236982739791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44586952397974597241278885 8360053574620236982739791)
      ·
        refine ⟨12540080361930355474109687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8360053574620236982739791 12540080361930355474109687)
        ·
          refine ⟨18810120542895533211164531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12540080361930355474109687 18810120542895533211164531)
          ·
            refine ⟨28215180814343299816746797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18810120542895533211164531 28215180814343299816746797)
            ·
              refine ⟨10580692805378737431280049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28215180814343299816746797 10580692805378737431280049)
              ·
                refine ⟨7935519604034053073460037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10580692805378737431280049 7935519604034053073460037)
                ·
                  refine ⟨1487909925756384951273757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7935519604034053073460037 1487909925756384951273757)
                  ·
                    refine ⟨557966222158644356727659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1487909925756384951273757 557966222158644356727659)
                    ·
                      rfl

theorem cell22_1629953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_1629953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629953 prefixEnd_1629953 := by exact prefixLift 1629953
  have htrace : WordTrace (prefixWord ++ tailWord_1629953) baseStart_1629953 baseEnd_1629953 := by
    simpa [prefixWord, tailWord_1629953, baseEnd_1629953] using wordTrace_append hprefix tailTrace_1629953
  have hstable : (prefixWord ++ tailWord_1629953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629953).length < 2 ^ (prefixWord ++ tailWord_1629953).sum := by decide
  have hdescent : baseEnd_1629953 < baseStart_1629953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629965 : List Nat := [1, 7, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1629965 : Nat := 118140960795 + 1629965 * 2 ^ 59
def prefixEnd_1629965 : Nat := 4983230072969 + 3 ^ 40 * 1629965 * 2
def baseEnd_1629965 : Nat := 557970330003880325427623

theorem tailTrace_1629965 : CollatzResearch.WordTrace tailWord_1629965 prefixEnd_1629965 557970330003880325427623 := by
  unfold tailWord_1629965
  simp only [CollatzResearch.WordTrace]
  refine ⟨59449707539922655704475349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39633138359948437136316899 59449707539922655704475349)
  ·
    refine ⟨1393352520466937243073641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 59449707539922655704475349 1393352520466937243073641)
    ·
      refine ⟨1045014390350202932305231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1393352520466937243073641 1045014390350202932305231)
      ·
        refine ⟨1567521585525304398457847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045014390350202932305231 1567521585525304398457847)
        ·
          refine ⟨2351282378287956597686771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567521585525304398457847 2351282378287956597686771)
          ·
            refine ⟨3526923567431934896530157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351282378287956597686771 3526923567431934896530157)
            ·
              refine ⟨1322596337786975586198809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3526923567431934896530157 1322596337786975586198809)
              ·
                refine ⟨991947253340231689649107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322596337786975586198809 991947253340231689649107)
                ·
                  refine ⟨1487920880010347534473661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991947253340231689649107 1487920880010347534473661)
                  ·
                    refine ⟨557970330003880325427623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1487920880010347534473661 557970330003880325427623)
                    ·
                      rfl

theorem cell22_1629965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1629965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629965 prefixEnd_1629965 := by exact prefixLift 1629965
  have htrace : WordTrace (prefixWord ++ tailWord_1629965) baseStart_1629965 baseEnd_1629965 := by
    simpa [prefixWord, tailWord_1629965, baseEnd_1629965] using wordTrace_append hprefix tailTrace_1629965
  have hstable : (prefixWord ++ tailWord_1629965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629965).length < 2 ^ (prefixWord ++ tailWord_1629965).sum := by decide
  have hdescent : baseEnd_1629965 < baseStart_1629965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629966 : List Nat := [4, 1, 1, 2, 1, 1, 12]
def baseStart_1629966 : Nat := 118140960795 + 1629966 * 2 ^ 59
def prefixEnd_1629966 : Nat := 4983230072969 + 3 ^ 40 * 1629966 * 2
def baseEnd_1629966 : Nat := 20665580456456172450097

theorem tailTrace_1629966 : CollatzResearch.WordTrace tailWord_1629966 prefixEnd_1629966 20665580456456172450097 := by
  unfold tailWord_1629966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431218001614879109407719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39633162675279355250174501 7431218001614879109407719)
  ·
    refine ⟨11146827002422318664111579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7431218001614879109407719 11146827002422318664111579)
    ·
      refine ⟨16720240503633477996167369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11146827002422318664111579 16720240503633477996167369)
      ·
        refine ⟨12540180377725108497125527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16720240503633477996167369 12540180377725108497125527)
        ·
          refine ⟨18810270566587662745688291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12540180377725108497125527 18810270566587662745688291)
          ·
            refine ⟨28215405849881494118532437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18810270566587662745688291 28215405849881494118532437)
            ·
              refine ⟨20665580456456172450097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 28215405849881494118532437 20665580456456172450097)
              ·
                rfl

theorem cell22_1629966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 12].length) (baseStart_1629966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1629966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1629966 prefixEnd_1629966 := by exact prefixLift 1629966
  have htrace : WordTrace (prefixWord ++ tailWord_1629966) baseStart_1629966 baseEnd_1629966 := by
    simpa [prefixWord, tailWord_1629966, baseEnd_1629966] using wordTrace_append hprefix tailTrace_1629966
  have hstable : (prefixWord ++ tailWord_1629966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629966).length < 2 ^ (prefixWord ++ tailWord_1629966).sum := by decide
  have hdescent : baseEnd_1629966 < baseStart_1629966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630103 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 1, 6]
def baseStart_1630103 : Nat := 118140960795 + 1630103 * 2 ^ 59
def prefixEnd_1630103 : Nat := 4983230072969 + 3 ^ 40 * 1630103 * 2
def baseEnd_1630103 : Nat := 558017570224093965477199

theorem tailTrace_1630103 : CollatzResearch.WordTrace tailWord_1630103 prefixEnd_1630103 558017570224093965477199 := by
  unfold tailWord_1630103
  simp only [CollatzResearch.WordTrace]
  refine ⟨59454740813422705272998963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39636493875615136848665975 59454740813422705272998963)
  ·
    refine ⟨89182111220134057909498445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59454740813422705272998963 89182111220134057909498445)
    ·
      refine ⟨33443291707550271716061917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89182111220134057909498445 33443291707550271716061917)
      ·
        refine ⟨12541234390331351893523219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33443291707550271716061917 12541234390331351893523219)
        ·
          refine ⟨18811851585497027840284829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12541234390331351893523219 18811851585497027840284829)
          ·
            refine ⟨7054444344561385440106811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18811851585497027840284829 7054444344561385440106811)
            ·
              refine ⟨10581666516842078160160217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7054444344561385440106811 10581666516842078160160217)
              ·
                refine ⟨7936249887631558620120163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10581666516842078160160217 7936249887631558620120163)
                ·
                  refine ⟨11904374831447337930180245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7936249887631558620120163 11904374831447337930180245)
                  ·
                    refine ⟨558017570224093965477199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11904374831447337930180245 558017570224093965477199)
                    ·
                      rfl

theorem cell22_1630103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_1630103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630103 prefixEnd_1630103 := by exact prefixLift 1630103
  have htrace : WordTrace (prefixWord ++ tailWord_1630103) baseStart_1630103 baseEnd_1630103 := by
    simpa [prefixWord, tailWord_1630103, baseEnd_1630103] using wordTrace_append hprefix tailTrace_1630103
  have hstable : (prefixWord ++ tailWord_1630103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630103).length < 2 ^ (prefixWord ++ tailWord_1630103).sum := by decide
  have hdescent : baseEnd_1630103 < baseStart_1630103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630105 : List Nat := [1, 2, 1, 2, 1, 3, 2, 5, 2, 3]
def baseStart_1630105 : Nat := 118140960795 + 1630105 * 2 ^ 59
def prefixEnd_1630105 : Nat := 4983230072969 + 3 ^ 40 * 1630105 * 2
def baseEnd_1630105 : Nat := 558018254864966626927193

theorem tailTrace_1630105 : CollatzResearch.WordTrace tailWord_1630105 prefixEnd_1630105 558018254864966626927193 := by
  unfold tailWord_1630105
  simp only [CollatzResearch.WordTrace]
  refine ⟨59454813759415459614571769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39636542506276973076381179 59454813759415459614571769)
  ·
    refine ⟨44591110319561594710928827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59454813759415459614571769 44591110319561594710928827)
    ·
      refine ⟨66886665479342392066393241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44591110319561594710928827 66886665479342392066393241)
      ·
        refine ⟨50164999109506794049794931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66886665479342392066393241 50164999109506794049794931)
        ·
          refine ⟨75247498664260191074692397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50164999109506794049794931 75247498664260191074692397)
          ·
            refine ⟨28217811999097571653009649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75247498664260191074692397 28217811999097571653009649)
            ·
              refine ⟨21163358999323178739757237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28217811999097571653009649 21163358999323178739757237)
              ·
                refine ⟨1984064906186548006852241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21163358999323178739757237 1984064906186548006852241)
                ·
                  refine ⟨1488048679639911005139181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1984064906186548006852241 1488048679639911005139181)
                  ·
                    refine ⟨558018254864966626927193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1488048679639911005139181 558018254864966626927193)
                    ·
                      rfl

theorem cell22_1630105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 3].length) (baseStart_1630105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630105 prefixEnd_1630105 := by exact prefixLift 1630105
  have htrace : WordTrace (prefixWord ++ tailWord_1630105) baseStart_1630105 baseEnd_1630105 := by
    simpa [prefixWord, tailWord_1630105, baseEnd_1630105] using wordTrace_append hprefix tailTrace_1630105
  have hstable : (prefixWord ++ tailWord_1630105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630105).length < 2 ^ (prefixWord ++ tailWord_1630105).sum := by decide
  have hdescent : baseEnd_1630105 < baseStart_1630105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630201 : List Nat := [1, 2, 1, 3, 1, 6, 2, 2, 1, 3]
def baseStart_1630201 : Nat := 118140960795 + 1630201 * 2 ^ 59
def prefixEnd_1630201 : Nat := 4983230072969 + 3 ^ 40 * 1630201 * 2
def baseEnd_1630201 : Nat := 558051117626854376526899

theorem tailTrace_1630201 : CollatzResearch.WordTrace tailWord_1630201 prefixEnd_1630201 558051117626854376526899 := by
  unfold tailWord_1630201
  simp only [CollatzResearch.WordTrace]
  refine ⟨59458315167067668010066457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39638876778045112006710971 59458315167067668010066457)
  ·
    refine ⟨44593736375300751007549843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59458315167067668010066457 44593736375300751007549843)
    ·
      refine ⟨66890604562951126511324765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44593736375300751007549843 66890604562951126511324765)
      ·
        refine ⟨25083976711106672441746787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66890604562951126511324765 25083976711106672441746787)
        ·
          refine ⟨37625965066660008662620181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25083976711106672441746787 37625965066660008662620181)
          ·
            refine ⟨1763717112499687906060321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37625965066660008662620181 1763717112499687906060321)
            ·
              refine ⟨1322787834374765929545241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1763717112499687906060321 1322787834374765929545241)
              ·
                refine ⟨992090875781074447158931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322787834374765929545241 992090875781074447158931)
                ·
                  refine ⟨1488136313671611670738397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992090875781074447158931 1488136313671611670738397)
                  ·
                    refine ⟨558051117626854376526899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1488136313671611670738397 558051117626854376526899)
                    ·
                      rfl

theorem cell22_1630201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 1, 3].length) (baseStart_1630201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630201 prefixEnd_1630201 := by exact prefixLift 1630201
  have htrace : WordTrace (prefixWord ++ tailWord_1630201) baseStart_1630201 baseEnd_1630201 := by
    simpa [prefixWord, tailWord_1630201, baseEnd_1630201] using wordTrace_append hprefix tailTrace_1630201
  have hstable : (prefixWord ++ tailWord_1630201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630201).length < 2 ^ (prefixWord ++ tailWord_1630201).sum := by decide
  have hdescent : baseEnd_1630201 < baseStart_1630201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630244 : List Nat := [2, 3, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_1630244 : Nat := 118140960795 + 1630244 * 2 ^ 59
def prefixEnd_1630244 : Nat := 4983230072969 + 3 ^ 40 * 1630244 * 2
def baseEnd_1630244 : Nat := 558065837405616597701767

theorem tailTrace_1630244 : CollatzResearch.WordTrace tailWord_1630244 prefixEnd_1630244 558065837405616597701767 := by
  unfold tailWord_1630244
  simp only [CollatzResearch.WordTrace]
  refine ⟨29729941752955943176940893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39639922337274590902587857 29729941752955943176940893)
  ·
    refine ⟨11148728157358478691352835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29729941752955943176940893 11148728157358478691352835)
    ·
      refine ⟨16723092236037718037029253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11148728157358478691352835 16723092236037718037029253)
      ·
        refine ⟨3135579794257072131942985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16723092236037718037029253 3135579794257072131942985)
        ·
          refine ⟨2351684845692804098957239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3135579794257072131942985 2351684845692804098957239)
          ·
            refine ⟨3527527268539206148435859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351684845692804098957239 3527527268539206148435859)
            ·
              refine ⟨5291290902808809222653789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3527527268539206148435859 5291290902808809222653789)
              ·
                refine ⟨1984234088553303458495171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5291290902808809222653789 1984234088553303458495171)
                ·
                  refine ⟨2976351132829955187742757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984234088553303458495171 2976351132829955187742757)
                  ·
                    refine ⟨558065837405616597701767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2976351132829955187742757 558065837405616597701767)
                    ·
                      rfl

theorem cell22_1630244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_1630244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630244 prefixEnd_1630244 := by exact prefixLift 1630244
  have htrace : WordTrace (prefixWord ++ tailWord_1630244) baseStart_1630244 baseEnd_1630244 := by
    simpa [prefixWord, tailWord_1630244, baseEnd_1630244] using wordTrace_append hprefix tailTrace_1630244
  have hstable : (prefixWord ++ tailWord_1630244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630244).length < 2 ^ (prefixWord ++ tailWord_1630244).sum := by decide
  have hdescent : baseEnd_1630244 < baseStart_1630244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630257 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 4, 3]
def baseStart_1630257 : Nat := 118140960795 + 1630257 * 2 ^ 59
def prefixEnd_1630257 : Nat := 4983230072969 + 3 ^ 40 * 1630257 * 2
def baseEnd_1630257 : Nat := 558070287571288897126727

theorem tailTrace_1630257 : CollatzResearch.WordTrace tailWord_1630257 prefixEnd_1630257 558070287571288897126727 := by
  unfold tailWord_1630257
  simp only [CollatzResearch.WordTrace]
  refine ⟨59460357654864789574105025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39640238436576526382736683 59460357654864789574105025)
  ·
    refine ⟨44595268241148592180578769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59460357654864789574105025 44595268241148592180578769)
    ·
      refine ⟨33446451180861444135434077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44595268241148592180578769 33446451180861444135434077)
      ·
        refine ⟨12542419192823041550787779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33446451180861444135434077 12542419192823041550787779)
        ·
          refine ⟨18813628789234562326181669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12542419192823041550787779 18813628789234562326181669)
          ·
            refine ⟨3527555397981480436159063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18813628789234562326181669 3527555397981480436159063)
            ·
              refine ⟨5291333096972220654238595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3527555397981480436159063 5291333096972220654238595)
              ·
                refine ⟨7936999645458330981357893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5291333096972220654238595 7936999645458330981357893)
                ·
                  refine ⟨1488187433523437059004605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7936999645458330981357893 1488187433523437059004605)
                  ·
                    refine ⟨558070287571288897126727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1488187433523437059004605 558070287571288897126727)
                    ·
                      rfl

theorem cell22_1630257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_1630257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630257 prefixEnd_1630257 := by exact prefixLift 1630257
  have htrace : WordTrace (prefixWord ++ tailWord_1630257) baseStart_1630257 baseEnd_1630257 := by
    simpa [prefixWord, tailWord_1630257, baseEnd_1630257] using wordTrace_append hprefix tailTrace_1630257
  have hstable : (prefixWord ++ tailWord_1630257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630257).length < 2 ^ (prefixWord ++ tailWord_1630257).sum := by decide
  have hdescent : baseEnd_1630257 < baseStart_1630257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630319 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 3, 3]
def baseStart_1630319 : Nat := 118140960795 + 1630319 * 2 ^ 59
def prefixEnd_1630319 : Nat := 4983230072969 + 3 ^ 40 * 1630319 * 2
def baseEnd_1630319 : Nat := 558091511438341402076537

theorem tailTrace_1630319 : CollatzResearch.WordTrace tailWord_1630319 prefixEnd_1630319 558091511438341402076537 := by
  unfold tailWord_1630319
  simp only [CollatzResearch.WordTrace]
  refine ⟨59462618980640174162862011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39641745987093449441908007 59462618980640174162862011)
  ·
    refine ⟨89193928470960261244293017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59462618980640174162862011 89193928470960261244293017)
    ·
      refine ⟨66895446353220195933219763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89193928470960261244293017 66895446353220195933219763)
      ·
        refine ⟨100343169529830293899829645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66895446353220195933219763 100343169529830293899829645)
        ·
          refine ⟨37628688573686360212436117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100343169529830293899829645 37628688573686360212436117)
          ·
            refine ⟨1763844776891548134957943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37628688573686360212436117 1763844776891548134957943)
            ·
              refine ⟨2645767165337322202436915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1763844776891548134957943 2645767165337322202436915)
              ·
                refine ⟨3968650748005983303655373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2645767165337322202436915 3968650748005983303655373)
                ·
                  refine ⟨1488244030502243738870765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3968650748005983303655373 1488244030502243738870765)
                  ·
                    refine ⟨558091511438341402076537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1488244030502243738870765 558091511438341402076537)
                    ·
                      rfl

theorem cell22_1630319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 3].length) (baseStart_1630319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630319 prefixEnd_1630319 := by exact prefixLift 1630319
  have htrace : WordTrace (prefixWord ++ tailWord_1630319) baseStart_1630319 baseEnd_1630319 := by
    simpa [prefixWord, tailWord_1630319, baseEnd_1630319] using wordTrace_append hprefix tailTrace_1630319
  have hstable : (prefixWord ++ tailWord_1630319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630319).length < 2 ^ (prefixWord ++ tailWord_1630319).sum := by decide
  have hdescent : baseEnd_1630319 < baseStart_1630319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630332 : List Nat := [2, 2, 2, 1, 1, 5, 1, 3, 5]
def baseStart_1630332 : Nat := 118140960795 + 1630332 * 2 ^ 59
def prefixEnd_1630332 : Nat := 4983230072969 + 3 ^ 40 * 1630332 * 2
def baseEnd_1630332 : Nat := 186031987201337900500499

theorem tailTrace_1630332 : CollatzResearch.WordTrace tailWord_1630332 prefixEnd_1630332 186031987201337900500499 := by
  unfold tailWord_1630332
  simp only [CollatzResearch.WordTrace]
  refine ⟨29731546564796538691542625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39642062086395384922056833 29731546564796538691542625)
  ·
    refine ⟨22298659923597404018656969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29731546564796538691542625 22298659923597404018656969)
    ·
      refine ⟨16723994942698053013992727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22298659923597404018656969 16723994942698053013992727)
      ·
        refine ⟨25085992414047079520989091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16723994942698053013992727 25085992414047079520989091)
        ·
          refine ⟨37628988621070619281483637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25085992414047079520989091 37628988621070619281483637)
          ·
            refine ⟨3527717683225370557639091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37628988621070619281483637 3527717683225370557639091)
            ·
              refine ⟨5291576524838055836458637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3527717683225370557639091 5291576524838055836458637)
              ·
                refine ⟨1984341196814270938671989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5291576524838055836458637 1984341196814270938671989)
                ·
                  refine ⟨186031987201337900500499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1984341196814270938671989 186031987201337900500499)
                  ·
                    rfl

theorem cell22_1630332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_1630332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630332 prefixEnd_1630332 := by exact prefixLift 1630332
  have htrace : WordTrace (prefixWord ++ tailWord_1630332) baseStart_1630332 baseEnd_1630332 := by
    simpa [prefixWord, tailWord_1630332, baseEnd_1630332] using wordTrace_append hprefix tailTrace_1630332
  have hstable : (prefixWord ++ tailWord_1630332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630332).length < 2 ^ (prefixWord ++ tailWord_1630332).sum := by decide
  have hdescent : baseEnd_1630332 < baseStart_1630332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630366 : List Nat := [4, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1630366 : Nat := 118140960795 + 1630366 * 2 ^ 59
def prefixEnd_1630366 : Nat := 4983230072969 + 3 ^ 40 * 1630366 * 2
def baseEnd_1630366 : Nat := 186035866832949648717131

theorem tailTrace_1630366 : CollatzResearch.WordTrace tailWord_1630366 prefixEnd_1630366 186035866832949648717131 := by
  unfold tailWord_1630366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7433041651433737648727869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39642888807646600793215301 7433041651433737648727869)
  ·
    refine ⟨2787390619287651618272951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7433041651433737648727869 2787390619287651618272951)
    ·
      refine ⟨4181085928931477427409427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2787390619287651618272951 4181085928931477427409427)
      ·
        refine ⟨6271628893397216141114141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4181085928931477427409427 6271628893397216141114141)
        ·
          refine ⟨2351860835023956052917803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6271628893397216141114141 2351860835023956052917803)
          ·
            refine ⟨3527791252535934079376705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351860835023956052917803 3527791252535934079376705)
            ·
              refine ⟨2645843439401950559532529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3527791252535934079376705 2645843439401950559532529)
              ·
                refine ⟨1984382579551462919649397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2645843439401950559532529 1984382579551462919649397)
                ·
                  refine ⟨186035866832949648717131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1984382579551462919649397 186035866832949648717131)
                  ·
                    rfl

theorem cell22_1630366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1630366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630366 prefixEnd_1630366 := by exact prefixLift 1630366
  have htrace : WordTrace (prefixWord ++ tailWord_1630366) baseStart_1630366 baseEnd_1630366 := by
    simpa [prefixWord, tailWord_1630366, baseEnd_1630366] using wordTrace_append hprefix tailTrace_1630366
  have hstable : (prefixWord ++ tailWord_1630366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630366).length < 2 ^ (prefixWord ++ tailWord_1630366).sum := by decide
  have hdescent : baseEnd_1630366 < baseStart_1630366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630370 : List Nat := [3, 3, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_1630370 : Nat := 118140960795 + 1630370 * 2 ^ 59
def prefixEnd_1630370 : Nat := 4983230072969 + 3 ^ 40 * 1630370 * 2
def baseEnd_1630370 : Nat := 558108969780594269051381

theorem tailTrace_1630370 : CollatzResearch.WordTrace tailWord_1630370 prefixEnd_1630370 558108969780594269051381 := by
  unfold tailWord_1630370
  simp only [CollatzResearch.WordTrace]
  refine ⟨14866119775863852468242141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39642986068970273248645709 14866119775863852468242141)
  ·
    refine ⟨5574794915948944675590803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14866119775863852468242141 5574794915948944675590803)
    ·
      refine ⟨8362192373923417013386205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5574794915948944675590803 8362192373923417013386205)
      ·
        refine ⟨3135822140221281380019827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8362192373923417013386205 3135822140221281380019827)
        ·
          refine ⟨4703733210331922070029741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3135822140221281380019827 4703733210331922070029741)
          ·
            refine ⟨1763899953874470776261153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4703733210331922070029741 1763899953874470776261153)
            ·
              refine ⟨1322924965405853082195865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1763899953874470776261153 1322924965405853082195865)
              ·
                refine ⟨992193724054389811646899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322924965405853082195865 992193724054389811646899)
                ·
                  refine ⟨1488290586081584717470349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992193724054389811646899 1488290586081584717470349)
                  ·
                    refine ⟨558108969780594269051381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1488290586081584717470349 558108969780594269051381)
                    ·
                      rfl

theorem cell22_1630370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_1630370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630370 prefixEnd_1630370 := by exact prefixLift 1630370
  have htrace : WordTrace (prefixWord ++ tailWord_1630370) baseStart_1630370 baseEnd_1630370 := by
    simpa [prefixWord, tailWord_1630370, baseEnd_1630370] using wordTrace_append hprefix tailTrace_1630370
  have hstable : (prefixWord ++ tailWord_1630370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630370).length < 2 ^ (prefixWord ++ tailWord_1630370).sum := by decide
  have hdescent : baseEnd_1630370 < baseStart_1630370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630392 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 1, 5]
def baseStart_1630392 : Nat := 118140960795 + 1630392 * 2 ^ 59
def prefixEnd_1630392 : Nat := 4983230072969 + 3 ^ 40 * 1630392 * 2
def baseEnd_1630392 : Nat := 558116500830193545001313

theorem tailTrace_1630392 : CollatzResearch.WordTrace tailWord_1630392 prefixEnd_1630392 558116500830193545001313 := by
  unfold tailWord_1630392
  simp only [CollatzResearch.WordTrace]
  refine ⟨29732640754687853815134715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39643521006250471753512953 29732640754687853815134715)
  ·
    refine ⟨44598961132031780722702073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29732640754687853815134715 44598961132031780722702073)
    ·
      refine ⟨33449220849023835542026555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44598961132031780722702073 33449220849023835542026555)
      ·
        refine ⟨50173831273535753313039833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33449220849023835542026555 50173831273535753313039833)
        ·
          refine ⟨37630373455151814984779875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50173831273535753313039833 37630373455151814984779875)
          ·
            refine ⟨56445560182727722477169813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37630373455151814984779875 56445560182727722477169813)
            ·
              refine ⟨2645885633565361991117335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56445560182727722477169813 2645885633565361991117335)
              ·
                refine ⟨3968828450348042986676003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2645885633565361991117335 3968828450348042986676003)
                ·
                  refine ⟨5953242675522064480014005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3968828450348042986676003 5953242675522064480014005)
                  ·
                    refine ⟨558116500830193545001313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5953242675522064480014005 558116500830193545001313)
                    ·
                      rfl

theorem cell22_1630392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_1630392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630392 prefixEnd_1630392 := by exact prefixLift 1630392
  have htrace : WordTrace (prefixWord ++ tailWord_1630392) baseStart_1630392 baseEnd_1630392 := by
    simpa [prefixWord, tailWord_1630392, baseEnd_1630392] using wordTrace_append hprefix tailTrace_1630392
  have hstable : (prefixWord ++ tailWord_1630392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630392).length < 2 ^ (prefixWord ++ tailWord_1630392).sum := by decide
  have hdescent : baseEnd_1630392 < baseStart_1630392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630405 : List Nat := [1, 3, 1, 1, 1, 1, 4, 10]
def baseStart_1630405 : Nat := 118140960795 + 1630405 * 2 ^ 59
def prefixEnd_1630405 : Nat := 4983230072969 + 3 ^ 40 * 1630405 * 2
def baseEnd_1630405 : Nat := 62013438999540649380697

theorem tailTrace_1630405 : CollatzResearch.WordTrace tailWord_1630405 prefixEnd_1630405 62013438999540649380697 := by
  unfold tailWord_1630405
  simp only [CollatzResearch.WordTrace]
  refine ⟨59465755658328610850492669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39643837105552407233661779 59465755658328610850492669)
  ·
    refine ⟨22299658371873229068934751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59465755658328610850492669 22299658371873229068934751)
    ·
      refine ⟨33449487557809843603402127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22299658371873229068934751 33449487557809843603402127)
      ·
        refine ⟨50174231336714765405103191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33449487557809843603402127 50174231336714765405103191)
        ·
          refine ⟨75261347005072148107654787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50174231336714765405103191 75261347005072148107654787)
          ·
            refine ⟨112892020507608222161482181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75261347005072148107654787 112892020507608222161482181)
            ·
              refine ⟨21167253845176541655277909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112892020507608222161482181 21167253845176541655277909)
              ·
                refine ⟨62013438999540649380697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21167253845176541655277909 62013438999540649380697)
                ·
                  rfl

theorem cell22_1630405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 10].length) (baseStart_1630405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630405 prefixEnd_1630405 := by exact prefixLift 1630405
  have htrace : WordTrace (prefixWord ++ tailWord_1630405) baseStart_1630405 baseEnd_1630405 := by
    simpa [prefixWord, tailWord_1630405, baseEnd_1630405] using wordTrace_append hprefix tailTrace_1630405
  have hstable : (prefixWord ++ tailWord_1630405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630405).length < 2 ^ (prefixWord ++ tailWord_1630405).sum := by decide
  have hdescent : baseEnd_1630405 < baseStart_1630405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630488 : List Nat := [2, 1, 2, 3, 1, 2, 5, 2, 1, 3]
def baseStart_1630488 : Nat := 118140960795 + 1630488 * 2 ^ 59
def prefixEnd_1630488 : Nat := 4983230072969 + 3 ^ 40 * 1630488 * 2
def baseEnd_1630488 : Nat := 558149363592081294601019

theorem tailTrace_1630488 : CollatzResearch.WordTrace tailWord_1630488 prefixEnd_1630488 558149363592081294601019 := by
  unfold tailWord_1630488
  simp only [CollatzResearch.WordTrace]
  refine ⟨29734391458513958012882059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39645855278018610683842745 29734391458513958012882059)
  ·
    refine ⟨44601587187770937019323089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29734391458513958012882059 44601587187770937019323089)
    ·
      refine ⟨33451190390828202764492317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44601587187770937019323089 33451190390828202764492317)
      ·
        refine ⟨12544196396560576036684619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33451190390828202764492317 12544196396560576036684619)
        ·
          refine ⟨18816294594840864055026929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12544196396560576036684619 18816294594840864055026929)
          ·
            refine ⟨14112220946130648041270197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18816294594840864055026929 14112220946130648041270197)
            ·
              refine ⟨1323020713699748253869081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14112220946130648041270197 1323020713699748253869081)
              ·
                refine ⟨992265535274811190401811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323020713699748253869081 992265535274811190401811)
                ·
                  refine ⟨1488398302912216785602717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992265535274811190401811 1488398302912216785602717)
                  ·
                    refine ⟨558149363592081294601019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1488398302912216785602717 558149363592081294601019)
                    ·
                      rfl

theorem cell22_1630488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_1630488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630488 prefixEnd_1630488 := by exact prefixLift 1630488
  have htrace : WordTrace (prefixWord ++ tailWord_1630488) baseStart_1630488 baseEnd_1630488 := by
    simpa [prefixWord, tailWord_1630488, baseEnd_1630488] using wordTrace_append hprefix tailTrace_1630488
  have hstable : (prefixWord ++ tailWord_1630488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630488).length < 2 ^ (prefixWord ++ tailWord_1630488).sum := by decide
  have hdescent : baseEnd_1630488 < baseStart_1630488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630576 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 2, 4]
def baseStart_1630576 : Nat := 118140960795 + 1630576 * 2 ^ 59
def prefixEnd_1630576 : Nat := 4983230072969 + 3 ^ 40 * 1630576 * 2
def baseEnd_1630576 : Nat := 558179487790478398400749

theorem tailTrace_1630576 : CollatzResearch.WordTrace tailWord_1630576 prefixEnd_1630576 558179487790478398400749 := by
  unfold tailWord_1630576
  simp only [CollatzResearch.WordTrace]
  refine ⟨29735996270354553527483791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39647995027139404703311721 29735996270354553527483791)
  ·
    refine ⟨44603994405531830291225687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29735996270354553527483791 44603994405531830291225687)
    ·
      refine ⟨66905991608297745436838531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44603994405531830291225687 66905991608297745436838531)
      ·
        refine ⟨100358987412446618155257797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66905991608297745436838531 100358987412446618155257797)
        ·
          refine ⟨18817310139833740904110837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100358987412446618155257797 18817310139833740904110837)
          ·
            refine ⟨1764122825609413209760391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18817310139833740904110837 1764122825609413209760391)
            ·
              refine ⟨2646184238414119814640587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764122825609413209760391 2646184238414119814640587)
              ·
                refine ⟨3969276357621179721960881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646184238414119814640587 3969276357621179721960881)
                ·
                  refine ⟨2976957268215884791470661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3969276357621179721960881 2976957268215884791470661)
                  ·
                    refine ⟨558179487790478398400749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2976957268215884791470661 558179487790478398400749)
                    ·
                      rfl

theorem cell22_1630576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 2, 4].length) (baseStart_1630576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630576 prefixEnd_1630576 := by exact prefixLift 1630576
  have htrace : WordTrace (prefixWord ++ tailWord_1630576) baseStart_1630576 baseEnd_1630576 := by
    simpa [prefixWord, tailWord_1630576, baseEnd_1630576] using wordTrace_append hprefix tailTrace_1630576
  have hstable : (prefixWord ++ tailWord_1630576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630576).length < 2 ^ (prefixWord ++ tailWord_1630576).sum := by decide
  have hdescent : baseEnd_1630576 < baseStart_1630576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630582 : List Nat := [5, 1, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_1630582 : Nat := 118140960795 + 1630582 * 2 ^ 59
def prefixEnd_1630582 : Nat := 4983230072969 + 3 ^ 40 * 1630582 * 2
def baseEnd_1630582 : Nat := 558181541713096382750731

theorem tailTrace_1630582 : CollatzResearch.WordTrace tailWord_1630582 prefixEnd_1630582 558181541713096382750731 := by
  unfold tailWord_1630582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3717013211167960629980375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39648140919124913386457333 3717013211167960629980375)
  ·
    refine ⟨5575519816751940944970563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3717013211167960629980375 5575519816751940944970563)
    ·
      refine ⟨8363279725127911417455845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5575519816751940944970563 8363279725127911417455845)
      ·
        refine ⟨1568114948461483390772971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8363279725127911417455845 1568114948461483390772971)
        ·
          refine ⟨2352172422692225086159457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568114948461483390772971 2352172422692225086159457)
          ·
            refine ⟨1764129317019168814619593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2352172422692225086159457 1764129317019168814619593)
            ·
              refine ⟨1323096987764376610964695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1764129317019168814619593 1323096987764376610964695)
              ·
                refine ⟨1984645481646564916447043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1323096987764376610964695 1984645481646564916447043)
                ·
                  refine ⟨2976968222469847374670565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984645481646564916447043 2976968222469847374670565)
                  ·
                    refine ⟨558181541713096382750731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2976968222469847374670565 558181541713096382750731)
                    ·
                      rfl

theorem cell22_1630582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_1630582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630582 prefixEnd_1630582 := by exact prefixLift 1630582
  have htrace : WordTrace (prefixWord ++ tailWord_1630582) baseStart_1630582 baseEnd_1630582 := by
    simpa [prefixWord, tailWord_1630582, baseEnd_1630582] using wordTrace_append hprefix tailTrace_1630582
  have hstable : (prefixWord ++ tailWord_1630582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630582).length < 2 ^ (prefixWord ++ tailWord_1630582).sum := by decide
  have hdescent : baseEnd_1630582 < baseStart_1630582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630595 : List Nat := [1, 1, 1, 3, 7, 1, 1, 2, 2, 3]
def baseStart_1630595 : Nat := 118140960795 + 1630595 * 2 ^ 59
def prefixEnd_1630595 : Nat := 4983230072969 + 3 ^ 40 * 1630595 * 2
def baseEnd_1630595 : Nat := 558185991878768682175691

theorem tailTrace_1630595 : CollatzResearch.WordTrace tailWord_1630595 prefixEnd_1630595 558185991878768682175691 := by
  unfold tailWord_1630595
  simp only [CollatzResearch.WordTrace]
  refine ⟨59472685527640273299909239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39648457018426848866606159 59472685527640273299909239)
  ·
    refine ⟨89209028291460409949863859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59472685527640273299909239 89209028291460409949863859)
    ·
      refine ⟨133813542437190614924795789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89209028291460409949863859 133813542437190614924795789)
      ·
        refine ⟨50180078413946480596798421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133813542437190614924795789 50180078413946480596798421)
        ·
          refine ⟨1176095587826870638987463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 50180078413946480596798421 1176095587826870638987463)
          ·
            refine ⟨1764143381740305958481195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176095587826870638987463 1764143381740305958481195)
            ·
              refine ⟨2646215072610458937721793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764143381740305958481195 2646215072610458937721793)
              ·
                refine ⟨1984661304457844203291345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2646215072610458937721793 1984661304457844203291345)
                ·
                  refine ⟨1488495978343383152468509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1984661304457844203291345 1488495978343383152468509)
                  ·
                    refine ⟨558185991878768682175691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1488495978343383152468509 558185991878768682175691)
                    ·
                      rfl

theorem cell22_1630595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 2, 3].length) (baseStart_1630595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630595 prefixEnd_1630595 := by exact prefixLift 1630595
  have htrace : WordTrace (prefixWord ++ tailWord_1630595) baseStart_1630595 baseEnd_1630595 := by
    simpa [prefixWord, tailWord_1630595, baseEnd_1630595] using wordTrace_append hprefix tailTrace_1630595
  have hstable : (prefixWord ++ tailWord_1630595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630595).length < 2 ^ (prefixWord ++ tailWord_1630595).sum := by decide
  have hdescent : baseEnd_1630595 < baseStart_1630595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630625 : List Nat := [1, 2, 3, 5, 2, 1, 2, 6]
def baseStart_1630625 : Nat := 118140960795 + 1630625 * 2 ^ 59
def prefixEnd_1630625 : Nat := 4983230072969 + 3 ^ 40 * 1630625 * 2
def baseEnd_1630625 : Nat := 62021806832428733769511

theorem tailTrace_1630625 : CollatzResearch.WordTrace tailWord_1630625 prefixEnd_1630625 62021806832428733769511 := by
  unfold tailWord_1630625
  simp only [CollatzResearch.WordTrace]
  refine ⟨59473779717531588423501329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39649186478354392282334219 59473779717531588423501329)
  ·
    refine ⟨44605334788148691317625997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59473779717531588423501329 44605334788148691317625997)
    ·
      refine ⟨16727000545555759244109749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44605334788148691317625997 16727000545555759244109749)
      ·
        refine ⟨1568156301145852429135289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16727000545555759244109749 1568156301145852429135289)
        ·
          refine ⟨1176117225859389321851467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1568156301145852429135289 1176117225859389321851467)
          ·
            refine ⟨1764175838789083982777201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176117225859389321851467 1764175838789083982777201)
            ·
              refine ⟨1323131879091812987082901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1764175838789083982777201 1323131879091812987082901)
              ·
                refine ⟨62021806832428733769511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1323131879091812987082901 62021806832428733769511)
                ·
                  rfl

theorem cell22_1630625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 6].length) (baseStart_1630625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630625 prefixEnd_1630625 := by exact prefixLift 1630625
  have htrace : WordTrace (prefixWord ++ tailWord_1630625) baseStart_1630625 baseEnd_1630625 := by
    simpa [prefixWord, tailWord_1630625, baseEnd_1630625] using wordTrace_append hprefix tailTrace_1630625
  have hstable : (prefixWord ++ tailWord_1630625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630625).length < 2 ^ (prefixWord ++ tailWord_1630625).sum := by decide
  have hdescent : baseEnd_1630625 < baseStart_1630625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630696 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 1, 5]
def baseStart_1630696 : Nat := 118140960795 + 1630696 * 2 ^ 59
def prefixEnd_1630696 : Nat := 4983230072969 + 3 ^ 40 * 1630696 * 2
def baseEnd_1630696 : Nat := 558220566242838085400381

theorem tailTrace_1630696 : CollatzResearch.WordTrace tailWord_1630696 prefixEnd_1630696 558220566242838085400381 := by
  unfold tailWord_1630696
  simp only [CollatzResearch.WordTrace]
  refine ⟨29738184650137183774667971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39650912866849578366223961 29738184650137183774667971)
  ·
    refine ⟨44607276975205775662001957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29738184650137183774667971 44607276975205775662001957)
    ·
      refine ⟨8363864432851082936625367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44607276975205775662001957 8363864432851082936625367)
      ·
        refine ⟨12545796649276624404938051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8363864432851082936625367 12545796649276624404938051)
        ·
          refine ⟨18818694973914936607407077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12545796649276624404938051 18818694973914936607407077)
          ·
            refine ⟨3528505307609050613888827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18818694973914936607407077 3528505307609050613888827)
            ·
              refine ⟨5292757961413575920833241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528505307609050613888827 5292757961413575920833241)
              ·
                refine ⟨3969568471060181940624931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5292757961413575920833241 3969568471060181940624931)
                ·
                  refine ⟨5954352706590272910937397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969568471060181940624931 5954352706590272910937397)
                  ·
                    refine ⟨558220566242838085400381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5954352706590272910937397 558220566242838085400381)
                    ·
                      rfl

theorem cell22_1630696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_1630696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630696 prefixEnd_1630696 := by exact prefixLift 1630696
  have htrace : WordTrace (prefixWord ++ tailWord_1630696) baseStart_1630696 baseEnd_1630696 := by
    simpa [prefixWord, tailWord_1630696, baseEnd_1630696] using wordTrace_append hprefix tailTrace_1630696
  have hstable : (prefixWord ++ tailWord_1630696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630696).length < 2 ^ (prefixWord ++ tailWord_1630696).sum := by decide
  have hdescent : baseEnd_1630696 < baseStart_1630696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630739 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 2, 6]
def baseStart_1630739 : Nat := 118140960795 + 1630739 * 2 ^ 59
def prefixEnd_1630739 : Nat := 4983230072969 + 3 ^ 40 * 1630739 * 2
def baseEnd_1630739 : Nat := 558235286021600306575249

theorem tailTrace_1630739 : CollatzResearch.WordTrace tailWord_1630739 prefixEnd_1630739 558235286021600306575249 := by
  unfold tailWord_1630739
  simp only [CollatzResearch.WordTrace]
  refine ⟨59477937639118585893151271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39651958426079057262100847 59477937639118585893151271)
  ·
    refine ⟨89216906458677878839726907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59477937639118585893151271 89216906458677878839726907)
    ·
      refine ⟨133825359688016818259590361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89216906458677878839726907 133825359688016818259590361)
      ·
        refine ⟨100369019766012613694692771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133825359688016818259590361 100369019766012613694692771)
        ·
          refine ⟨150553529649018920542039157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100369019766012613694692771 150553529649018920542039157)
          ·
            refine ⟨14114393404595523800816171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150553529649018920542039157 14114393404595523800816171)
            ·
              refine ⟨21171590106893285701224257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14114393404595523800816171 21171590106893285701224257)
              ·
                refine ⟨15878692580169964275918193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21171590106893285701224257 15878692580169964275918193)
                ·
                  refine ⟨11909019435127473206938645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15878692580169964275918193 11909019435127473206938645)
                  ·
                    refine ⟨558235286021600306575249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11909019435127473206938645 558235286021600306575249)
                    ·
                      rfl

theorem cell22_1630739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_1630739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630739 prefixEnd_1630739 := by exact prefixLift 1630739
  have htrace : WordTrace (prefixWord ++ tailWord_1630739) baseStart_1630739 baseEnd_1630739 := by
    simpa [prefixWord, tailWord_1630739, baseEnd_1630739] using wordTrace_append hprefix tailTrace_1630739
  have hstable : (prefixWord ++ tailWord_1630739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630739).length < 2 ^ (prefixWord ++ tailWord_1630739).sum := by decide
  have hdescent : baseEnd_1630739 < baseStart_1630739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630910 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_1630910 : Nat := 118140960795 + 1630910 * 2 ^ 59
def prefixEnd_1630910 : Nat := 4983230072969 + 3 ^ 40 * 1630910 * 2
def baseEnd_1630910 : Nat := 558293822816212860549725

theorem tailTrace_1630910 : CollatzResearch.WordTrace tailWord_1630910 prefixEnd_1630910 558293822816212860549725 := by
  unfold tailWord_1630910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7435521815187385262203273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39656116347666054731750789 7435521815187385262203273)
  ·
    refine ⟨5576641361390538946652455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7435521815187385262203273 5576641361390538946652455)
    ·
      refine ⟨8364962042085808419978683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5576641361390538946652455 8364962042085808419978683)
      ·
        refine ⟨12547443063128712629968025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8364962042085808419978683 12547443063128712629968025)
        ·
          refine ⟨9410582297346534472476019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12547443063128712629968025 9410582297346534472476019)
          ·
            refine ⟨14115873446019801708714029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9410582297346534472476019 14115873446019801708714029)
            ·
              refine ⟨5293452542257425640767761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14115873446019801708714029 5293452542257425640767761)
              ·
                refine ⟨3970089406693069230575821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5293452542257425640767761 3970089406693069230575821)
                ·
                  refine ⟨1488783527509900961465933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3970089406693069230575821 1488783527509900961465933)
                  ·
                    refine ⟨558293822816212860549725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1488783527509900961465933 558293822816212860549725)
                    ·
                      rfl

theorem cell22_1630910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_1630910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630910 prefixEnd_1630910 := by exact prefixLift 1630910
  have htrace : WordTrace (prefixWord ++ tailWord_1630910) baseStart_1630910 baseEnd_1630910 := by
    simpa [prefixWord, tailWord_1630910, baseEnd_1630910] using wordTrace_append hprefix tailTrace_1630910
  have hstable : (prefixWord ++ tailWord_1630910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630910).length < 2 ^ (prefixWord ++ tailWord_1630910).sum := by decide
  have hdescent : baseEnd_1630910 < baseStart_1630910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630940 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 7]
def baseStart_1630940 : Nat := 118140960795 + 1630940 * 2 ^ 59
def prefixEnd_1630940 : Nat := 4983230072969 + 3 ^ 40 * 1630940 * 2
def baseEnd_1630940 : Nat := 186101364143100927433211

theorem tailTrace_1630940 : CollatzResearch.WordTrace tailWord_1630940 prefixEnd_1630940 186101364143100927433211 := by
  unfold tailWord_1630940
  simp only [CollatzResearch.WordTrace]
  refine ⟨29742634355695198610609137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39656845807593598147478849 29742634355695198610609137)
  ·
    refine ⟨22306975766771398957956853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29742634355695198610609137 22306975766771398957956853)
    ·
      refine ⟨2091278978134818652308455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22306975766771398957956853 2091278978134818652308455)
      ·
        refine ⟨3136918467202227978462683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2091278978134818652308455 3136918467202227978462683)
        ·
          refine ⟨4705377700803341967694025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136918467202227978462683 4705377700803341967694025)
          ·
            refine ⟨3529033275602506475770519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4705377700803341967694025 3529033275602506475770519)
            ·
              refine ⟨5293549913403759713655779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529033275602506475770519 5293549913403759713655779)
              ·
                refine ⟨7940324870105639570483669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293549913403759713655779 7940324870105639570483669)
                ·
                  refine ⟨186101364143100927433211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7940324870105639570483669 186101364143100927433211)
                  ·
                    rfl

theorem cell22_1630940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_1630940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630940 prefixEnd_1630940 := by exact prefixLift 1630940
  have htrace : WordTrace (prefixWord ++ tailWord_1630940) baseStart_1630940 baseEnd_1630940 := by
    simpa [prefixWord, tailWord_1630940, baseEnd_1630940] using wordTrace_append hprefix tailTrace_1630940
  have hstable : (prefixWord ++ tailWord_1630940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630940).length < 2 ^ (prefixWord ++ tailWord_1630940).sum := by decide
  have hdescent : baseEnd_1630940 < baseStart_1630940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630985 : List Nat := [1, 2, 1, 1, 3, 2, 5, 3, 4]
def baseStart_1630985 : Nat := 118140960795 + 1630985 * 2 ^ 59
def prefixEnd_1630985 : Nat := 4983230072969 + 3 ^ 40 * 1630985 * 2
def baseEnd_1630985 : Nat := 186106498949645888308165

theorem tailTrace_1630985 : CollatzResearch.WordTrace tailWord_1630985 prefixEnd_1630985 186106498949645888308165 := by
  unfold tailWord_1630985
  simp only [CollatzResearch.WordTrace]
  refine ⟨59486909996227369906606409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39657939997484913271070939 59486909996227369906606409)
  ·
    refine ⟨44615182497170527429954807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59486909996227369906606409 44615182497170527429954807)
    ·
      refine ⟨66922773745755791144932211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44615182497170527429954807 66922773745755791144932211)
      ·
        refine ⟨100384160618633686717398317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66922773745755791144932211 100384160618633686717398317)
        ·
          refine ⟨37644060231987632519024369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100384160618633686717398317 37644060231987632519024369)
          ·
            refine ⟨28233045173990724389268277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37644060231987632519024369 28233045173990724389268277)
            ·
              refine ⟨2646847985061630411493901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28233045173990724389268277 2646847985061630411493901)
              ·
                refine ⟨992567994398111404310213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2646847985061630411493901 992567994398111404310213)
                ·
                  refine ⟨186106498949645888308165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 992567994398111404310213 186106498949645888308165)
                  ·
                    rfl

theorem cell22_1630985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 4].length) (baseStart_1630985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1630985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1630985 prefixEnd_1630985 := by exact prefixLift 1630985
  have htrace : WordTrace (prefixWord ++ tailWord_1630985) baseStart_1630985 baseEnd_1630985 := by
    simpa [prefixWord, tailWord_1630985, baseEnd_1630985] using wordTrace_append hprefix tailTrace_1630985
  have hstable : (prefixWord ++ tailWord_1630985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630985).length < 2 ^ (prefixWord ++ tailWord_1630985).sum := by decide
  have hdescent : baseEnd_1630985 < baseStart_1630985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631000 : List Nat := [2, 1, 2, 3, 1, 1, 1, 6, 2, 3]
def baseStart_1631000 : Nat := 118140960795 + 1631000 * 2 ^ 59
def prefixEnd_1631000 : Nat := 4983230072969 + 3 ^ 40 * 1631000 * 2
def baseEnd_1631000 : Nat := 558324631655482625799449

theorem tailTrace_1631000 : CollatzResearch.WordTrace tailWord_1631000 prefixEnd_1631000 558324631655482625799449 := by
  unfold tailWord_1631000
  simp only [CollatzResearch.WordTrace]
  refine ⟨29743728545586513734201227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39658304727448684978934969 29743728545586513734201227)
  ·
    refine ⟨44615592818379770601301841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29743728545586513734201227 44615592818379770601301841)
    ·
      refine ⟨33461694613784827950976381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44615592818379770601301841 33461694613784827950976381)
      ·
        refine ⟨12548135480169310481616143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33461694613784827950976381 12548135480169310481616143)
        ·
          refine ⟨18822203220253965722424215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12548135480169310481616143 18822203220253965722424215)
          ·
            refine ⟨28233304830380948583636323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18822203220253965722424215 28233304830380948583636323)
            ·
              refine ⟨42349957245571422875454485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28233304830380948583636323 42349957245571422875454485)
              ·
                refine ⟨1985154245886160447286929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42349957245571422875454485 1985154245886160447286929)
                ·
                  refine ⟨1488865684414620335465197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1985154245886160447286929 1488865684414620335465197)
                  ·
                    refine ⟨558324631655482625799449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1488865684414620335465197 558324631655482625799449)
                    ·
                      rfl

theorem cell22_1631000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_1631000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631000 prefixEnd_1631000 := by exact prefixLift 1631000
  have htrace : WordTrace (prefixWord ++ tailWord_1631000) baseStart_1631000 baseEnd_1631000 := by
    simpa [prefixWord, tailWord_1631000, baseEnd_1631000] using wordTrace_append hprefix tailTrace_1631000
  have hstable : (prefixWord ++ tailWord_1631000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631000).length < 2 ^ (prefixWord ++ tailWord_1631000).sum := by decide
  have hdescent : baseEnd_1631000 < baseStart_1631000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631002 : List Nat := [3, 1, 1, 3, 2, 1, 5, 2, 4]
def baseStart_1631002 : Nat := 118140960795 + 1631002 * 2 ^ 59
def prefixEnd_1631002 : Nat := 4983230072969 + 3 ^ 40 * 1631002 * 2
def baseEnd_1631002 : Nat := 186108438765451762416481

theorem tailTrace_1631002 : CollatzResearch.WordTrace tailWord_1631002 prefixEnd_1631002 186108438765451762416481 := by
  unfold tailWord_1631002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14871882509291445452493815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39658353358110521206650173 14871882509291445452493815)
  ·
    refine ⟨22307823763937168178740723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14871882509291445452493815 22307823763937168178740723)
    ·
      refine ⟨33461735645905752268111085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22307823763937168178740723 33461735645905752268111085)
      ·
        refine ⟨12548150867214657100541657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33461735645905752268111085 12548150867214657100541657)
        ·
          refine ⟨9411113150410992825406243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12548150867214657100541657 9411113150410992825406243)
          ·
            refine ⟨14116669725616489238109365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9411113150410992825406243 14116669725616489238109365)
            ·
              refine ⟨1323437786776545866072753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14116669725616489238109365 1323437786776545866072753)
              ·
                refine ⟨992578340082409399554565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323437786776545866072753 992578340082409399554565)
                ·
                  refine ⟨186108438765451762416481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 992578340082409399554565 186108438765451762416481)
                  ·
                    rfl

theorem cell22_1631002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_1631002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631002 prefixEnd_1631002 := by exact prefixLift 1631002
  have htrace : WordTrace (prefixWord ++ tailWord_1631002) baseStart_1631002 baseEnd_1631002 := by
    simpa [prefixWord, tailWord_1631002, baseEnd_1631002] using wordTrace_append hprefix tailTrace_1631002
  have hstable : (prefixWord ++ tailWord_1631002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631002).length < 2 ^ (prefixWord ++ tailWord_1631002).sum := by decide
  have hdescent : baseEnd_1631002 < baseStart_1631002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631013 : List Nat := [1, 3, 1, 2, 3, 1, 4, 7]
def baseStart_1631013 : Nat := 118140960795 + 1631013 * 2 ^ 59
def prefixEnd_1631013 : Nat := 4983230072969 + 3 ^ 40 * 1631013 * 2
def baseEnd_1631013 : Nat := 62036564646794991691601

theorem tailTrace_1631013 : CollatzResearch.WordTrace tailWord_1631013 prefixEnd_1631013 62036564646794991691601 := by
  unfold tailWord_1631013
  simp only [CollatzResearch.WordTrace]
  refine ⟨59487931240125930688625693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39658620826750620459083795 59487931240125930688625693)
  ·
    refine ⟨22307974215047224008234635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59487931240125930688625693 22307974215047224008234635)
    ·
      refine ⟨33461961322570836012351953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22307974215047224008234635 33461961322570836012351953)
      ·
        refine ⟨25096470991928127009263965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33461961322570836012351953 25096470991928127009263965)
        ·
          refine ⟨9411176621973047628473987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25096470991928127009263965 9411176621973047628473987)
          ·
            refine ⟨14116764932959571442710981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9411176621973047628473987 14116764932959571442710981)
            ·
              refine ⟨2646893424929919645508309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14116764932959571442710981 2646893424929919645508309)
              ·
                refine ⟨62036564646794991691601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2646893424929919645508309 62036564646794991691601)
                ·
                  rfl

theorem cell22_1631013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 7].length) (baseStart_1631013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631013 prefixEnd_1631013 := by exact prefixLift 1631013
  have htrace : WordTrace (prefixWord ++ tailWord_1631013) baseStart_1631013 baseEnd_1631013 := by
    simpa [prefixWord, tailWord_1631013, baseEnd_1631013] using wordTrace_append hprefix tailTrace_1631013
  have hstable : (prefixWord ++ tailWord_1631013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631013).length < 2 ^ (prefixWord ++ tailWord_1631013).sum := by decide
  have hdescent : baseEnd_1631013 < baseStart_1631013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631021 : List Nat := [1, 5, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1631021 : Nat := 118140960795 + 1631021 * 2 ^ 59
def prefixEnd_1631021 : Nat := 4983230072969 + 3 ^ 40 * 1631021 * 2
def baseEnd_1631021 : Nat := 558331820384645571024385

theorem tailTrace_1631021 : CollatzResearch.WordTrace tailWord_1631021 prefixEnd_1631021 558331820384645571024385 := by
  unfold tailWord_1631021
  simp only [CollatzResearch.WordTrace]
  refine ⟨59488223024096948054916917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39658815349397965369944611 59488223024096948054916917)
  ·
    refine ⟨5577020908509088880148461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59488223024096948054916917 5577020908509088880148461)
    ·
      refine ⟨2091382840690908330055673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5577020908509088880148461 2091382840690908330055673)
      ·
        refine ⟨1568537130518181247541755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2091382840690908330055673 1568537130518181247541755)
        ·
          refine ⟨2352805695777271871312633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568537130518181247541755 2352805695777271871312633)
          ·
            refine ⟨1764604271832953903484475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2352805695777271871312633 1764604271832953903484475)
            ·
              refine ⟨2646906407749430855226713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764604271832953903484475 2646906407749430855226713)
              ·
                refine ⟨1985179805812073141420035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2646906407749430855226713 1985179805812073141420035)
                ·
                  refine ⟨2977769708718109712130053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1985179805812073141420035 2977769708718109712130053)
                  ·
                    refine ⟨558331820384645571024385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2977769708718109712130053 558331820384645571024385)
                    ·
                      rfl

theorem cell22_1631021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1631021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631021 prefixEnd_1631021 := by exact prefixLift 1631021
  have htrace : WordTrace (prefixWord ++ tailWord_1631021) baseStart_1631021 baseEnd_1631021 := by
    simpa [prefixWord, tailWord_1631021, baseEnd_1631021] using wordTrace_append hprefix tailTrace_1631021
  have hstable : (prefixWord ++ tailWord_1631021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631021).length < 2 ^ (prefixWord ++ tailWord_1631021).sum := by decide
  have hdescent : baseEnd_1631021 < baseStart_1631021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631053 : List Nat := [1, 6, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1631053 : Nat := 118140960795 + 1631053 * 2 ^ 59
def prefixEnd_1631053 : Nat := 4983230072969 + 3 ^ 40 * 1631053 * 2
def baseEnd_1631053 : Nat := 186114258212869384741429

theorem tailTrace_1631053 : CollatzResearch.WordTrace tailWord_1631053 prefixEnd_1631053 186114258212869384741429 := by
  unfold tailWord_1631053
  simp only [CollatzResearch.WordTrace]
  refine ⟨59489390159981017520081813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39659593439987345013387875 59489390159981017520081813)
  ·
    refine ⟨2788565163749110196253835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59489390159981017520081813 2788565163749110196253835)
    ·
      refine ⟨4182847745623665294380753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2788565163749110196253835 4182847745623665294380753)
      ·
        refine ⟨3137135809217748970785565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4182847745623665294380753 3137135809217748970785565)
        ·
          refine ⟨1176425928456655864044587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3137135809217748970785565 1176425928456655864044587)
          ·
            refine ⟨1764638892684983796066881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176425928456655864044587 1764638892684983796066881)
            ·
              refine ⟨1323479169513737847050161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1764638892684983796066881 1323479169513737847050161)
              ·
                refine ⟨992609377135303385287621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323479169513737847050161 992609377135303385287621)
                ·
                  refine ⟨186114258212869384741429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 992609377135303385287621 186114258212869384741429)
                  ·
                    rfl

theorem cell22_1631053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1631053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631053 prefixEnd_1631053 := by exact prefixLift 1631053
  have htrace : WordTrace (prefixWord ++ tailWord_1631053) baseStart_1631053 baseEnd_1631053 := by
    simpa [prefixWord, tailWord_1631053, baseEnd_1631053] using wordTrace_append hprefix tailTrace_1631053
  have hstable : (prefixWord ++ tailWord_1631053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631053).length < 2 ^ (prefixWord ++ tailWord_1631053).sum := by decide
  have hdescent : baseEnd_1631053 < baseStart_1631053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631075 : List Nat := [1, 1, 1, 5, 3, 1, 2, 3, 5]
def baseStart_1631075 : Nat := 118140960795 + 1631075 * 2 ^ 59
def prefixEnd_1631075 : Nat := 4983230072969 + 3 ^ 40 * 1631075 * 2
def baseEnd_1631075 : Nat := 186116768562735810058073

theorem tailTrace_1631075 : CollatzResearch.WordTrace tailWord_1631075 prefixEnd_1631075 186116768562735810058073 := by
  unfold tailWord_1631075
  simp only [CollatzResearch.WordTrace]
  refine ⟨59490192565901315277382679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39660128377267543518255119 59490192565901315277382679)
  ·
    refine ⟨89235288848851972916074019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59490192565901315277382679 89235288848851972916074019)
    ·
      refine ⟨133852933273277959374111029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89235288848851972916074019 133852933273277959374111029)
      ·
        refine ⟨12548712494369808691322909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133852933273277959374111029 12548712494369808691322909)
        ·
          refine ⟨4705767185388678259246091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12548712494369808691322909 4705767185388678259246091)
          ·
            refine ⟨7058650778083017388869137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4705767185388678259246091 7058650778083017388869137)
            ·
              refine ⟨5293988083562263041651853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7058650778083017388869137 5293988083562263041651853)
              ·
                refine ⟨1985245531335848640619445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5293988083562263041651853 1985245531335848640619445)
                ·
                  refine ⟨186116768562735810058073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1985245531335848640619445 186116768562735810058073)
                  ·
                    rfl

theorem cell22_1631075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 5].length) (baseStart_1631075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631075 prefixEnd_1631075 := by exact prefixLift 1631075
  have htrace : WordTrace (prefixWord ++ tailWord_1631075) baseStart_1631075 baseEnd_1631075 := by
    simpa [prefixWord, tailWord_1631075, baseEnd_1631075] using wordTrace_append hprefix tailTrace_1631075
  have hstable : (prefixWord ++ tailWord_1631075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631075).length < 2 ^ (prefixWord ++ tailWord_1631075).sum := by decide
  have hdescent : baseEnd_1631075 < baseStart_1631075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631148 : List Nat := [2, 2, 1, 1, 1, 1, 2, 12]
def baseStart_1631148 : Nat := 118140960795 + 1631148 * 2 ^ 59
def prefixEnd_1631148 : Nat := 4983230072969 + 3 ^ 40 * 1631148 * 2
def baseEnd_1631148 : Nat := 62041699453339952566555

theorem tailTrace_1631148 : CollatzResearch.WordTrace tailWord_1631148 prefixEnd_1631148 62041699453339952566555 := by
  unfold tailWord_1631148
  simp only [CollatzResearch.WordTrace]
  refine ⟨29746427547318424372395049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39661903396424565829860065 29746427547318424372395049)
  ·
    refine ⟨22309820660488818279296287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29746427547318424372395049 22309820660488818279296287)
    ·
      refine ⟨33464730990733227418944431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22309820660488818279296287 33464730990733227418944431)
      ·
        refine ⟨50197096486099841128416647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33464730990733227418944431 50197096486099841128416647)
        ·
          refine ⟨75295644729149761692624971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50197096486099841128416647 75295644729149761692624971)
          ·
            refine ⟨112943467093724642538937457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75295644729149761692624971 112943467093724642538937457)
            ·
              refine ⟨84707600320293481904203093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112943467093724642538937457 84707600320293481904203093)
              ·
                refine ⟨62041699453339952566555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 84707600320293481904203093 62041699453339952566555)
                ·
                  rfl

theorem cell22_1631148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 12].length) (baseStart_1631148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631148 prefixEnd_1631148 := by exact prefixLift 1631148
  have htrace : WordTrace (prefixWord ++ tailWord_1631148) baseStart_1631148 baseEnd_1631148 := by
    simpa [prefixWord, tailWord_1631148, baseEnd_1631148] using wordTrace_append hprefix tailTrace_1631148
  have hstable : (prefixWord ++ tailWord_1631148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631148).length < 2 ^ (prefixWord ++ tailWord_1631148).sum := by decide
  have hdescent : baseEnd_1631148 < baseStart_1631148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631163 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 4, 7]
def baseStart_1631163 : Nat := 118140960795 + 1631163 * 2 ^ 59
def prefixEnd_1631163 : Nat := 4983230072969 + 3 ^ 40 * 1631163 * 2
def baseEnd_1631163 : Nat := 558380429886604533973949

theorem tailTrace_1631163 : CollatzResearch.WordTrace tailWord_1631163 prefixEnd_1631163 558380429886604533973949 := by
  unfold tailWord_1631163
  simp only [CollatzResearch.WordTrace]
  refine ⟨59493402189582506306586143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39662268126388337537724095 59493402189582506306586143)
  ·
    refine ⟨89240103284373759459879215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59493402189582506306586143 89240103284373759459879215)
    ·
      refine ⟨133860154926560639189818823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89240103284373759459879215 133860154926560639189818823)
      ·
        refine ⟨200790232389840958784728235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133860154926560639189818823 200790232389840958784728235)
        ·
          refine ⟨301185348584761438177092353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200790232389840958784728235 301185348584761438177092353)
          ·
            refine ⟨225889011438571078632819265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301185348584761438177092353 225889011438571078632819265)
            ·
              refine ⟨169416758578928308974614449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225889011438571078632819265 169416758578928308974614449)
              ·
                refine ⟨127062568934196231730960837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169416758578928308974614449 127062568934196231730960837)
                ·
                  refine ⟨23824231675161793449555157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127062568934196231730960837 23824231675161793449555157)
                  ·
                    refine ⟨558380429886604533973949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23824231675161793449555157 558380429886604533973949)
                    ·
                      rfl

theorem cell22_1631163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_1631163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631163 prefixEnd_1631163 := by exact prefixLift 1631163
  have htrace : WordTrace (prefixWord ++ tailWord_1631163) baseStart_1631163 baseEnd_1631163 := by
    simpa [prefixWord, tailWord_1631163, baseEnd_1631163] using wordTrace_append hprefix tailTrace_1631163
  have hstable : (prefixWord ++ tailWord_1631163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631163).length < 2 ^ (prefixWord ++ tailWord_1631163).sum := by decide
  have hdescent : baseEnd_1631163 < baseStart_1631163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631186 : List Nat := [3, 2, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_1631186 : Nat := 118140960795 + 1631186 * 2 ^ 59
def prefixEnd_1631186 : Nat := 4983230072969 + 3 ^ 40 * 1631186 * 2
def baseEnd_1631186 : Nat := 558388303256640140648879

theorem tailTrace_1631186 : CollatzResearch.WordTrace tailWord_1631186 prefixEnd_1631186 558388303256640140648879 := by
  unfold tailWord_1631186
  simp only [CollatzResearch.WordTrace]
  refine ⟨14873560267124795308668353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39662827378999454156448941 14873560267124795308668353)
  ·
    refine ⟨11155170200343596481501265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14873560267124795308668353 11155170200343596481501265)
    ·
      refine ⟨8366377650257697361125949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11155170200343596481501265 8366377650257697361125949)
      ·
        refine ⟨3137391618846636510422231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8366377650257697361125949 3137391618846636510422231)
        ·
          refine ⟨4706087428269954765633347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3137391618846636510422231 4706087428269954765633347)
          ·
            refine ⟨7059131142404932148450021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706087428269954765633347 7059131142404932148450021)
            ·
              refine ⟨1323587089200924777834379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7059131142404932148450021 1323587089200924777834379)
              ·
                refine ⟨1985380633801387166751569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1323587089200924777834379 1985380633801387166751569)
                ·
                  refine ⟨1489035475351040375063677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1985380633801387166751569 1489035475351040375063677)
                  ·
                    refine ⟨558388303256640140648879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1489035475351040375063677 558388303256640140648879)
                    ·
                      rfl

theorem cell22_1631186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_1631186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631186 prefixEnd_1631186 := by exact prefixLift 1631186
  have htrace : WordTrace (prefixWord ++ tailWord_1631186) baseStart_1631186 baseEnd_1631186 := by
    simpa [prefixWord, tailWord_1631186, baseEnd_1631186] using wordTrace_append hprefix tailTrace_1631186
  have hstable : (prefixWord ++ tailWord_1631186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631186).length < 2 ^ (prefixWord ++ tailWord_1631186).sum := by decide
  have hdescent : baseEnd_1631186 < baseStart_1631186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631225 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 2, 5]
def baseStart_1631225 : Nat := 118140960795 + 1631225 * 2 ^ 59
def prefixEnd_1631225 : Nat := 4983230072969 + 3 ^ 40 * 1631225 * 2
def baseEnd_1631225 : Nat := 558401653753657038923759

theorem tailTrace_1631225 : CollatzResearch.WordTrace tailWord_1631225 prefixEnd_1631225 558401653753657038923759 := by
  unfold tailWord_1631225
  simp only [CollatzResearch.WordTrace]
  refine ⟨59495663515357890895343129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39663775676905260596895419 59495663515357890895343129)
  ·
    refine ⟨44621747636518418171507347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59495663515357890895343129 44621747636518418171507347)
    ·
      refine ⟨66932621454777627257261021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44621747636518418171507347 66932621454777627257261021)
      ·
        refine ⟨25099733045541610221472883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66932621454777627257261021 25099733045541610221472883)
        ·
          refine ⟨37649599568312415332209325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25099733045541610221472883 37649599568312415332209325)
          ·
            refine ⟨14118599838117155749578497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37649599568312415332209325 14118599838117155749578497)
            ·
              refine ⟨10588949878587866812183873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14118599838117155749578497 10588949878587866812183873)
              ·
                refine ⟨7941712408940900109137905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10588949878587866812183873 7941712408940900109137905)
                ·
                  refine ⟨5956284306705675081853429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7941712408940900109137905 5956284306705675081853429)
                  ·
                    refine ⟨558401653753657038923759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5956284306705675081853429 558401653753657038923759)
                    ·
                      rfl

theorem cell22_1631225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_1631225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631225 prefixEnd_1631225 := by exact prefixLift 1631225
  have htrace : WordTrace (prefixWord ++ tailWord_1631225) baseStart_1631225 baseEnd_1631225 := by
    simpa [prefixWord, tailWord_1631225, baseEnd_1631225] using wordTrace_append hprefix tailTrace_1631225
  have hstable : (prefixWord ++ tailWord_1631225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631225).length < 2 ^ (prefixWord ++ tailWord_1631225).sum := by decide
  have hdescent : baseEnd_1631225 < baseStart_1631225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631242 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_1631242 : Nat := 118140960795 + 1631242 * 2 ^ 59
def prefixEnd_1631242 : Nat := 4983230072969 + 3 ^ 40 * 1631242 * 2
def baseEnd_1631242 : Nat := 558407473201074661248707

theorem tailTrace_1631242 : CollatzResearch.WordTrace tailWord_1631242 prefixEnd_1631242 558407473201074661248707 := by
  unfold tailWord_1631242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14874070889074075699677995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39664189037530868532474653 14874070889074075699677995)
  ·
    refine ⟨22311106333611113549516993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14874070889074075699677995 22311106333611113549516993)
    ·
      refine ⟨16733329750208335162137745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22311106333611113549516993 16733329750208335162137745)
      ·
        refine ⟨12549997312656251371603309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16733329750208335162137745 12549997312656251371603309)
        ·
          refine ⟨4706248992246094264351241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12549997312656251371603309 4706248992246094264351241)
          ·
            refine ⟨3529686744184570698263431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4706248992246094264351241 3529686744184570698263431)
            ·
              refine ⟨5294530116276856047395147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529686744184570698263431 5294530116276856047395147)
              ·
                refine ⟨7941795174415284071092721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5294530116276856047395147 7941795174415284071092721)
                ·
                  refine ⟨5956346380811463053319541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7941795174415284071092721 5956346380811463053319541)
                  ·
                    refine ⟨558407473201074661248707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5956346380811463053319541 558407473201074661248707)
                    ·
                      rfl

theorem cell22_1631242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_1631242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631242 prefixEnd_1631242 := by exact prefixLift 1631242
  have htrace : WordTrace (prefixWord ++ tailWord_1631242) baseStart_1631242 baseEnd_1631242 := by
    simpa [prefixWord, tailWord_1631242, baseEnd_1631242] using wordTrace_append hprefix tailTrace_1631242
  have hstable : (prefixWord ++ tailWord_1631242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631242).length < 2 ^ (prefixWord ++ tailWord_1631242).sum := by decide
  have hdescent : baseEnd_1631242 < baseStart_1631242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631289 : List Nat := [1, 2, 1, 5, 2, 1, 2, 4, 4]
def baseStart_1631289 : Nat := 118140960795 + 1631289 * 2 ^ 59
def prefixEnd_1631289 : Nat := 4983230072969 + 3 ^ 40 * 1631289 * 2
def baseEnd_1631289 : Nat := 186141187420527401774521

theorem tailTrace_1631289 : CollatzResearch.WordTrace tailWord_1631289 prefixEnd_1631289 186141187420527401774521 := by
  unfold tailWord_1631289
  simp only [CollatzResearch.WordTrace]
  refine ⟨59497997787126029825672921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39665331858084019883781947 59497997787126029825672921)
  ·
    refine ⟨44623498340344522369254691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59497997787126029825672921 44623498340344522369254691)
    ·
      refine ⟨66935247510516783553882037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44623498340344522369254691 66935247510516783553882037)
      ·
        refine ⟨6275179454110948458176441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66935247510516783553882037 6275179454110948458176441)
        ·
          refine ⟨4706384590583211343632331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6275179454110948458176441 4706384590583211343632331)
          ·
            refine ⟨7059576885874817015448497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706384590583211343632331 7059576885874817015448497)
            ·
              refine ⟨5294682664406112761586373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7059576885874817015448497 5294682664406112761586373)
              ·
                refine ⟨992752999576146142797445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5294682664406112761586373 992752999576146142797445)
                ·
                  refine ⟨186141187420527401774521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 992752999576146142797445 186141187420527401774521)
                  ·
                    rfl

theorem cell22_1631289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 4].length) (baseStart_1631289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631289 prefixEnd_1631289 := by exact prefixLift 1631289
  have htrace : WordTrace (prefixWord ++ tailWord_1631289) baseStart_1631289 baseEnd_1631289 := by
    simpa [prefixWord, tailWord_1631289, baseEnd_1631289] using wordTrace_append hprefix tailTrace_1631289
  have hstable : (prefixWord ++ tailWord_1631289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631289).length < 2 ^ (prefixWord ++ tailWord_1631289).sum := by decide
  have hdescent : baseEnd_1631289 < baseStart_1631289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631336 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 2, 4]
def baseStart_1631336 : Nat := 118140960795 + 1631336 * 2 ^ 59
def prefixEnd_1631336 : Nat := 4983230072969 + 3 ^ 40 * 1631336 * 2
def baseEnd_1631336 : Nat := 558439651322089749398419

theorem tailTrace_1631336 : CollatzResearch.WordTrace tailWord_1631336 prefixEnd_1631336 558439651322089749398419 := by
  unfold tailWord_1631336
  simp only [CollatzResearch.WordTrace]
  refine ⟨29749856008977878426316931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39666474678637171235089241 29749856008977878426316931)
  ·
    refine ⟨44624784013466817639475397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29749856008977878426316931 44624784013466817639475397)
    ·
      refine ⟨8367147002525028307401637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44624784013466817639475397 8367147002525028307401637)
      ·
        refine ⟨1568840062973442807637807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8367147002525028307401637 1568840062973442807637807)
        ·
          refine ⟨2353260094460164211456711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568840062973442807637807 2353260094460164211456711)
          ·
            refine ⟨3529890141690246317185067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353260094460164211456711 3529890141690246317185067)
            ·
              refine ⟨5294835212535369475777601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529890141690246317185067 5294835212535369475777601)
              ·
                refine ⟨3971126409401527106833201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5294835212535369475777601 3971126409401527106833201)
                ·
                  refine ⟨2978344807051145330124901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3971126409401527106833201 2978344807051145330124901)
                  ·
                    refine ⟨558439651322089749398419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2978344807051145330124901 558439651322089749398419)
                    ·
                      rfl

theorem cell22_1631336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_1631336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631336 prefixEnd_1631336 := by exact prefixLift 1631336
  have htrace : WordTrace (prefixWord ++ tailWord_1631336) baseStart_1631336 baseEnd_1631336 := by
    simpa [prefixWord, tailWord_1631336, baseEnd_1631336] using wordTrace_append hprefix tailTrace_1631336
  have hstable : (prefixWord ++ tailWord_1631336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631336).length < 2 ^ (prefixWord ++ tailWord_1631336).sum := by decide
  have hdescent : baseEnd_1631336 < baseStart_1631336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631409 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 3, 4]
def baseStart_1631409 : Nat := 118140960795 + 1631409 * 2 ^ 59
def prefixEnd_1631409 : Nat := 4983230072969 + 3 ^ 40 * 1631409 * 2
def baseEnd_1631409 : Nat := 558464640713941892323195

theorem tailTrace_1631409 : CollatzResearch.WordTrace tailWord_1631409 prefixEnd_1631409 558464640713941892323195 := by
  unfold tailWord_1631409
  simp only [CollatzResearch.WordTrace]
  refine ⟨59502374546691290320041281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39668249697794193546694187 59502374546691290320041281)
  ·
    refine ⟨44626780910018467740030961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59502374546691290320041281 44626780910018467740030961)
    ·
      refine ⟨33470085682513850805023221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44626780910018467740030961 33470085682513850805023221)
      ·
        refine ⟨3137820532735673512970927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33470085682513850805023221 3137820532735673512970927)
        ·
          refine ⟨4706730799103510269456391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3137820532735673512970927 4706730799103510269456391)
          ·
            refine ⟨7060096198655265404184587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706730799103510269456391 7060096198655265404184587)
            ·
              refine ⟨10590144297982898106276881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7060096198655265404184587 10590144297982898106276881)
              ·
                refine ⟨7942608223487173579707661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10590144297982898106276881 7942608223487173579707661)
                ·
                  refine ⟨2978478083807690092390373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7942608223487173579707661 2978478083807690092390373)
                  ·
                    refine ⟨558464640713941892323195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2978478083807690092390373 558464640713941892323195)
                    ·
                      rfl

theorem cell22_1631409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_1631409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631409 prefixEnd_1631409 := by exact prefixLift 1631409
  have htrace : WordTrace (prefixWord ++ tailWord_1631409) baseStart_1631409 baseEnd_1631409 := by
    simpa [prefixWord, tailWord_1631409, baseEnd_1631409] using wordTrace_append hprefix tailTrace_1631409
  have hstable : (prefixWord ++ tailWord_1631409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631409).length < 2 ^ (prefixWord ++ tailWord_1631409).sum := by decide
  have hdescent : baseEnd_1631409 < baseStart_1631409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631424 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 6]
def baseStart_1631424 : Nat := 118140960795 + 1631424 * 2 ^ 59
def prefixEnd_1631424 : Nat := 4983230072969 + 3 ^ 40 * 1631424 * 2
def baseEnd_1631424 : Nat := 186156591840162284399383

theorem tailTrace_1631424 : CollatzResearch.WordTrace tailWord_1631424 prefixEnd_1631424 186156591840162284399383 := by
  unfold tailWord_1631424
  simp only [CollatzResearch.WordTrace]
  refine ⟨29751460820818473940918663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39668614427757965254558217 29751460820818473940918663)
  ·
    refine ⟨44627191231227710911377995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29751460820818473940918663 44627191231227710911377995)
    ·
      refine ⟨66940786846841566367066993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44627191231227710911377995 66940786846841566367066993)
      ·
        refine ⟨50205590135131174775300245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66940786846841566367066993 50205590135131174775300245)
        ·
          refine ⟨2353387037584273817592199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50205590135131174775300245 2353387037584273817592199)
          ·
            refine ⟨3530080556376410726388299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353387037584273817592199 3530080556376410726388299)
            ·
              refine ⟨5295120834564616089582449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3530080556376410726388299 5295120834564616089582449)
              ·
                refine ⟨3971340625923462067186837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5295120834564616089582449 3971340625923462067186837)
                ·
                  refine ⟨186156591840162284399383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3971340625923462067186837 186156591840162284399383)
                  ·
                    rfl

theorem cell22_1631424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 6].length) (baseStart_1631424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631424 prefixEnd_1631424 := by exact prefixLift 1631424
  have htrace : WordTrace (prefixWord ++ tailWord_1631424) baseStart_1631424 baseEnd_1631424 := by
    simpa [prefixWord, tailWord_1631424, baseEnd_1631424] using wordTrace_append hprefix tailTrace_1631424
  have hstable : (prefixWord ++ tailWord_1631424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631424).length < 2 ^ (prefixWord ++ tailWord_1631424).sum := by decide
  have hdescent : baseEnd_1631424 < baseStart_1631424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631456 : List Nat := [2, 1, 1, 3, 1, 4, 3, 2, 2, 3]
def baseStart_1631456 : Nat := 118140960795 + 1631456 * 2 ^ 59
def prefixEnd_1631456 : Nat := 4983230072969 + 3 ^ 40 * 1631456 * 2
def baseEnd_1631456 : Nat := 558480729774449436398051

theorem tailTrace_1631456 : CollatzResearch.WordTrace tailWord_1631456 prefixEnd_1631456 558480729774449436398051 := by
  unfold tailWord_1631456
  simp only [CollatzResearch.WordTrace]
  refine ⟨29752044388760508673501111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39669392518347344898001481 29752044388760508673501111)
  ·
    refine ⟨44628066583140763010251667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29752044388760508673501111 44628066583140763010251667)
    ·
      refine ⟨66942099874711144515377501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44628066583140763010251667 66942099874711144515377501)
      ·
        refine ⟨25103287453016679193266563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66942099874711144515377501 25103287453016679193266563)
        ·
          refine ⟨37654931179525018789899845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25103287453016679193266563 37654931179525018789899845)
          ·
            refine ⟨7060299596160941023106221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37654931179525018789899845 7060299596160941023106221)
            ·
              refine ⟨2647612348560352883664833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7060299596160941023106221 2647612348560352883664833)
              ·
                refine ⟨1985709261420264662748625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2647612348560352883664833 1985709261420264662748625)
                ·
                  refine ⟨1489281946065198497061469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1985709261420264662748625 1489281946065198497061469)
                  ·
                    refine ⟨558480729774449436398051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1489281946065198497061469 558480729774449436398051)
                    ·
                      rfl

theorem cell22_1631456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 2, 3].length) (baseStart_1631456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631456 prefixEnd_1631456 := by exact prefixLift 1631456
  have htrace : WordTrace (prefixWord ++ tailWord_1631456) baseStart_1631456 baseEnd_1631456 := by
    simpa [prefixWord, tailWord_1631456, baseEnd_1631456] using wordTrace_append hprefix tailTrace_1631456
  have hstable : (prefixWord ++ tailWord_1631456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631456).length < 2 ^ (prefixWord ++ tailWord_1631456).sum := by decide
  have hdescent : baseEnd_1631456 < baseStart_1631456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631486 : List Nat := [4, 2, 2, 1, 1, 2, 4, 6]
def baseStart_1631486 : Nat := 118140960795 + 1631486 * 2 ^ 59
def prefixEnd_1631486 : Nat := 4983230072969 + 3 ^ 40 * 1631486 * 2
def baseEnd_1631486 : Nat := 62054555487504373127551

theorem tailTrace_1631486 : CollatzResearch.WordTrace tailWord_1631486 prefixEnd_1631486 62054555487504373127551 := by
  unfold tailWord_1631486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7438147870926541558824289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39670121978274888313729541 7438147870926541558824289)
  ·
    refine ⟨5578610903194906169118217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7438147870926541558824289 5578610903194906169118217)
    ·
      refine ⟨4183958177396179626838663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5578610903194906169118217 4183958177396179626838663)
      ·
        refine ⟨6275937266094269440257995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4183958177396179626838663 6275937266094269440257995)
        ·
          refine ⟨9413905899141404160386993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6275937266094269440257995 9413905899141404160386993)
          ·
            refine ⟨7060429424356053120290245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9413905899141404160386993 7060429424356053120290245)
            ·
              refine ⟨1323830517066759960054421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7060429424356053120290245 1323830517066759960054421)
              ·
                refine ⟨62054555487504373127551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1323830517066759960054421 62054555487504373127551)
                ·
                  rfl

theorem cell22_1631486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_1631486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631486 prefixEnd_1631486 := by exact prefixLift 1631486
  have htrace : WordTrace (prefixWord ++ tailWord_1631486) baseStart_1631486 baseEnd_1631486 := by
    simpa [prefixWord, tailWord_1631486, baseEnd_1631486] using wordTrace_append hprefix tailTrace_1631486
  have hstable : (prefixWord ++ tailWord_1631486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631486).length < 2 ^ (prefixWord ++ tailWord_1631486).sum := by decide
  have hdescent : baseEnd_1631486 < baseStart_1631486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631497 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 9]
def baseStart_1631497 : Nat := 118140960795 + 1631497 * 2 ^ 59
def prefixEnd_1631497 : Nat := 4983230072969 + 3 ^ 40 * 1631497 * 2
def baseEnd_1631497 : Nat := 186164921637446332040975

theorem tailTrace_1631497 : CollatzResearch.WordTrace tailWord_1631497 prefixEnd_1631497 186164921637446332040975 := by
  unfold tailWord_1631497
  simp only [CollatzResearch.WordTrace]
  refine ⟨59505584170372481349244745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39670389446914987566163163 59505584170372481349244745)
  ·
    refine ⟨44629188127779361011933559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59505584170372481349244745 44629188127779361011933559)
    ·
      refine ⟨66943782191669041517900339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44629188127779361011933559 66943782191669041517900339)
      ·
        refine ⟨100415673287503562276850509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66943782191669041517900339 100415673287503562276850509)
        ·
          refine ⟨37655877482813835853818941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100415673287503562276850509 37655877482813835853818941)
          ·
            refine ⟨14120954056055188445182103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37655877482813835853818941 14120954056055188445182103)
            ·
              refine ⟨21181431084082782667773155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14120954056055188445182103 21181431084082782667773155)
              ·
                refine ⟨31772146626124174001659733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21181431084082782667773155 31772146626124174001659733)
                ·
                  refine ⟨186164921637446332040975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31772146626124174001659733 186164921637446332040975)
                  ·
                    rfl

theorem cell22_1631497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_1631497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631497 prefixEnd_1631497 := by exact prefixLift 1631497
  have htrace : WordTrace (prefixWord ++ tailWord_1631497) baseStart_1631497 baseEnd_1631497 := by
    simpa [prefixWord, tailWord_1631497, baseEnd_1631497] using wordTrace_append hprefix tailTrace_1631497
  have hstable : (prefixWord ++ tailWord_1631497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631497).length < 2 ^ (prefixWord ++ tailWord_1631497).sum := by decide
  have hdescent : baseEnd_1631497 < baseStart_1631497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631514 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 7]
def baseStart_1631514 : Nat := 118140960795 + 1631514 * 2 ^ 59
def prefixEnd_1631514 : Nat := 4983230072969 + 3 ^ 40 * 1631514 * 2
def baseEnd_1631514 : Nat := 186166861453252206149291

theorem tailTrace_1631514 : CollatzResearch.WordTrace tailWord_1631514 prefixEnd_1631514 186166861453252206149291 := by
  unfold tailWord_1631514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14876551052827723313153399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39670802807540595501742397 14876551052827723313153399)
  ·
    refine ⟨22314826579241584969730099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14876551052827723313153399 22314826579241584969730099)
    ·
      refine ⟨33472239868862377454595149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22314826579241584969730099 33472239868862377454595149)
      ·
        refine ⟨12552089950823391545473181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33472239868862377454595149 12552089950823391545473181)
        ·
          refine ⟨4707033731558771829552443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12552089950823391545473181 4707033731558771829552443)
          ·
            refine ⟨7060550597338157744328665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4707033731558771829552443 7060550597338157744328665)
            ·
              refine ⟨5295412948003618308246499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7060550597338157744328665 5295412948003618308246499)
              ·
                refine ⟨7943119422005427462369749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295412948003618308246499 7943119422005427462369749)
                ·
                  refine ⟨186166861453252206149291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7943119422005427462369749 186166861453252206149291)
                  ·
                    rfl

theorem cell22_1631514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_1631514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631514 prefixEnd_1631514 := by exact prefixLift 1631514
  have htrace : WordTrace (prefixWord ++ tailWord_1631514) baseStart_1631514 baseEnd_1631514 := by
    simpa [prefixWord, tailWord_1631514, baseEnd_1631514] using wordTrace_append hprefix tailTrace_1631514
  have hstable : (prefixWord ++ tailWord_1631514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631514).length < 2 ^ (prefixWord ++ tailWord_1631514).sum := by decide
  have hdescent : baseEnd_1631514 < baseStart_1631514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631565 : List Nat := [1, 6, 1, 3, 1, 1, 2, 2, 5]
def baseStart_1631565 : Nat := 118140960795 + 1631565 * 2 ^ 59
def prefixEnd_1631565 : Nat := 4983230072969 + 3 ^ 40 * 1631565 * 2
def baseEnd_1631565 : Nat := 186172680900669828474239

theorem tailTrace_1631565 : CollatzResearch.WordTrace tailWord_1631565 prefixEnd_1631565 186172680900669828474239 := by
  unfold tailWord_1631565
  simp only [CollatzResearch.WordTrace]
  refine ⟨59508064334126128962720149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39672042889417419308480099 59508064334126128962720149)
  ·
    refine ⟨2789440515662162295127507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59508064334126128962720149 2789440515662162295127507)
    ·
      refine ⟨4184160773493243442691261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2789440515662162295127507 4184160773493243442691261)
      ·
        refine ⟨1569060290059966291009223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4184160773493243442691261 1569060290059966291009223)
        ·
          refine ⟨2353590435089949436513835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569060290059966291009223 2353590435089949436513835)
          ·
            refine ⟨3530385652634924154770753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353590435089949436513835 3530385652634924154770753)
            ·
              refine ⟨2647789239476193116078065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3530385652634924154770753 2647789239476193116078065)
              ·
                refine ⟨1985841929607144837058549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2647789239476193116078065 1985841929607144837058549)
                ·
                  refine ⟨186172680900669828474239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1985841929607144837058549 186172680900669828474239)
                  ·
                    rfl

theorem cell22_1631565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_1631565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631565 prefixEnd_1631565 := by exact prefixLift 1631565
  have htrace : WordTrace (prefixWord ++ tailWord_1631565) baseStart_1631565 baseEnd_1631565 := by
    simpa [prefixWord, tailWord_1631565, baseEnd_1631565] using wordTrace_append hprefix tailTrace_1631565
  have hstable : (prefixWord ++ tailWord_1631565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631565).length < 2 ^ (prefixWord ++ tailWord_1631565).sum := by decide
  have hdescent : baseEnd_1631565 < baseStart_1631565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631576 : List Nat := [2, 1, 2, 2, 1, 1, 5, 4, 4]
def baseStart_1631576 : Nat := 118140960795 + 1631576 * 2 ^ 59
def prefixEnd_1631576 : Nat := 4983230072969 + 3 ^ 40 * 1631576 * 2
def baseEnd_1631576 : Nat := 186173936075603041132561

theorem tailTrace_1631576 : CollatzResearch.WordTrace tailWord_1631576 prefixEnd_1631576 186173936075603041132561 := by
  unfold tailWord_1631576
  simp only [CollatzResearch.WordTrace]
  refine ⟨29754232768543138920685291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39672310358057518560913721 29754232768543138920685291)
  ·
    refine ⟨44631349152814708381027937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29754232768543138920685291 44631349152814708381027937)
    ·
      refine ⟨33473511864611031285770953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44631349152814708381027937 33473511864611031285770953)
      ·
        refine ⟨25105133898458273464328215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33473511864611031285770953 25105133898458273464328215)
        ·
          refine ⟨37657700847687410196492323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25105133898458273464328215 37657700847687410196492323)
          ·
            refine ⟨56486551271531115294738485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37657700847687410196492323 56486551271531115294738485)
            ·
              refine ⟨5295614181706042058881733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56486551271531115294738485 5295614181706042058881733)
              ·
                refine ⟨992927659069882886040325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5295614181706042058881733 992927659069882886040325)
                ·
                  refine ⟨186173936075603041132561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 992927659069882886040325 186173936075603041132561)
                  ·
                    rfl

theorem cell22_1631576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 4].length) (baseStart_1631576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631576 prefixEnd_1631576 := by exact prefixLift 1631576
  have htrace : WordTrace (prefixWord ++ tailWord_1631576) baseStart_1631576 baseEnd_1631576 := by
    simpa [prefixWord, tailWord_1631576, baseEnd_1631576] using wordTrace_append hprefix tailTrace_1631576
  have hstable : (prefixWord ++ tailWord_1631576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631576).length < 2 ^ (prefixWord ++ tailWord_1631576).sum := by decide
  have hdescent : baseEnd_1631576 < baseStart_1631576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631589 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_1631589 : Nat := 118140960795 + 1631589 * 2 ^ 59
def prefixEnd_1631589 : Nat := 4983230072969 + 3 ^ 40 * 1631589 * 2
def baseEnd_1631589 : Nat := 558526258392481422822643

theorem tailTrace_1631589 : CollatzResearch.WordTrace tailWord_1631589 prefixEnd_1631589 558526258392481422822643 := by
  unfold tailWord_1631589
  simp only [CollatzResearch.WordTrace]
  refine ⟨59508939686039181061593821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39672626457359454041062547 59508939686039181061593821)
  ·
    refine ⟨22315852382264692898097683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59508939686039181061593821 22315852382264692898097683)
    ·
      refine ⟨33473778573397039347146525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22315852382264692898097683 33473778573397039347146525)
      ·
        refine ⟨12552666965023889755179947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33473778573397039347146525 12552666965023889755179947)
        ·
          refine ⟨18829000447535834632769921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12552666965023889755179947 18829000447535834632769921)
          ·
            refine ⟨14121750335651875974577441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18829000447535834632769921 14121750335651875974577441)
            ·
              refine ⟨10591312751738906980933081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14121750335651875974577441 10591312751738906980933081)
              ·
                refine ⟨7943484563804180235699811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10591312751738906980933081 7943484563804180235699811)
                ·
                  refine ⟨11915226845706270353549717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7943484563804180235699811 11915226845706270353549717)
                  ·
                    refine ⟨558526258392481422822643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11915226845706270353549717 558526258392481422822643)
                    ·
                      rfl

theorem cell22_1631589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_1631589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631589 prefixEnd_1631589 := by exact prefixLift 1631589
  have htrace : WordTrace (prefixWord ++ tailWord_1631589) baseStart_1631589 baseEnd_1631589 := by
    simpa [prefixWord, tailWord_1631589, baseEnd_1631589] using wordTrace_append hprefix tailTrace_1631589
  have hstable : (prefixWord ++ tailWord_1631589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631589).length < 2 ^ (prefixWord ++ tailWord_1631589).sum := by decide
  have hdescent : baseEnd_1631589 < baseStart_1631589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631625 : List Nat := [1, 2, 1, 1, 7, 2, 1, 2, 2, 3]
def baseStart_1631625 : Nat := 118140960795 + 1631625 * 2 ^ 59
def prefixEnd_1631625 : Nat := 4983230072969 + 3 ^ 40 * 1631625 * 2
def baseEnd_1631625 : Nat := 558538581928189328922533

theorem tailTrace_1631625 : CollatzResearch.WordTrace tailWord_1631625 prefixEnd_1631625 558538581928189328922533 := by
  unfold tailWord_1631625
  simp only [CollatzResearch.WordTrace]
  refine ⟨59510252713908759209904329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39673501809272506139936219 59510252713908759209904329)
  ·
    refine ⟨44632689535431569407428247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59510252713908759209904329 44632689535431569407428247)
    ·
      refine ⟨66949034303147354111142371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44632689535431569407428247 66949034303147354111142371)
      ·
        refine ⟨100423551454721031166713557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66949034303147354111142371 100423551454721031166713557)
        ·
          refine ⟨2353676987220024167969849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 100423551454721031166713557 2353676987220024167969849)
          ·
            refine ⟨1765257740415018125977387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2353676987220024167969849 1765257740415018125977387)
            ·
              refine ⟨2647886610622527188966081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765257740415018125977387 2647886610622527188966081)
              ·
                refine ⟨1985914957966895391724561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2647886610622527188966081 1985914957966895391724561)
                ·
                  refine ⟨1489436218475171543793421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1985914957966895391724561 1489436218475171543793421)
                  ·
                    refine ⟨558538581928189328922533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1489436218475171543793421 558538581928189328922533)
                    ·
                      rfl

theorem cell22_1631625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 3].length) (baseStart_1631625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631625 prefixEnd_1631625 := by exact prefixLift 1631625
  have htrace : WordTrace (prefixWord ++ tailWord_1631625) baseStart_1631625 baseEnd_1631625 := by
    simpa [prefixWord, tailWord_1631625, baseEnd_1631625] using wordTrace_append hprefix tailTrace_1631625
  have hstable : (prefixWord ++ tailWord_1631625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631625).length < 2 ^ (prefixWord ++ tailWord_1631625).sum := by decide
  have hdescent : baseEnd_1631625 < baseStart_1631625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631664 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 4, 5]
def baseStart_1631664 : Nat := 118140960795 + 1631664 * 2 ^ 59
def prefixEnd_1631664 : Nat := 4983230072969 + 3 ^ 40 * 1631664 * 2
def baseEnd_1631664 : Nat := 558551932425206227197413

theorem tailTrace_1631664 : CollatzResearch.WordTrace tailWord_1631664 prefixEnd_1631664 558551932425206227197413 := by
  unfold tailWord_1631664
  simp only [CollatzResearch.WordTrace]
  refine ⟨29755837580383734435287023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39674450107178312580382697 29755837580383734435287023)
  ·
    refine ⟨44633756370575601652930535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29755837580383734435287023 44633756370575601652930535)
    ·
      refine ⟨66950634555863402479395803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44633756370575601652930535 66950634555863402479395803)
      ·
        refine ⟨100425951833795103719093705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66950634555863402479395803 100425951833795103719093705)
        ·
          refine ⟨75319463875346327789320279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100425951833795103719093705 75319463875346327789320279)
          ·
            refine ⟨112979195813019491683980419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75319463875346327789320279 112979195813019491683980419)
            ·
              refine ⟨169468793719529237525970629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112979195813019491683980419 169468793719529237525970629)
              ·
                refine ⟨31775398822411732036119493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169468793719529237525970629 31775398822411732036119493)
                ·
                  refine ⟨5957887279202199756772405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31775398822411732036119493 5957887279202199756772405)
                  ·
                    refine ⟨558551932425206227197413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5957887279202199756772405 558551932425206227197413)
                    ·
                      rfl

theorem cell22_1631664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_1631664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631664 prefixEnd_1631664 := by exact prefixLift 1631664
  have htrace : WordTrace (prefixWord ++ tailWord_1631664) baseStart_1631664 baseEnd_1631664 := by
    simpa [prefixWord, tailWord_1631664, baseEnd_1631664] using wordTrace_append hprefix tailTrace_1631664
  have hstable : (prefixWord ++ tailWord_1631664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631664).length < 2 ^ (prefixWord ++ tailWord_1631664).sum := by decide
  have hdescent : baseEnd_1631664 < baseStart_1631664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631713 : List Nat := [1, 2, 3, 1, 2, 3, 3, 2, 1, 4]
def baseStart_1631713 : Nat := 118140960795 + 1631713 * 2 ^ 59
def prefixEnd_1631713 : Nat := 4983230072969 + 3 ^ 40 * 1631713 * 2
def baseEnd_1631713 : Nat := 558568706126586432722263

theorem tailTrace_1631713 : CollatzResearch.WordTrace tailWord_1631713 prefixEnd_1631713 558568706126586432722263 := by
  unfold tailWord_1631713
  simp only [CollatzResearch.WordTrace]
  refine ⟨59513462337589950239107793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39675641558393300159405195 59513462337589950239107793)
  ·
    refine ⟨44635096753192462679330845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59513462337589950239107793 44635096753192462679330845)
    ·
      refine ⟨16738161282447173504749067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44635096753192462679330845 16738161282447173504749067)
      ·
        refine ⟨25107241923670760257123601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16738161282447173504749067 25107241923670760257123601)
        ·
          refine ⟨18830431442753070192842701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25107241923670760257123601 18830431442753070192842701)
          ·
            refine ⟨7061411791032401322316013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18830431442753070192842701 7061411791032401322316013)
            ·
              refine ⟨2648029421637150495868505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7061411791032401322316013 2648029421637150495868505)
              ·
                refine ⟨1986022066227862871901379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2648029421637150495868505 1986022066227862871901379)
                ·
                  refine ⟨2979033099341794307852069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986022066227862871901379 2979033099341794307852069)
                  ·
                    refine ⟨558568706126586432722263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2979033099341794307852069 558568706126586432722263)
                    ·
                      rfl

theorem cell22_1631713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_1631713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631713 prefixEnd_1631713 := by exact prefixLift 1631713
  have htrace : WordTrace (prefixWord ++ tailWord_1631713) baseStart_1631713 baseEnd_1631713 := by
    simpa [prefixWord, tailWord_1631713, baseEnd_1631713] using wordTrace_append hprefix tailTrace_1631713
  have hstable : (prefixWord ++ tailWord_1631713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631713).length < 2 ^ (prefixWord ++ tailWord_1631713).sum := by decide
  have hdescent : baseEnd_1631713 < baseStart_1631713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631745 : List Nat := [1, 2, 4, 1, 4, 1, 1, 4, 4]
def baseStart_1631745 : Nat := 118140960795 + 1631745 * 2 ^ 59
def prefixEnd_1631745 : Nat := 4983230072969 + 3 ^ 40 * 1631745 * 2
def baseEnd_1631745 : Nat := 186193220126849671974055

theorem tailTrace_1631745 : CollatzResearch.WordTrace tailWord_1631745 prefixEnd_1631745 186193220126849671974055 := by
  unfold tailWord_1631745
  simp only [CollatzResearch.WordTrace]
  refine ⟨59514629473474019704272689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39676419648982679802848459 59514629473474019704272689)
  ·
    refine ⟨44635972105105514778204517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59514629473474019704272689 44635972105105514778204517)
    ·
      refine ⟨8369244769707284020913347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44635972105105514778204517 8369244769707284020913347)
      ·
        refine ⟨12553867154560926031370021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8369244769707284020913347 12553867154560926031370021)
        ·
          refine ⟨2353850091480173630881879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12553867154560926031370021 2353850091480173630881879)
          ·
            refine ⟨3530775137220260446322819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353850091480173630881879 3530775137220260446322819)
            ·
              refine ⟨5296162705830390669484229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3530775137220260446322819 5296162705830390669484229)
              ·
                refine ⟨993030507343198250528293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5296162705830390669484229 993030507343198250528293)
                ·
                  refine ⟨186193220126849671974055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 993030507343198250528293 186193220126849671974055)
                  ·
                    rfl

theorem cell22_1631745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 4].length) (baseStart_1631745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631745 prefixEnd_1631745 := by exact prefixLift 1631745
  have htrace : WordTrace (prefixWord ++ tailWord_1631745) baseStart_1631745 baseEnd_1631745 := by
    simpa [prefixWord, tailWord_1631745, baseEnd_1631745] using wordTrace_append hprefix tailTrace_1631745
  have hstable : (prefixWord ++ tailWord_1631745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631745).length < 2 ^ (prefixWord ++ tailWord_1631745).sum := by decide
  have hdescent : baseEnd_1631745 < baseStart_1631745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631773 : List Nat := [1, 4, 2, 2, 1, 1, 5, 6]
def baseStart_1631773 : Nat := 118140960795 + 1631773 * 2 ^ 59
def prefixEnd_1631773 : Nat := 4983230072969 + 3 ^ 40 * 1631773 * 2
def baseEnd_1631773 : Nat := 62065471705862919580231

theorem tailTrace_1631773 : CollatzResearch.WordTrace tailWord_1631773 prefixEnd_1631773 62065471705862919580231 := by
  unfold tailWord_1631773
  simp only [CollatzResearch.WordTrace]
  refine ⟨59515650717372580486291973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39677100478248386990861315 59515650717372580486291973)
  ·
    refine ⟨11159184509507358841179745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59515650717372580486291973 11159184509507358841179745)
    ·
      refine ⟨8369388382130519130884809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11159184509507358841179745 8369388382130519130884809)
      ·
        refine ⟨6277041286597889348163607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8369388382130519130884809 6277041286597889348163607)
        ·
          refine ⟨9415561929896834022245411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6277041286597889348163607 9415561929896834022245411)
          ·
            refine ⟨14123342894845251033368117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9415561929896834022245411 14123342894845251033368117)
            ·
              refine ⟨1324063396391742284378261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14123342894845251033368117 1324063396391742284378261)
              ·
                refine ⟨62065471705862919580231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1324063396391742284378261 62065471705862919580231)
                ·
                  rfl

theorem cell22_1631773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 6].length) (baseStart_1631773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631773 prefixEnd_1631773 := by exact prefixLift 1631773
  have htrace : WordTrace (prefixWord ++ tailWord_1631773) baseStart_1631773 baseEnd_1631773 := by
    simpa [prefixWord, tailWord_1631773, baseEnd_1631773] using wordTrace_append hprefix tailTrace_1631773
  have hstable : (prefixWord ++ tailWord_1631773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631773).length < 2 ^ (prefixWord ++ tailWord_1631773).sum := by decide
  have hdescent : baseEnd_1631773 < baseStart_1631773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631882 : List Nat := [3, 1, 2, 3, 2, 3, 1, 2, 1, 4]
def baseStart_1631882 : Nat := 118140960795 + 1631882 * 2 ^ 59
def prefixEnd_1631882 : Nat := 4983230072969 + 3 ^ 40 * 1631882 * 2
def baseEnd_1631882 : Nat := 558626558280326325246745

theorem tailTrace_1631882 : CollatzResearch.WordTrace tailWord_1631882 prefixEnd_1631882 558626558280326325246745 := by
  unfold tailWord_1631882
  simp only [CollatzResearch.WordTrace]
  refine ⟨14879906568494423025502475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39679750849318461401339933 14879906568494423025502475)
  ·
    refine ⟨22319859852741634538253713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14879906568494423025502475 22319859852741634538253713)
    ·
      refine ⟨16739894889556225903690285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22319859852741634538253713 16739894889556225903690285)
      ·
        refine ⟨6277460583583584713883857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16739894889556225903690285 6277460583583584713883857)
        ·
          refine ⟨4708095437687688535412893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6277460583583584713883857 4708095437687688535412893)
          ·
            refine ⟨1765535789132883200779835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4708095437687688535412893 1765535789132883200779835)
            ·
              refine ⟨2648303683699324801169753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765535789132883200779835 2648303683699324801169753)
              ·
                refine ⟨1986227762774493600877315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2648303683699324801169753 1986227762774493600877315)
                ·
                  refine ⟨2979341644161740401315973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986227762774493600877315 2979341644161740401315973)
                  ·
                    refine ⟨558626558280326325246745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2979341644161740401315973 558626558280326325246745)
                    ·
                      rfl

theorem cell22_1631882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_1631882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631882 prefixEnd_1631882 := by exact prefixLift 1631882
  have htrace : WordTrace (prefixWord ++ tailWord_1631882) baseStart_1631882 baseEnd_1631882 := by
    simpa [prefixWord, tailWord_1631882, baseEnd_1631882] using wordTrace_append hprefix tailTrace_1631882
  have hstable : (prefixWord ++ tailWord_1631882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631882).length < 2 ^ (prefixWord ++ tailWord_1631882).sum := by decide
  have hdescent : baseEnd_1631882 < baseStart_1631882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631968 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 2, 5]
def baseStart_1631968 : Nat := 118140960795 + 1631968 * 2 ^ 59
def prefixEnd_1631968 : Nat := 4983230072969 + 3 ^ 40 * 1631968 * 2
def baseEnd_1631968 : Nat := 558655997837850767596481

theorem tailTrace_1631968 : CollatzResearch.WordTrace tailWord_1631968 prefixEnd_1631968 558655997837850767596481 := by
  unfold tailWord_1631968
  simp only [CollatzResearch.WordTrace]
  refine ⟨29761381475833064394820279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39681841967777419193093705 29761381475833064394820279)
  ·
    refine ⟨44642072213749596592230419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29761381475833064394820279 44642072213749596592230419)
    ·
      refine ⟨66963108320624394888345629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44642072213749596592230419 66963108320624394888345629)
      ·
        refine ⟨25111165620234148083129611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66963108320624394888345629 25111165620234148083129611)
        ·
          refine ⟨37666748430351222124694417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25111165620234148083129611 37666748430351222124694417)
          ·
            refine ⟨28250061322763416593520813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37666748430351222124694417 28250061322763416593520813)
            ·
              refine ⟨10593772996036281222570305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28250061322763416593520813 10593772996036281222570305)
              ·
                refine ⟨7945329747027210916927729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10593772996036281222570305 7945329747027210916927729)
                ·
                  refine ⟨5958997310270408187695797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7945329747027210916927729 5958997310270408187695797)
                  ·
                    refine ⟨558655997837850767596481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5958997310270408187695797 558655997837850767596481)
                    ·
                      rfl

theorem cell22_1631968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_1631968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1631968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1631968 prefixEnd_1631968 := by exact prefixLift 1631968
  have htrace : WordTrace (prefixWord ++ tailWord_1631968) baseStart_1631968 baseEnd_1631968 := by
    simpa [prefixWord, tailWord_1631968, baseEnd_1631968] using wordTrace_append hprefix tailTrace_1631968
  have hstable : (prefixWord ++ tailWord_1631968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631968).length < 2 ^ (prefixWord ++ tailWord_1631968).sum := by decide
  have hdescent : baseEnd_1631968 < baseStart_1631968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632015 : List Nat := [1, 1, 2, 1, 1, 1, 4, 7, 4]
def baseStart_1632015 : Nat := 118140960795 + 1632015 * 2 ^ 59
def prefixEnd_1632015 : Nat := 4983230072969 + 3 ^ 40 * 1632015 * 2
def baseEnd_1632015 : Nat := 186224028966119437223779

theorem tailTrace_1632015 : CollatzResearch.WordTrace tailWord_1632015 prefixEnd_1632015 186224028966119437223779 := by
  unfold tailWord_1632015
  simp only [CollatzResearch.WordTrace]
  refine ⟨59524477182495855816601499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39682984788330570544400999 59524477182495855816601499)
  ·
    refine ⟨89286715773743783724902249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59524477182495855816601499 89286715773743783724902249)
    ·
      refine ⟨66965036830307837793676687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89286715773743783724902249 66965036830307837793676687)
      ·
        refine ⟨100447555245461756690515031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66965036830307837793676687 100447555245461756690515031)
        ·
          refine ⟨150671332868192635035772547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100447555245461756690515031 150671332868192635035772547)
          ·
            refine ⟨226006999302288952553658821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150671332868192635035772547 226006999302288952553658821)
            ·
              refine ⟨42376312369179178603811029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226006999302288952553658821 42376312369179178603811029)
              ·
                refine ⟨993194821152636998526821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42376312369179178603811029 993194821152636998526821)
                ·
                  refine ⟨186224028966119437223779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 993194821152636998526821 186224028966119437223779)
                  ·
                    rfl

theorem cell22_1632015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 4].length) (baseStart_1632015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632015 prefixEnd_1632015 := by exact prefixLift 1632015
  have htrace : WordTrace (prefixWord ++ tailWord_1632015) baseStart_1632015 baseEnd_1632015 := by
    simpa [prefixWord, tailWord_1632015, baseEnd_1632015] using wordTrace_append hprefix tailTrace_1632015
  have hstable : (prefixWord ++ tailWord_1632015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632015).length < 2 ^ (prefixWord ++ tailWord_1632015).sum := by decide
  have hdescent : baseEnd_1632015 < baseStart_1632015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632062 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1632062 : Nat := 118140960795 + 1632062 * 2 ^ 59
def prefixEnd_1632062 : Nat := 4983230072969 + 3 ^ 40 * 1632062 * 2
def baseEnd_1632062 : Nat := 558688175958865855746193

theorem tailTrace_1632062 : CollatzResearch.WordTrace tailWord_1632062 prefixEnd_1632062 558688175958865855746193 := by
  unfold tailWord_1632062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7440773926665697855445305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39684127608883721895708293 7440773926665697855445305)
  ·
    refine ⟨5580580444999273391583979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7440773926665697855445305 5580580444999273391583979)
    ·
      refine ⟨8370870667498910087375969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5580580444999273391583979 8370870667498910087375969)
      ·
        refine ⟨6278153000624182565531977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8370870667498910087375969 6278153000624182565531977)
        ·
          refine ⟨4708614750468136924148983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6278153000624182565531977 4708614750468136924148983)
          ·
            refine ⟨7062922125702205386223475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4708614750468136924148983 7062922125702205386223475)
            ·
              refine ⟨10594383188553308079335213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7062922125702205386223475 10594383188553308079335213)
              ·
                refine ⟨3972893695707490529750705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10594383188553308079335213 3972893695707490529750705)
                ·
                  refine ⟨2979670271780617897313029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3972893695707490529750705 2979670271780617897313029)
                  ·
                    refine ⟨558688175958865855746193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2979670271780617897313029 558688175958865855746193)
                    ·
                      rfl

theorem cell22_1632062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1632062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632062 prefixEnd_1632062 := by exact prefixLift 1632062
  have htrace : WordTrace (prefixWord ++ tailWord_1632062) baseStart_1632062 baseEnd_1632062 := by
    simpa [prefixWord, tailWord_1632062, baseEnd_1632062] using wordTrace_append hprefix tailTrace_1632062
  have hstable : (prefixWord ++ tailWord_1632062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632062).length < 2 ^ (prefixWord ++ tailWord_1632062).sum := by decide
  have hdescent : baseEnd_1632062 < baseStart_1632062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632167 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 6]
def baseStart_1632167 : Nat := 118140960795 + 1632167 * 2 ^ 59
def prefixEnd_1632167 : Nat := 4983230072969 + 3 ^ 40 * 1632167 * 2
def baseEnd_1632167 : Nat := 186241373201560193956957

theorem tailTrace_1632167 : CollatzResearch.WordTrace tailWord_1632167 prefixEnd_1632167 186241373201560193956957 := by
  unfold tailWord_1632167
  simp only [CollatzResearch.WordTrace]
  refine ⟨59530021077945185776134755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39686680718630123850756503 59530021077945185776134755)
  ·
    refine ⟨89295031616917778664202133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59530021077945185776134755 89295031616917778664202133)
    ·
      refine ⟨4185704607043020874884475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89295031616917778664202133 4185704607043020874884475)
      ·
        refine ⟨6278556910564531312326713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4185704607043020874884475 6278556910564531312326713)
        ·
          refine ⟨4708917682923398484245035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6278556910564531312326713 4708917682923398484245035)
          ·
            refine ⟨7063376524385097726367553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4708917682923398484245035 7063376524385097726367553)
            ·
              refine ⟨5297532393288823294775665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7063376524385097726367553 5297532393288823294775665)
              ·
                refine ⟨3973149294966617471081749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5297532393288823294775665 3973149294966617471081749)
                ·
                  refine ⟨186241373201560193956957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3973149294966617471081749 186241373201560193956957)
                  ·
                    rfl

theorem cell22_1632167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 6].length) (baseStart_1632167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632167 prefixEnd_1632167 := by exact prefixLift 1632167
  have htrace : WordTrace (prefixWord ++ tailWord_1632167) baseStart_1632167 baseEnd_1632167 := by
    simpa [prefixWord, tailWord_1632167, baseEnd_1632167] using wordTrace_append hprefix tailTrace_1632167
  have hstable : (prefixWord ++ tailWord_1632167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632167).length < 2 ^ (prefixWord ++ tailWord_1632167).sum := by decide
  have hdescent : baseEnd_1632167 < baseStart_1632167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632212 : List Nat := [2, 4, 1, 2, 1, 1, 4, 7]
def baseStart_1632212 : Nat := 118140960795 + 1632212 * 2 ^ 59
def prefixEnd_1632212 : Nat := 4983230072969 + 3 ^ 40 * 1632212 * 2
def baseEnd_1632212 : Nat := 62082169336035051610637

theorem tailTrace_1632212 : CollatzResearch.WordTrace tailWord_1632212 prefixEnd_1632212 62082169336035051610637 := by
  unfold tailWord_1632212
  simp only [CollatzResearch.WordTrace]
  refine ⟨29765831181391079230761445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39687774908521438974348593 29765831181391079230761445)
  ·
    refine ⟨5581093346510827355767771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29765831181391079230761445 5581093346510827355767771)
    ·
      refine ⟨8371640019766241033651657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5581093346510827355767771 8371640019766241033651657)
      ·
        refine ⟨6278730014824680775238743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8371640019766241033651657 6278730014824680775238743)
        ·
          refine ⟨9418095022237021162858115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6278730014824680775238743 9418095022237021162858115)
          ·
            refine ⟨14127142533355531744287173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9418095022237021162858115 14127142533355531744287173)
            ·
              refine ⟨2648839225004162202053845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14127142533355531744287173 2648839225004162202053845)
              ·
                refine ⟨62082169336035051610637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2648839225004162202053845 62082169336035051610637)
                ·
                  rfl

theorem cell22_1632212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 7].length) (baseStart_1632212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632212 prefixEnd_1632212 := by exact prefixLift 1632212
  have htrace : WordTrace (prefixWord ++ tailWord_1632212) baseStart_1632212 baseEnd_1632212 := by
    simpa [prefixWord, tailWord_1632212, baseEnd_1632212] using wordTrace_append hprefix tailTrace_1632212
  have hstable : (prefixWord ++ tailWord_1632212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632212).length < 2 ^ (prefixWord ++ tailWord_1632212).sum := by decide
  have hdescent : baseEnd_1632212 < baseStart_1632212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632220 : List Nat := [2, 2, 6, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1632220 : Nat := 118140960795 + 1632220 * 2 ^ 59
def prefixEnd_1632220 : Nat := 4983230072969 + 3 ^ 40 * 1632220 * 2
def baseEnd_1632220 : Nat := 558742262587806110295709

theorem tailTrace_1632220 : CollatzResearch.WordTrace tailWord_1632220 prefixEnd_1632220 558742262587806110295709 := by
  unfold tailWord_1632220
  simp only [CollatzResearch.WordTrace]
  refine ⟨29765977073376587913907057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39687969431168783885209409 29765977073376587913907057)
  ·
    refine ⟨22324482805032440935430293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29765977073376587913907057 22324482805032440935430293)
    ·
      refine ⟨1046460131485895668848295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22324482805032440935430293 1046460131485895668848295)
      ·
        refine ⟨1569690197228843503272443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046460131485895668848295 1569690197228843503272443)
        ·
          refine ⟨2354535295843265254908665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569690197228843503272443 2354535295843265254908665)
          ·
            refine ⟨1765901471882448941181499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2354535295843265254908665 1765901471882448941181499)
            ·
              refine ⟨2648852207823673411772249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765901471882448941181499 2648852207823673411772249)
              ·
                refine ⟨1986639155867755058829187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2648852207823673411772249 1986639155867755058829187)
                ·
                  refine ⟨2979958733801632588243781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986639155867755058829187 2979958733801632588243781)
                  ·
                    refine ⟨558742262587806110295709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2979958733801632588243781 558742262587806110295709)
                    ·
                      rfl

theorem cell22_1632220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1632220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632220 prefixEnd_1632220 := by exact prefixLift 1632220
  have htrace : WordTrace (prefixWord ++ tailWord_1632220) baseStart_1632220 baseEnd_1632220 := by
    simpa [prefixWord, tailWord_1632220, baseEnd_1632220] using wordTrace_append hprefix tailTrace_1632220
  have hstable : (prefixWord ++ tailWord_1632220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632220).length < 2 ^ (prefixWord ++ tailWord_1632220).sum := by decide
  have hdescent : baseEnd_1632220 < baseStart_1632220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632240 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 9]
def baseStart_1632240 : Nat := 118140960795 + 1632240 * 2 ^ 59
def prefixEnd_1632240 : Nat := 4983230072969 + 3 ^ 40 * 1632240 * 2
def baseEnd_1632240 : Nat := 186249702998844241598549

theorem tailTrace_1632240 : CollatzResearch.WordTrace tailWord_1632240 prefixEnd_1632240 186249702998844241598549 := by
  unfold tailWord_1632240
  simp only [CollatzResearch.WordTrace]
  refine ⟨29766341803340359621771087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39688455737787146162361449 29766341803340359621771087)
  ·
    refine ⟨44649512705010539432656631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29766341803340359621771087 44649512705010539432656631)
    ·
      refine ⟨66974269057515809148984947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44649512705010539432656631 66974269057515809148984947)
      ·
        refine ⟨100461403586273713723477421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66974269057515809148984947 100461403586273713723477421)
        ·
          refine ⟨37673026344852642646304033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100461403586273713723477421 37673026344852642646304033)
          ·
            refine ⟨28254769758639481984728025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37673026344852642646304033 28254769758639481984728025)
            ·
              refine ⟨21191077318979611488546019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28254769758639481984728025 21191077318979611488546019)
              ·
                refine ⟨31786615978469417232819029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21191077318979611488546019 31786615978469417232819029)
                ·
                  refine ⟨186249702998844241598549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31786615978469417232819029 186249702998844241598549)
                  ·
                    rfl

theorem cell22_1632240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_1632240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632240 prefixEnd_1632240 := by exact prefixLift 1632240
  have htrace : WordTrace (prefixWord ++ tailWord_1632240) baseStart_1632240 baseEnd_1632240 := by
    simpa [prefixWord, tailWord_1632240, baseEnd_1632240] using wordTrace_append hprefix tailTrace_1632240
  have hstable : (prefixWord ++ tailWord_1632240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632240).length < 2 ^ (prefixWord ++ tailWord_1632240).sum := by decide
  have hdescent : baseEnd_1632240 < baseStart_1632240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632255 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 3, 7]
def baseStart_1632255 : Nat := 118140960795 + 1632255 * 2 ^ 59
def prefixEnd_1632255 : Nat := 4983230072969 + 3 ^ 40 * 1632255 * 2
def baseEnd_1632255 : Nat := 558754243803077685670601

theorem tailTrace_1632255 : CollatzResearch.WordTrace tailWord_1632255 prefixEnd_1632255 558754243803077685670601 := by
  unfold tailWord_1632255
  simp only [CollatzResearch.WordTrace]
  refine ⟨59533230701626376805338219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39688820467750917870225479 59533230701626376805338219)
  ·
    refine ⟨89299846052439565208007329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59533230701626376805338219 89299846052439565208007329)
    ·
      refine ⟨66974884539329673906005497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89299846052439565208007329 66974884539329673906005497)
      ·
        refine ⟨50231163404497255429504123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66974884539329673906005497 50231163404497255429504123)
        ·
          refine ⟨75346745106745883144256185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50231163404497255429504123 75346745106745883144256185)
          ·
            refine ⟨56510058830059412358192139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75346745106745883144256185 56510058830059412358192139)
            ·
              refine ⟨84765088245089118537288209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56510058830059412358192139 84765088245089118537288209)
              ·
                refine ⟨63573816183816838902966157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84765088245089118537288209 63573816183816838902966157)
                ·
                  refine ⟨23840181068931314588612309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63573816183816838902966157 23840181068931314588612309)
                  ·
                    refine ⟨558754243803077685670601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23840181068931314588612309 558754243803077685670601)
                    ·
                      rfl

theorem cell22_1632255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_1632255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632255 prefixEnd_1632255 := by exact prefixLift 1632255
  have htrace : WordTrace (prefixWord ++ tailWord_1632255) baseStart_1632255 baseEnd_1632255 := by
    simpa [prefixWord, tailWord_1632255, baseEnd_1632255] using wordTrace_append hprefix tailTrace_1632255
  have hstable : (prefixWord ++ tailWord_1632255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632255).length < 2 ^ (prefixWord ++ tailWord_1632255).sum := by decide
  have hdescent : baseEnd_1632255 < baseStart_1632255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632261 : List Nat := [1, 3, 1, 1, 2, 5, 1, 4, 1, 3]
def baseStart_1632261 : Nat := 118140960795 + 1632261 * 2 ^ 59
def prefixEnd_1632261 : Nat := 4983230072969 + 3 ^ 40 * 1632261 * 2
def baseEnd_1632261 : Nat := 558756297725695670020583

theorem tailTrace_1632261 : CollatzResearch.WordTrace tailWord_1632261 prefixEnd_1632261 558756297725695670020583 := by
  unfold tailWord_1632261
  simp only [CollatzResearch.WordTrace]
  refine ⟨59533449539604639830056637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39688966359736426553371091 59533449539604639830056637)
  ·
    refine ⟨22325043577351739936271239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59533449539604639830056637 22325043577351739936271239)
    ·
      refine ⟨33487565366027609904406859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22325043577351739936271239 33487565366027609904406859)
      ·
        refine ⟨50231348049041414856610289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33487565366027609904406859 50231348049041414856610289)
        ·
          refine ⟨37673511036781061142457717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50231348049041414856610289 37673511036781061142457717)
          ·
            refine ⟨3531891659698224482105411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37673511036781061142457717 3531891659698224482105411)
            ·
              refine ⟨5297837489547336723158117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531891659698224482105411 5297837489547336723158117)
              ·
                refine ⟨993344529290125635592147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5297837489547336723158117 993344529290125635592147)
                ·
                  refine ⟨1490016793935188453388221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993344529290125635592147 1490016793935188453388221)
                  ·
                    refine ⟨558756297725695670020583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1490016793935188453388221 558756297725695670020583)
                    ·
                      rfl

theorem cell22_1632261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_1632261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632261 prefixEnd_1632261 := by exact prefixLift 1632261
  have htrace : WordTrace (prefixWord ++ tailWord_1632261) baseStart_1632261 baseEnd_1632261 := by
    simpa [prefixWord, tailWord_1632261, baseEnd_1632261] using wordTrace_append hprefix tailTrace_1632261
  have hstable : (prefixWord ++ tailWord_1632261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632261).length < 2 ^ (prefixWord ++ tailWord_1632261).sum := by decide
  have hdescent : baseEnd_1632261 < baseStart_1632261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632287 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 3, 4]
def baseStart_1632287 : Nat := 118140960795 + 1632287 * 2 ^ 59
def prefixEnd_1632287 : Nat := 4983230072969 + 3 ^ 40 * 1632287 * 2
def baseEnd_1632287 : Nat := 558765198057040268870503

theorem tailTrace_1632287 : CollatzResearch.WordTrace tailWord_1632287 prefixEnd_1632287 558765198057040268870503 := by
  unfold tailWord_1632287
  simp only [CollatzResearch.WordTrace]
  refine ⟨59534397837510446270503115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39689598558340297513668743 59534397837510446270503115)
  ·
    refine ⟨89301596756265669405754673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59534397837510446270503115 89301596756265669405754673)
    ·
      refine ⟨66976197567199252054316005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89301596756265669405754673 66976197567199252054316005)
      ·
        refine ⟨12558037043849859760184251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66976197567199252054316005 12558037043849859760184251)
        ·
          refine ⟨18837055565774789640276377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12558037043849859760184251 18837055565774789640276377)
          ·
            refine ⟨14127791674331092230207283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18837055565774789640276377 14127791674331092230207283)
            ·
              refine ⟨21191687511496638345310925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14127791674331092230207283 21191687511496638345310925)
              ·
                refine ⟨7946882816811239379491597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21191687511496638345310925 7946882816811239379491597)
                ·
                  refine ⟨2980081056304214767309349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7946882816811239379491597 2980081056304214767309349)
                  ·
                    refine ⟨558765198057040268870503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2980081056304214767309349 558765198057040268870503)
                    ·
                      rfl

theorem cell22_1632287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_1632287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632287 prefixEnd_1632287 := by exact prefixLift 1632287
  have htrace : WordTrace (prefixWord ++ tailWord_1632287) baseStart_1632287 baseEnd_1632287 := by
    simpa [prefixWord, tailWord_1632287, baseEnd_1632287] using wordTrace_append hprefix tailTrace_1632287
  have hstable : (prefixWord ++ tailWord_1632287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632287).length < 2 ^ (prefixWord ++ tailWord_1632287).sum := by decide
  have hdescent : baseEnd_1632287 < baseStart_1632287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632295 : List Nat := [1, 1, 7, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1632295 : Nat := 118140960795 + 1632295 * 2 ^ 59
def prefixEnd_1632295 : Nat := 4983230072969 + 3 ^ 40 * 1632295 * 2
def baseEnd_1632295 : Nat := 558767936620530914670479

theorem tailTrace_1632295 : CollatzResearch.WordTrace tailWord_1632295 prefixEnd_1632295 558767936620530914670479 := by
  unfold tailWord_1632295
  simp only [CollatzResearch.WordTrace]
  refine ⟨59534689621481463636794339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39689793080987642424529559 59534689621481463636794339)
  ·
    refine ⟨89302034432222195455191509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59534689621481463636794339 89302034432222195455191509)
    ·
      refine ⟨2093016432005207705981051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 89302034432222195455191509 2093016432005207705981051)
      ·
        refine ⟨3139524648007811558971577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093016432005207705981051 3139524648007811558971577)
        ·
          refine ⟨2354643486005858669228683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3139524648007811558971577 2354643486005858669228683)
          ·
            refine ⟨3531965229008788003843025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354643486005858669228683 3531965229008788003843025)
            ·
              refine ⟨2648973921756591002882269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3531965229008788003843025 2648973921756591002882269)
              ·
                refine ⟨993365220658721626080851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2648973921756591002882269 993365220658721626080851)
                ·
                  refine ⟨1490047830988082439121277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993365220658721626080851 1490047830988082439121277)
                  ·
                    refine ⟨558767936620530914670479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1490047830988082439121277 558767936620530914670479)
                    ·
                      rfl

theorem cell22_1632295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1632295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632295 prefixEnd_1632295 := by exact prefixLift 1632295
  have htrace : WordTrace (prefixWord ++ tailWord_1632295) baseStart_1632295 baseEnd_1632295 := by
    simpa [prefixWord, tailWord_1632295, baseEnd_1632295] using wordTrace_append hprefix tailTrace_1632295
  have hstable : (prefixWord ++ tailWord_1632295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632295).length < 2 ^ (prefixWord ++ tailWord_1632295).sum := by decide
  have hdescent : baseEnd_1632295 < baseStart_1632295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632304 : List Nat := [2, 1, 1, 1, 2, 6, 1, 3, 1, 4]
def baseStart_1632304 : Nat := 118140960795 + 1632304 * 2 ^ 59
def prefixEnd_1632304 : Nat := 4983230072969 + 3 ^ 40 * 1632304 * 2
def baseEnd_1632304 : Nat := 558771017504457891195451

theorem tailTrace_1632304 : CollatzResearch.WordTrace tailWord_1632304 prefixEnd_1632304 558771017504457891195451 := by
  unfold tailWord_1632304
  simp only [CollatzResearch.WordTrace]
  refine ⟨29767508939224429086935983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39690011918965905449247977 29767508939224429086935983)
  ·
    refine ⟨44651263408836643630403975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29767508939224429086935983 44651263408836643630403975)
    ·
      refine ⟨66976895113254965445605963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44651263408836643630403975 66976895113254965445605963)
      ·
        refine ⟨100465342669882448168408945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66976895113254965445605963 100465342669882448168408945)
        ·
          refine ⟨75349007002411836126306709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100465342669882448168408945 75349007002411836126306709)
          ·
            refine ⟨3531984703238054818420627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75349007002411836126306709 3531984703238054818420627)
            ·
              refine ⟨5297977054857082227630941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531984703238054818420627 5297977054857082227630941)
              ·
                refine ⟨1986741395571405835361603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5297977054857082227630941 1986741395571405835361603)
                ·
                  refine ⟨2980112093357108753042405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986741395571405835361603 2980112093357108753042405)
                  ·
                    refine ⟨558771017504457891195451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2980112093357108753042405 558771017504457891195451)
                    ·
                      rfl

theorem cell22_1632304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_1632304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632304 prefixEnd_1632304 := by exact prefixLift 1632304
  have htrace : WordTrace (prefixWord ++ tailWord_1632304) baseStart_1632304 baseEnd_1632304 := by
    simpa [prefixWord, tailWord_1632304, baseEnd_1632304] using wordTrace_append hprefix tailTrace_1632304
  have hstable : (prefixWord ++ tailWord_1632304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632304).length < 2 ^ (prefixWord ++ tailWord_1632304).sum := by decide
  have hdescent : baseEnd_1632304 < baseStart_1632304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632308 : List Nat := [2, 5, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1632308 : Nat := 118140960795 + 1632308 * 2 ^ 59
def prefixEnd_1632308 : Nat := 4983230072969 + 3 ^ 40 * 1632308 * 2
def baseEnd_1632308 : Nat := 186257462262067738031813

theorem tailTrace_1632308 : CollatzResearch.WordTrace tailWord_1632308 prefixEnd_1632308 186257462262067738031813 := by
  unfold tailWord_1632308
  simp only [CollatzResearch.WordTrace]
  refine ⟨29767581885217183428508789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39690109180289577904678385 29767581885217183428508789)
  ·
    refine ⟨2790710801739110946422699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29767581885217183428508789 2790710801739110946422699)
    ·
      refine ⟨4186066202608666419634049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2790710801739110946422699 4186066202608666419634049)
      ·
        refine ⟨3139549651956499814725537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4186066202608666419634049 3139549651956499814725537)
        ·
          refine ⟨2354662238967374861044153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3139549651956499814725537 2354662238967374861044153)
          ·
            refine ⟨1765996679225531145783115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2354662238967374861044153 1765996679225531145783115)
            ·
              refine ⟨2648995018838296718674673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765996679225531145783115 2648995018838296718674673)
              ·
                refine ⟨1986746264128722539006005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2648995018838296718674673 1986746264128722539006005)
                ·
                  refine ⟨186257462262067738031813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1986746264128722539006005 186257462262067738031813)
                  ·
                    rfl

theorem cell22_1632308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1632308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632308 prefixEnd_1632308 := by exact prefixLift 1632308
  have htrace : WordTrace (prefixWord ++ tailWord_1632308) baseStart_1632308 baseEnd_1632308 := by
    simpa [prefixWord, tailWord_1632308, baseEnd_1632308] using wordTrace_append hprefix tailTrace_1632308
  have hstable : (prefixWord ++ tailWord_1632308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632308).length < 2 ^ (prefixWord ++ tailWord_1632308).sum := by decide
  have hdescent : baseEnd_1632308 < baseStart_1632308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632319 : List Nat := [1, 1, 2, 2, 3, 1, 4, 4, 4]
def baseStart_1632319 : Nat := 118140960795 + 1632319 * 2 ^ 59
def prefixEnd_1632319 : Nat := 4983230072969 + 3 ^ 40 * 1632319 * 2
def baseEnd_1632319 : Nat := 186258717437000950690135

theorem tailTrace_1632319 : CollatzResearch.WordTrace tailWord_1632319 prefixEnd_1632319 186258717437000950690135 := by
  unfold tailWord_1632319
  simp only [CollatzResearch.WordTrace]
  refine ⟨59535564973394515735668011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39690376648929677157112007 59535564973394515735668011)
  ·
    refine ⟨89303347460091773603502017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59535564973394515735668011 89303347460091773603502017)
    ·
      refine ⟨66977510595068830202626513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89303347460091773603502017 66977510595068830202626513)
      ·
        refine ⟨50233132946301622651969885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66977510595068830202626513 50233132946301622651969885)
        ·
          refine ⟨18837424854863108494488707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50233132946301622651969885 18837424854863108494488707)
          ·
            refine ⟨28256137282294662741733061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18837424854863108494488707 28256137282294662741733061)
            ·
              refine ⟨5298025740430249264074949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28256137282294662741733061 5298025740430249264074949)
              ·
                refine ⟨993379826330671737014053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5298025740430249264074949 993379826330671737014053)
                ·
                  refine ⟨186258717437000950690135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 993379826330671737014053 186258717437000950690135)
                  ·
                    rfl

theorem cell22_1632319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 4].length) (baseStart_1632319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632319 prefixEnd_1632319 := by exact prefixLift 1632319
  have htrace : WordTrace (prefixWord ++ tailWord_1632319) baseStart_1632319 baseEnd_1632319 := by
    simpa [prefixWord, tailWord_1632319, baseEnd_1632319] using wordTrace_append hprefix tailTrace_1632319
  have hstable : (prefixWord ++ tailWord_1632319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632319).length < 2 ^ (prefixWord ++ tailWord_1632319).sum := by decide
  have hdescent : baseEnd_1632319 < baseStart_1632319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632332 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_1632332 : Nat := 118140960795 + 1632332 * 2 ^ 59
def prefixEnd_1632332 : Nat := 4983230072969 + 3 ^ 40 * 1632332 * 2
def baseEnd_1632332 : Nat := 558780602476675151495365

theorem tailTrace_1632332 : CollatzResearch.WordTrace tailWord_1632332 prefixEnd_1632332 558780602476675151495365 := by
  unfold tailWord_1632332
  simp only [CollatzResearch.WordTrace]
  refine ⟨29768019561173709477945625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39690692748231612637260833 29768019561173709477945625)
  ·
    refine ⟨22326014670880282108459219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29768019561173709477945625 22326014670880282108459219)
    ·
      refine ⟨33489022006320423162688829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22326014670880282108459219 33489022006320423162688829)
      ·
        refine ⟨12558383252370158686008311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33489022006320423162688829 12558383252370158686008311)
        ·
          refine ⟨18837574878555238029012467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12558383252370158686008311 18837574878555238029012467)
          ·
            refine ⟨28256362317832857043518701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18837574878555238029012467 28256362317832857043518701)
            ·
              refine ⟨10596135869187321391319513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28256362317832857043518701 10596135869187321391319513)
              ·
                refine ⟨7947101901890491043489635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10596135869187321391319513 7947101901890491043489635)
                ·
                  refine ⟨11920652852835736565234453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7947101901890491043489635 11920652852835736565234453)
                  ·
                    refine ⟨558780602476675151495365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11920652852835736565234453 558780602476675151495365)
                    ·
                      rfl

theorem cell22_1632332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_1632332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632332 prefixEnd_1632332 := by exact prefixLift 1632332
  have htrace : WordTrace (prefixWord ++ tailWord_1632332) baseStart_1632332 baseEnd_1632332 := by
    simpa [prefixWord, tailWord_1632332, baseEnd_1632332] using wordTrace_append hprefix tailTrace_1632332
  have hstable : (prefixWord ++ tailWord_1632332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632332).length < 2 ^ (prefixWord ++ tailWord_1632332).sum := by decide
  have hdescent : baseEnd_1632332 < baseStart_1632332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632334 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_1632334 : Nat := 118140960795 + 1632334 * 2 ^ 59
def prefixEnd_1632334 : Nat := 4983230072969 + 3 ^ 40 * 1632334 * 2
def baseEnd_1632334 : Nat := 558781287117547812945359

theorem tailTrace_1632334 : CollatzResearch.WordTrace tailWord_1632334 prefixEnd_1632334 558781287117547812945359 := by
  unfold tailWord_1632334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7442014008542521662183007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39690741378893448864976037 7442014008542521662183007)
  ·
    refine ⟨11163021012813782493274511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7442014008542521662183007 11163021012813782493274511)
    ·
      refine ⟨16744531519220673739911767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11163021012813782493274511 16744531519220673739911767)
      ·
        refine ⟨25116797278831010609867651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16744531519220673739911767 25116797278831010609867651)
        ·
          refine ⟨37675195918246515914801477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25116797278831010609867651 37675195918246515914801477)
          ·
            refine ⟨7064099234671221734025277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37675195918246515914801477 7064099234671221734025277)
            ·
              refine ⟨2649037213001708150259479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7064099234671221734025277 2649037213001708150259479)
              ·
                refine ⟨3973555819502562225389219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649037213001708150259479 3973555819502562225389219)
                ·
                  refine ⟨5960333729253843338083829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3973555819502562225389219 5960333729253843338083829)
                  ·
                    refine ⟨558781287117547812945359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5960333729253843338083829 558781287117547812945359)
                    ·
                      rfl

theorem cell22_1632334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_1632334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632334 prefixEnd_1632334 := by exact prefixLift 1632334
  have htrace : WordTrace (prefixWord ++ tailWord_1632334) baseStart_1632334 baseEnd_1632334 := by
    simpa [prefixWord, tailWord_1632334, baseEnd_1632334] using wordTrace_append hprefix tailTrace_1632334
  have hstable : (prefixWord ++ tailWord_1632334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632334).length < 2 ^ (prefixWord ++ tailWord_1632334).sum := by decide
  have hdescent : baseEnd_1632334 < baseStart_1632334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632385 : List Nat := [1, 2, 4, 2, 3, 2, 2, 1, 2, 3]
def baseStart_1632385 : Nat := 118140960795 + 1632385 * 2 ^ 59
def prefixEnd_1632385 : Nat := 4983230072969 + 3 ^ 40 * 1632385 * 2
def baseEnd_1632385 : Nat := 558798745459800679920203

theorem tailTrace_1632385 : CollatzResearch.WordTrace tailWord_1632385 prefixEnd_1632385 558798745459800679920203 := by
  unfold tailWord_1632385
  simp only [CollatzResearch.WordTrace]
  refine ⟨59537972191155409007570609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39691981460770272671713739 59537972191155409007570609)
  ·
    refine ⟨44653479143366556755677957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59537972191155409007570609 44653479143366556755677957)
    ·
      refine ⟨8372527339381229391689617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44653479143366556755677957 8372527339381229391689617)
      ·
        refine ⟨6279395504535922043767213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8372527339381229391689617 6279395504535922043767213)
        ·
          refine ⟨2354773314200970766412705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6279395504535922043767213 2354773314200970766412705)
          ·
            refine ⟨1766079985650728074809529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2354773314200970766412705 1766079985650728074809529)
            ·
              refine ⟨1324559989238046056107147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1766079985650728074809529 1324559989238046056107147)
              ·
                refine ⟨1986839983857069084160721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324559989238046056107147 1986839983857069084160721)
                ·
                  refine ⟨1490129987892801813120541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1986839983857069084160721 1490129987892801813120541)
                  ·
                    refine ⟨558798745459800679920203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1490129987892801813120541 558798745459800679920203)
                    ·
                      rfl

theorem cell22_1632385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_1632385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632385 prefixEnd_1632385 := by exact prefixLift 1632385
  have htrace : WordTrace (prefixWord ++ tailWord_1632385) baseStart_1632385 baseEnd_1632385 := by
    simpa [prefixWord, tailWord_1632385, baseEnd_1632385] using wordTrace_append hprefix tailTrace_1632385
  have hstable : (prefixWord ++ tailWord_1632385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632385).length < 2 ^ (prefixWord ++ tailWord_1632385).sum := by decide
  have hdescent : baseEnd_1632385 < baseStart_1632385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632439 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 3, 4]
def baseStart_1632439 : Nat := 118140960795 + 1632439 * 2 ^ 59
def prefixEnd_1632439 : Nat := 4983230072969 + 3 ^ 40 * 1632439 * 2
def baseEnd_1632439 : Nat := 558817230763362539070037

theorem tailTrace_1632439 : CollatzResearch.WordTrace tailWord_1632439 prefixEnd_1632439 558817230763362539070037 := by
  unfold tailWord_1632439
  simp only [CollatzResearch.WordTrace]
  refine ⟨59539941732959776230036371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39693294488639850820024247 59539941732959776230036371)
  ·
    refine ⟨89309912599439664345054557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59539941732959776230036371 89309912599439664345054557)
    ·
      refine ⟨33491217224789874129395459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89309912599439664345054557 33491217224789874129395459)
      ·
        refine ⟨50236825837184811194093189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33491217224789874129395459 50236825837184811194093189)
        ·
          refine ⟨9419404844472152098892473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50236825837184811194093189 9419404844472152098892473)
          ·
            refine ⟨7064553633354114074169355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9419404844472152098892473 7064553633354114074169355)
            ·
              refine ⟨10596830450031171111254033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7064553633354114074169355 10596830450031171111254033)
              ·
                refine ⟨7947622837523378333440525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10596830450031171111254033 7947622837523378333440525)
                ·
                  refine ⟨2980358564071266875040197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7947622837523378333440525 2980358564071266875040197)
                  ·
                    refine ⟨558817230763362539070037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2980358564071266875040197 558817230763362539070037)
                    ·
                      rfl

theorem cell22_1632439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_1632439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1632439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1632439 prefixEnd_1632439 := by exact prefixLift 1632439
  have htrace : WordTrace (prefixWord ++ tailWord_1632439) baseStart_1632439 baseEnd_1632439 := by
    simpa [prefixWord, tailWord_1632439, baseEnd_1632439] using wordTrace_append hprefix tailTrace_1632439
  have hstable : (prefixWord ++ tailWord_1632439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632439).length < 2 ^ (prefixWord ++ tailWord_1632439).sum := by decide
  have hdescent : baseEnd_1632439 < baseStart_1632439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
